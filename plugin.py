"""麦麦电话闹钟（local.wake-call）—— 到点给她打一通电话。

链路：定时 → 按任务提示词生成一句话 → TTS 合成 → ffmpeg 转 8k/mono → baresip 拨 SIP → 手机原生来电。

可以配多个任务：每个任务有自己的时间、自己的提示词，不一定非得叫起床。
为什么不用 QQ / 不用安卓系统接口：
    MaiBot 跑在 proot 里，够不到 /system、binder、am，也调不动拨号和短信；
    所以唯一能真正"响铃"的路径是网络侧发起一通 SIP 呼叫。
"""

from __future__ import annotations

import asyncio
import contextlib
import json
import os
import random
import re
import shutil
import subprocess
import sys
import tempfile
import time
import uuid
from datetime import datetime, timedelta
from pathlib import Path
from typing import Any, Dict, Optional

from maibot_sdk import API, Field, MaiBotPlugin, PluginConfigBase

PLUGIN_VERSION = "1.0.0"
MAX_ATTEMPTS = 3

# 报「找不到 ffmpeg」等于让用户再去搜一次怎么装，所以直接把命令写进异常里。
MISSING_FFMPEG = (
    "找不到 ffmpeg —— 语音要先转成 8k 单声道 WAV 才能播，这一步只能靠它。"
    "安装：Debian/Ubuntu/proot 用 apt install -y ffmpeg；"
    "macOS 用 brew install ffmpeg；"
    "Windows 去 gyan.dev 下 essentials 版，解压后把 bin 目录加进 PATH，"
    "重开终端跑 ffmpeg -version 确认有输出"
)


def _as_port(value: str) -> int:
    """把端口字符串转成 int，不合法一律当 0（= 没写端口），绝不抛异常。"""
    try:
        port = int(str(value).strip())
    except (TypeError, ValueError):
        return 0
    return port if 0 < port < 65536 else 0



# 任务数量上限：一天打几十通电话既没意义，也会把侧边栏撑爆。
MAX_JOBS = 10
RETRY_DELAY_SECONDS = 30
# 内网探测结果的缓存：扫一遍 /24 要 1~2 秒，没必要每通电话都重扫。
# 10 分钟内复用上次结果，换网络（换 WiFi）时最多晚 10 分钟才失效。
LAN_CACHE_TTL = 600
# 端口段扫描失败后的冷却时间：扫一次要给对端发 2 万多个 OPTIONS，
# 不能每通电话都来一遍，失败就等 10 分钟再说。
LAN_SCAN_COOLDOWN = 600
# 扫一遍临时端口段的时间上限。实测 800pps 下命中约 11 秒、扫完约 16 秒，
# 留点余量；超了就放弃改走公网，绝不把电话卡死在这儿。
LAN_SCAN_BUDGET = 18.0
# 内网对端缓存按「网段」分开记：换回旧网络时还能直接复用上次那台主机。
# 记的是 host:port —— IP 在同一张网络里很稳，端口每次 App 启动都会变，
# 所以「端口变了就在同一台上重扫」比重找主机便宜得多（14 秒 vs 好几分钟）。
LAN_PEER_CACHE_MAX = 8
# 缓存验证只发 1 个 OPTIONS，很便宜，所以查得勤：60 秒一次，
# 对方 App 重启换了端口，最多 1 分钟就自愈，不会踩空早上的闹钟。
LAN_PREWARM_INTERVAL = 60
# 同一台主机重扫端口段的冷却：扫一次要发近 3 万个包、约 14 秒，失败别每分钟重来。
LAN_REHEAL_COOLDOWN = 180
# 完全没有线索时（刚进新网络、网关又不是对方）的兜底：ping 扫出活跃主机后，
# 最多逐台试几台。每台 14 秒，所以必须限量，不能把整张网都翻一遍。
LAN_SWEEP_LIMIT = 4
# 活跃主机超过这个数就认定是「公共网络」（校园网实测本 /24 有 140~170 台），
# 这时绝不逐台扫端口：既扫不到人（接听端往往在别的 /24），又是往陌生人设备上灌包。
# 公共网络里只走「记住那台主机」这条路，找不到就提示手填 IP。
LAN_SWEEP_MAX_HOSTS = 8
# 「IP 变了、端口没变」的补救：拿旧端口扫本机整段地址。
# Linphone 的端口只在 App 重启时变，重连 WiFi / 换 DHCP 地址时端口是保留的，
# 所以拿旧端口当「名字」去整段找人，比重新扫端口段便宜两个数量级：
# 实测 /20（4094 个地址）单 socket 收发约 2~3 秒，而端口段单机要十几秒还找不到人。
# 代价是往同网段的陌生设备各发一条 SIP OPTIONS（不建会话、不响铃），
# 默认前缀 /20，用户可在侧边栏改成 /24（更收敛）或 /16（更宽）。
LAN_SUBNET_MAX_HOSTS = 8192
LAN_SUBNET_COOLDOWN = 300.0
# 拨号现场用的冷却，比预热循环的短得多：只躲开「刚刚才扫过」的那一次。
# 为什么不能复用预热的冷却：那是为「别一直空扫」设计的，会一路退避到 60 分钟。
# 但拨号是关键时刻，扫一次约 7 秒换来内网直呼，比走公网登录 + 中继收敛的 80 秒划算太多。
# 实测教训：23:08 扫失败后，23:10 和 23:12 两通都被 300 秒冷却挡在门外，直接走了公网。
DIAL_SUBNET_COOLDOWN = 60.0
# 公共网络（校园网 / 酒店 / 公司）里 L2.5 的退避表：连续未命中就逐级拉长，命中即清零。
# 为什么只在公共网络里退避：校园网实测「对端一整晚都不在这张网里」是常态，
# 而每 5 分钟往 4094 个地址各发一个包，一天上限约 118 万个 —— 既扰民又容易被网络中心盯上。
# 家里 WiFi / 热点则保持 5 分钟固定节奏，那是对端随时会回来的环境，查得勤才是对的。
LAN_SUBNET_BACKOFF = (300.0, 900.0, 1800.0, 3600.0)
# 离任一任务触发不足这么多分钟时，把退避压回最小值：宁可多扫一次，也不能踩空闹钟。
LAN_PREWAKE_MINUTES = 10.0
# 历史命中过的 /24 最多优先扫几个。缓存本身只留 8 张网络（LAN_PEER_CACHE_MAX），
# 一个 /24 才 253 个包，全扫也就 2000 来个，比本机 /20 的 4094 个还少。
LAN_HISTORY_SUBNET_MAX = 8
# 整段发完之后再等多久收应答。单台超时按 0.8 秒设计，这里给够一倍余量。
LAN_SCAN_COLLECT = 1.6
# 「这张网是不是公共网络」的缓存：判定一次要扫一遍本 /24，不能每轮都做。
_PUBLIC_NET_CACHE: Dict[str, Any] = {"ip": "", "public": False, "count": 0, "ts": 0.0}
PUBLIC_NET_TTL = 600.0
_LOCAL_NET_CACHE: Dict[str, Any] = {"ip": "", "prefix": 24, "ts": 0.0}
# 本机 WLAN 地址的缓存：_note_lan_peer 是每个 UDP 包都会走的热路径，
# 而挑接口要起一个 `ip addr` 子进程，每次都调会把事件循环拖垮。
_LOCAL_IP_CACHE: Dict[str, Any] = {"ip": "", "ts": 0.0}
# 本机掩码缓存 10 秒：_note_lan_peer 是每个 UDP 包都会走的热路径，
# 每次都起一个 `ip` 子进程会把事件循环拖垮。
LOCAL_NET_TTL = 10.0
_LAN_CACHE: Dict[str, Any] = {"ts": 0.0, "entries": None}
# 注册最长等待：实测校园网到 sip.linphone.org 的 TLS 注册偶尔要 40 秒。
REG_WAIT = 45
# 接通后保持通话的秒数：台词时长 + 余量，够说完就不再拖。
PLAY_SECONDS = 60
# 每次拨号的 baresip 报文会落盘，只保留最近这么多份。
DIAL_LOG_KEEP = 30
# 人设注入上限：几个字的台词用不着几万字人设，塞太多既涨钱又会让模型跑题。
PERSONA_INJECT_LIMIT = 4000
STATE_FILENAME = "state.json"

DEFAULT_INTENT = (
    "现在是早上 {hour}:{minute}，你刚被闹钟弄醒，要去叫主人起床。"
    "说一两句叫他起来的话：可以懒洋洋地催、可以嘴硬一下再软，也可以抱怨他怎么还不起。"
    "语气像刚睡醒在耳边说话，别用客服腔，别说教。"
    "只输出这句话本身，不要解释、不要加引号、不要问他有什么需要帮忙的。"
)

# 模型偶尔会带「麦麦：」这类前缀，去掉。
_PREFIX_RE = re.compile(r"^\s*(?:她|麦麦|助手|AI|Bot)\s*[:：]\s*", re.IGNORECASE)

# ─── 台词守门 ───
# 中转站抽风时最典型的表现：吐一大段英文的限流说明，或者「作为 AI 我无法…」。
# 这段话一旦原样送进 TTS 就是按字白烧钱（豆包按字数计费），所以合成前先过一道闸。
# 这里只收「正常台词里几乎不会出现、只有报错或拒答才会出现」的词，
# 命中即判废，改说本地备用台词（不花钱、也不会把报错念给她听）。
# 故意不做「中文占比」判断：用户可能就想要英文/日文台词，按语种猜会误杀正常内容。
DEFAULT_BAN_WORDS = (
    # 中转站 / 官方 API 的限流、额度、鉴权话术
    "rate limit", "rate-limit", "too many requests", "quota", "insufficient",
    "exceed", "unauthorized", "forbidden", "invalid api key", "api key",
    "service unavailable", "overloaded", "over capacity", "try again later",
    "please try again", "upgrade your plan", "content policy", "content filter",
    "moderation", "billing problem", "payment required",
    # 模型自述式拒答（用较长短语，避免误伤正常英文台词里的 sorry / can't）
    # 注意：不要收裸的 "i can't"——"I can't wait to see you" / "I can't believe
    # you're still asleep" 都是正常台词，会被误杀成「模型出错」。
    "as an ai", "language model", "i cannot assist", "i cannot provide",
    "i cannot comply", "i am unable", "i'm unable",
    "i'm sorry, but i", "sorry, but i cannot", "cannot assist", "cannot help",
    "can't help with", "unable to help",
    # 中文侧：同样是「只在异常时出现」的词
    "限流", "额度", "余额不足", "请求失败", "请求超时", "服务繁忙", "服务器繁忙",
    "系统繁忙", "鉴权失败", "认证失败", "无权访问", "欠费", "错误码", "已达上限",
    "触发上限", "内容审核", "接口异常", "签名错误", "参数错误", "请稍后再试",
)

# 判废时改说这些。故意写得像她本人会说的话：就算模型挂了，接起来也是正常的一通电话。
DEFAULT_FALLBACK_LINES = (
    "喂——起床啦，太阳都晒屁股了。",
    "别赖了，再睡下去今天就没了。",
    "快起来，我数三个数哦。",
    "醒醒，天亮很久了。",
    "起床，听见没，我叫你起床。",
    "再睡五分钟，就五分钟，然后必须起。",
    "喂，早饭都凉了，你还躺着呢。",
    "睁眼，先睁眼，然后坐起来。",
    "该起了，别让我一直催你。",
    "喂，我在这儿等你起来呢。",
)

# SIP 响应行形如 `<- SIP/2.0 180 Ringing`。只认这种形态，
# 不能拿裸的 "100" / "180" 去 in log —— IP（10.0.0.100）、端口、时间戳全会误命中，
# 结果把「注册都没成功」误报成「服务器已转接但手机没应答」。
_SIP_CODE_RE = re.compile(r"SIP/2\.0\s+(\d{3})")


class _LanProbeProtocol(asyncio.DatagramProtocol):
    """把 5060 上收到的任何包丢给插件，用来学习对端真实端口。

    故意不看内容：Linphone 的保活是空 CRLF、拨号才是 INVITE，形态不固定，
    我们只关心「谁、从哪个端口发来的」。这个端口就是它当前能接电话的地址。
    """

    def __init__(self, plugin: Any) -> None:
        self._plugin = plugin

    def datagram_received(self, data: bytes, addr: tuple[str, int]) -> None:
        with contextlib.suppress(Exception):
            self._plugin._note_lan_peer(addr, data)


def _sip_code_list(log: str) -> list[str]:
    """按出现顺序取 SIP 状态码，判定要看顺序而不只是有没有出现过。"""
    return [m.group(1) for m in _SIP_CODE_RE.finditer(log or "")]


def _sip_invite_final(trace: str) -> str:
    """取「这条 INVITE 事务」的最终响应码。

    为什么不能只看最后一个 2xx：同一段报文里还有 REGISTER / OPTIONS / BYE 的事务，
    它们全都会回 200 OK。只按「有没有 2xx」判断，会把一件根本没接通的事判成成功，
    当天就不再重拨 —— 叫起床最不能接受的错就是这种。
    CSeq 里带着方法名，只有 `CSeq: N INVITE` 上面的那个状态码才属于这通呼叫。
    """
    code = ""
    last_invite = ""
    for line in (trace or "").splitlines():
        text = line.strip()
        if text.startswith("SIP/2.0 "):
            parts = text.split()
            code = parts[1] if len(parts) > 1 else ""
        elif text[:5].lower() == "cseq:" and "invite" in text.lower():
            last_invite = code
    return last_invite


def has_any(codes: list[str], *wanted: str) -> bool:
    return any(code in codes for code in wanted)


# 报文里能说明问题的行：状态码、媒体协商、编码协商、接通/注册标记。
_DIGEST_PREFIX = ("SIP/2.0", "m=audio", "a=rtpmap", "a=sendrecv", "a=sendonly", "a=recvonly", "c=IN IP4")
_DIGEST_CONTAINS = ("call established", "registered successfully", "aucodec")


def _dial_digest(log: str, limit: int = 8) -> str:
    """把一段 baresip 报文压成一行日志，够判断卡在哪一步就行。

    特意保留 `c=IN IP4` / `a=rtpmap`：媒体地址和编码就是「响了却没声音」的唯一现场证据。
    """
    picked: list[str] = []
    seen: set[str] = set()
    for raw in (log or "").splitlines():
        line = raw.strip()
        if not line:
            continue
        low = line.lower()
        if not (line.startswith(_DIGEST_PREFIX) or any(k in low for k in _DIGEST_CONTAINS)):
            continue
        key = line[:72]
        if key in seen:
            continue
        seen.add(key)
        picked.append(line[:110])
        if len(picked) >= limit:
            break
    return " ｜ ".join(picked)


class PluginSection(PluginConfigBase):
    __ui_label__ = "插件"

    # enabled 是宿主保留键（WebUI 顶部启停开关写同一个键），不能在模型里声明。
    config_version: str = Field(
        default=PLUGIN_VERSION,
        description="配置版本，请勿手动修改。",
        json_schema_extra={"disabled": True, "hidden": True, "label": "配置版本", "order": 99},
    )


class JobSection(PluginConfigBase):
    """一个定时任务：几点打、说什么、怎么调。

    可以有多个，比如 08:00 叫起床、13:20 喊吃午饭、23:30 催睡觉，
    每个任务的提示词各管各的，互不影响。
    """

    __ui_label__ = "定时任务"

    id: str = Field(
        default="",
        description="任务标识，创建时自动生成，用来记「这个任务今天拨过没有」。别手改。",
        json_schema_extra={"hidden": True, "disabled": True},
    )
    label: str = Field(default="叫起床", description="任务名，只在界面上用来区分。")
    enabled: bool = Field(default=True, description="这个任务到点是否打电话。")
    hour: int = Field(default=8, ge=0, le=23, description="小时，0-23，按运行环境本地时区。")
    minute: int = Field(default=0, ge=0, le=59, description="分钟，0-59。")
    catch_up_minutes: int = Field(
        default=30, ge=0, le=720, description="错过时间点后仍补打的宽限分钟数，0 表示只在当分钟内触发。"
    )
    max_chars: int = Field(default=60, ge=10, le=200, description="这个任务台词的最大字数，超长截断。")
    intent: str = Field(
        default=DEFAULT_INTENT,
        description="交给模型生成台词的提示词，支持 {hour}、{minute}、{label} 三个占位符。",
    )
    llm_task: str = Field(default="", description="留空则用 [wake].llm_task 的全局设定。")


class WakeSection(PluginConfigBase):
    __ui_label__ = "全局"

    enabled: bool = Field(default=True, description="总开关，关掉后所有任务都不拨号。")
    check_interval_seconds: int = Field(default=20, ge=5, le=300, description="轮询间隔（秒）。")
    max_chars: int = Field(default=60, ge=10, le=200, description="新建任务时的默认字数上限。")
    llm_task: str = Field(
        default="replyer",
        description=(
            "默认用哪个模型任务生成台词：replyer = 她平时聊天用的模型（最像本人，稍慢）；"
            "utils = 小任务快模型（便宜快，但人设感弱）；留空 = 宿主的插件默认任务。"
        ),
    )

    # 兼容字段：0.1.x 只有这一个开关。现在由 [persona].source 决定，
    # 保留它只是为了老 config.toml 里那行不报未知键；source 为空时才用它推断。
    use_bot_persona: bool = Field(
        default=True,
        description="兼容字段，等价于 [persona].source = follow / custom。",
        json_schema_extra={"hidden": True, "disabled": True},
    )

    # 兼容 0.1.x 的单任务时代：首次启动会把这四个字段迁移成第一个任务，之后不再读。
    hour: int = Field(default=8, ge=0, le=23, description="兼容字段，已迁移到 [[jobs]]。",
                      json_schema_extra={"hidden": True, "disabled": True})
    minute: int = Field(default=0, ge=0, le=59, description="兼容字段，已迁移到 [[jobs]]。",
                        json_schema_extra={"hidden": True, "disabled": True})
    catch_up_minutes: int = Field(default=30, ge=0, le=720, description="兼容字段，已迁移到 [[jobs]]。",
                                  json_schema_extra={"hidden": True, "disabled": True})
    intent: str = Field(default=DEFAULT_INTENT, description="兼容字段，已迁移到 [[jobs]]。",
                        json_schema_extra={"hidden": True, "disabled": True})


class GuardSection(PluginConfigBase):
    """台词守门：模型返回异常时不让错误文本烧掉语音合成的钱。

    两道闸，都在送进 TTS 之前：
      ① 词表闸：命中「只有报错才会出现」的词 → 判废，改说本地备用台词；
      ② 字数闸：任何情况下都截到 max_chars 以内（比任务自己的上限更低时以它为准）。
    两道闸都能单独关掉，词表和备用台词都可以自己改。
    """

    __ui_label__ = "台词守门"

    enabled: bool = Field(
        default=True,
        description="总开关。关掉后模型返回什么就念什么，只保留任务自己的字数上限。",
    )
    max_chars: int = Field(
        default=80,
        description=(
            "送进语音合成前允许的最大字数，超出直接截断。"
            "这是保险丝：任务里的「台词字数上限」比它小时按任务那个算。"
        ),
    )
    ban_words: str = Field(
        default="",
        description=(
            "禁用词，命中任意一个就判定模型返回异常，改用备用台词。"
            "每行一个，也可以用逗号分隔。留空 = 使用内置默认词表"
            "（只收限流、额度、鉴权、AI 拒答这类正常台词里不会出现的词）。"
        ),
    )
    fallback_lines: str = Field(
        default="",
        description=(
            "模型被判定为异常时改说这些，每行一句，随机挑一句（尽量不重复）。"
            "留空 = 使用内置的十句备用台词。"
        ),
    )


class PersonaSection(PluginConfigBase):
    __ui_label__ = "语音人设"

    source: str = Field(
        default="",
        description=(
            "人设来源：follow = 每次现读 MaiBot 的 [personality]，改设置这里自动跟着变；"
            "custom = 只用本插件里这份人设，和设置彻底解绑。留空 = 按旧配置自动推断。"
        ),
    )
    text: str = Field(
        default="",
        description=(
            "插件自己的语音人设全文。首次启用时会把 MaiBot 当前人设原文存一份到这里，"
            "之后可以随便改，不影响 MaiBot 本身的人设。"
        ),
    )
    first_paragraph_only: bool = Field(
        default=True,
        description=(
            "仅 follow 模式生效：只取人设的第一段。后面常是大段关系/暧昧设定，"
            "早上叫人起床用不上还白烧 token；关掉则整个人设都塞进提示词。"
        ),
    )
    initialized: bool = Field(
        default=False,
        description="是否已经做过首次快照。由插件自己维护，别手改。",
        json_schema_extra={"hidden": True, "disabled": True},
    )
    synced_at: str = Field(
        default="",
        description="上次从 MaiBot 设置导入的时间。",
        json_schema_extra={"hidden": True, "disabled": True},
    )


class SipSection(PluginConfigBase):
    __ui_label__ = "SIP 拨号"

    enabled: bool = Field(default=True, description="关闭后只生成台词、不拨号，用于调试。")
    caller_aor: str = Field(
        default="", description="主叫账号，形如 sip:bot@sip.linphone.org（给 MaiBot 用的那个）。"
    )
    caller_user: str = Field(default="", description="鉴权用户名，留空则从主叫账号里取 @ 前面那段。")
    caller_pass: str = Field(default="", description="主叫账号的密码。")
    server: str = Field(
        default="",
        description=(
            "SIP 服务器（出局代理）地址，可写 host、host:port 或 [IPv6]:port，端口留空按 5060。"
            "留空则自动取主叫账号 @ 后面的域名。"
            "sip2sip 必须单独填 proxy.sipthor.net —— 它的账号域名 sip2sip.info 解析不出来。"
            "自建私有 SIP 改了端口就写成 1.2.3.4:5080。"
        ),
    )
    transport: str = Field(
        default="",
        description=(
            "公网账号的传输层，留空 = UDP。填 tcp 时 outbound 会带上 ;transport=tcp，"
            "适合运营商回收 UDP 映射、或自建服务器只放行 TCP 的情况。"
            "只影响公网拨号；内网直呼永远走 UDP（局域网内没有 NAT 要穿）。"
        ),
    )
    callee_aor: str = Field(
        default="", description="被叫账号，即你手机 Linphone 上登录的那个，形如 sip:me@sip.linphone.org。"
    )
    baresip_bin: str = Field(default="/usr/bin/baresip", description="baresip 可执行文件路径。")
    module_path: str = Field(default="/usr/lib/baresip/modules", description="baresip 模块目录。")
    ring_seconds: int = Field(
        default=45, ge=10, le=180, description="单次呼叫总时长（秒），到点强制挂断。"
    )
    retry_times: int = Field(default=2, ge=0, le=5, description="拨号失败后的重拨次数。")
    retry_interval_seconds: int = Field(
        default=30, ge=5, le=600, description="两次重拨之间的间隔（秒）。"
    )

    # ─── 内网直呼 ───
    lan_call_enabled: bool = Field(
        default=False,
        description=(
            "同一局域网时直接走内网呼叫（把 INVITE 发给对端的局域网 IP），"
            "媒体不再绕到海外服务器再回来。只有真的探测到同网段有 SIP 设备应答才会启用，"
            "否则照常走公网账号——所以拨号机换网络时不会因为找不到对端而打不通。"
        ),
    )
    lan_target: str = Field(
        default="",
        description=(
            "内网直呼目标，填 IP 或 IP:端口（要接电话那台的局域网地址）。"
            "留空 = 拨号前自动找：先问上次学到的地址，不应答再扫临时端口段把它找回来。"
        ),
    )
    lan_scan_enabled: bool = Field(
        default=True,
        description=(
            "上次学到的端口失效时（Linphone 重启、换 WiFi），自动扫一遍本机的临时端口段"
            "把新的 SIP 端口找回来。只发 OPTIONS 问询，不响铃、不建立通话。"
            "正因为 Linphone 的端口是内核随机分配的，又没有设置项能固定，才需要这一步。"
        ),
    )
    lan_probe_timeout: float = Field(
        default=1.2, ge=0.3, le=5.0, description="自动探测时每个地址等应答的秒数。"
    )
    lan_fallback_public: bool = Field(
        default=True,
        description="内网直呼没接通时，自动用公网账号再拨一次（避免静默失败）。",
    )
    lan_subnet_scan: bool = Field(
        default=True,
        description=(
            "对方换了 IP 但 App 没重启时（SIP 端口不变），拿记住的端口扫一遍本机所在网段，把它找回来。"
            "校园网/DHCP 每天换一个 /24，这一步让用户不用重新填地址。"
            "对每个地址只发一个 SIP OPTIONS 问询，不响铃、不建立会话、不发业务数据。"
        ),
    )
    lan_subnet_prefix: int = Field(
        default=20,
        description=(
            "上面那次整段扫描的范围。/24 最收敛（254 个地址，约 1 秒）；"
            "/20 适合校园网这种按 /20 分池的网络（4094 个地址，实测约 9 秒）；"
            "填得比 /19 更宽会自动收敛到 /19（单次最多发 8192 个包）。"
        ),
    )


class TtsSection(PluginConfigBase):
    __ui_label__ = "语音合成"

    backend: str = Field(
        default="edge",
        description=(
            "当前启用的后端：edge = 微软 Edge 朗读（免费、无需密钥）；"
            "openai = 任意 OpenAI 兼容 /v1/audio/speech；"
            "minimax = MiniMax T2A；doubao = 豆包 / 火山引擎语音合成。"
        ),
    )
    timeout: int = Field(default=30, ge=5, le=120, description="单次合成超时（秒）。")

    # 旧字段：仅用于兼容历史配置，新配置请用下面带前缀的字段。
    voice: str = Field(
        default="zh-CN-XiaoyiNeural",
        description="兼容字段，等价于 edge_voice。",
        json_schema_extra={"hidden": True, "disabled": True},
    )
    rate: str = Field(
        default="+0%",
        description="兼容字段，等价于 edge_rate。",
        json_schema_extra={"hidden": True, "disabled": True},
    )
    api_url: str = Field(
        default="", description="兼容字段，等价于 openai_url。", json_schema_extra={"hidden": True, "disabled": True}
    )
    api_key: str = Field(
        default="", description="兼容字段，等价于 openai_key。", json_schema_extra={"hidden": True, "disabled": True}
    )
    api_model: str = Field(
        default="tts-v4",
        description="兼容字段，等价于 openai_model。",
        json_schema_extra={"hidden": True, "disabled": True},
    )
    response_format: str = Field(
        default="mp3",
        description="兼容字段，等价于 openai_format。",
        json_schema_extra={"hidden": True, "disabled": True},
    )

    # ── Edge（免费）──
    edge_voice: str = Field(default="zh-CN-XiaoyiNeural", description="edge 音色，如 zh-CN-XiaoyiNeural。")
    edge_rate: str = Field(default="+0%", description="edge 语速，如 +10% / -10%。")

    # ── OpenAI 兼容 ──
    openai_url: str = Field(
        default="", description="OpenAI 兼容接口地址，如 https://api.siliconflow.cn/v1/audio/speech。"
    )
    openai_key: str = Field(default="", description="OpenAI 兼容接口的 Bearer Token。")
    openai_model: str = Field(default="tts-1", description="OpenAI 兼容接口的 model。")
    openai_voice: str = Field(default="alloy", description="OpenAI 兼容接口的 voice。")
    openai_format: str = Field(default="mp3", description="OpenAI 兼容接口的 response_format。")
    openai_speed: float = Field(default=1.0, ge=0.25, le=4.0, description="OpenAI 兼容接口的 speed。")

    # ── MiniMax ──
    minimax_url: str = Field(default="https://api.minimaxi.com/v1/t2a_v2", description="MiniMax T2A 接口地址。")
    minimax_key: str = Field(default="", description="MiniMax API Key（Bearer）。")
    minimax_group_id: str = Field(
        default="", description="MiniMax GroupId，多数情况可以不填；报 GroupId 缺失时才需要。"
    )
    minimax_model: str = Field(default="speech-2.6-turbo", description="MiniMax 模型名。")
    minimax_voice: str = Field(default="female-shaonv", description="MiniMax voice_id。")
    minimax_format: str = Field(default="mp3", description="MiniMax 音频格式。")
    minimax_speed: float = Field(default=1.0, ge=0.5, le=2.0, description="MiniMax 语速倍率。")

    # ── 豆包 / 火山引擎 ──
    # 新版控制台（X-Api-Key 单头鉴权）不需要 AppID，界面上也不再提供这个输入框；
    # 下面两个字段只为还在用 v1 旧接口、手改 config.toml 的人保留。
    doubao_api: str = Field(
        default="v3",
        description="豆包接口版本：v3 = 语音合成 2.0（推荐，只需 API Key）。",
        json_schema_extra={"hidden": True, "disabled": True},
    )
    doubao_url: str = Field(
        default="https://openspeech.bytedance.com/api/v3/tts/unidirectional",
        description="v3 用 https://openspeech.bytedance.com/api/v3/tts/unidirectional。",
    )
    doubao_app_id: str = Field(
        default="",
        description="只有 v1 旧接口需要，新版控制台没有这一项。",
        json_schema_extra={"hidden": True, "disabled": True},
    )
    doubao_token: str = Field(default="", description="火山引擎 API Key（新版控制台「API Key 管理」里那串）。")
    doubao_cluster: str = Field(
        default="volcano_tts",
        description="只有 v1 旧接口需要。",
        json_schema_extra={"hidden": True, "disabled": True},
    )
    doubao_resource_id: str = Field(default="seed-tts-2.0", description="v3 用的 X-Api-Resource-Id。")
    doubao_voice: str = Field(default="", description="豆包 speaker / voice_type，如 zh_female_shuangkuaisisi_moon_bigtts。")
    doubao_format: str = Field(default="mp3", description="豆包音频格式。")
    doubao_speed: float = Field(default=1.0, ge=0.2, le=3.0, description="豆包语速倍率。")
    doubao_sample_rate: int = Field(default=24000, description="豆包采样率。")


class WakeCallConfig(PluginConfigBase):
    plugin: PluginSection = Field(default_factory=PluginSection)
    wake: WakeSection = Field(default_factory=WakeSection)
    jobs: list[JobSection] = Field(default_factory=list)
    persona: PersonaSection = Field(default_factory=PersonaSection)
    sip: SipSection = Field(default_factory=SipSection)
    tts: TtsSection = Field(default_factory=TtsSection)
    guard: GuardSection = Field(default_factory=GuardSection)


class WakeCallPlugin(MaiBotPlugin):
    """到点生成一句台词，合成语音，再用 SIP 呼到手机上。"""

    config_model = WakeCallConfig

    def __init__(self) -> None:
        super().__init__()
        self._task: Optional[asyncio.Task[None]] = None
        self._state: Dict[str, Any] = {}
        self._state_path: Optional[Path] = None
        self._busy = False
        # 内网对端学习：Linphone 的 SIP 端口是随机分配的（实测 52038，不是 5060），
        # 又没有设置项能固定，所以只能靠「对端主动发包时记下源地址」来知道他今天在哪个端口。
        self._lan_transport: Optional[asyncio.DatagramTransport] = None
        self._lan_task: Optional[asyncio.Task[None]] = None
        # 后台预热：闹钟响之前就把端口摸清楚，别让拨号现场去扫那两万多个端口。
        self._prewarm_task: Optional[asyncio.Task[None]] = None

    # ──── 生命周期 ────

    def _check_deps(self) -> None:
        """启动时把缺的外部命令一次点清。

        这两个都是外部可执行文件，装不上就永远拨不出去。等到任务触发那一刻才发现，
        代价是错过一次闹钟，所以提前说。
        """
        if shutil.which("ffmpeg") is None:
            self.ctx.logger.warning("环境自检: %s", MISSING_FFMPEG)
        # 用户可能填相对名（baresip）也可能填绝对路径，两种都认，免得误报缺失。
        baresip_bin = self.config.sip.baresip_bin
        if not (Path(baresip_bin).exists() or shutil.which(baresip_bin)):
            self.ctx.logger.warning(
                "环境自检: 找不到 baresip（%s），拨号会失败。"
                "Debian/proot 装：apt install -y baresip baresip-modules",
                baresip_bin,
            )

    @staticmethod
    def _cleanup_stale_sip_dirs() -> None:
        """清掉上次被强杀（OOM / 卸载）留在 /tmp 的临时 SIP 配置。

        accounts 里是明文密码。正常收摊会 rmtree，但 SIGKILL 时 finally 不执行，
        目录就留在那儿了。这里只清一小时以前的，正在拨的那一份不会被误删。
        """
        cutoff = time.time() - 3600
        with contextlib.suppress(OSError):
            for item in Path(tempfile.gettempdir()).glob("wakecall-sip-*"):
                with contextlib.suppress(OSError):
                    if item.is_dir() and item.stat().st_mtime < cutoff:
                        shutil.rmtree(item, ignore_errors=True)

    async def on_load(self) -> None:
        self._state_path = self._resolve_state_path()
        self._state = self._load_state()
        self._cleanup_stale_sip_dirs()
        # 首次启用（或被上传到别人的机器上第一次跑）时，把人设全文存到插件里。
        self._ensure_persona_snapshot()
        # 老配置只有一个时间点，迁移成第一个任务。
        self._ensure_jobs()
        self._migrate_state()
        self._restart_timer()
        jobs = self.config.jobs
        active = [j for j in jobs if j.enabled]
        self.ctx.logger.info(
            "麦麦电话闹钟已加载: 总开关=%s 任务=%d(启用 %d) 主叫=%s 被叫=%s",
            self._enabled(),
            len(jobs),
            len(active),
            self.config.sip.caller_aor.strip() or "(未配置)",
            self.config.sip.callee_aor.strip() or "(未配置)",
        )
        for job in jobs:
            self.ctx.logger.info(
                "  · %s %02d:%02d %s",
                job.label or job.id or "(未命名)",
                job.hour,
                job.minute,
                "启用" if job.enabled else "停用",
            )
        if self._enabled() and self.config.sip.enabled:
            missing = [
                name
                for name in ("caller_aor", "caller_pass", "callee_aor")
                if not str(getattr(self.config.sip, name)).strip()
            ]
            if missing:
                self.ctx.logger.warning("麦麦电话闹钟缺少 SIP 配置: %s，到点会拨不出去", ", ".join(missing))
        if self._enabled():
            self._check_deps()
        if self.config.sip.lan_call_enabled:
            await self._start_lan_listener()
            self._start_lan_prewarm()

    async def on_unload(self) -> None:
        await self._stop_timer()
        await self._stop_lan_listener()
        await self._stop_lan_prewarm()
        self.ctx.logger.info("麦麦电话闹钟已卸载")

    async def on_config_update(self, scope: str, config_data: Dict[str, Any], version: str) -> None:
        del config_data
        if scope != "self":
            return
        await self._stop_timer()
        self._restart_timer()
        # 内网直呼是刚加的开关，保存时开/关要立刻反映到 5060 监听上，
        # 否则用户得重启插件才生效。
        if self.config.sip.lan_call_enabled:
            await self._start_lan_listener()
            self._start_lan_prewarm()
        else:
            await self._stop_lan_listener()
            await self._stop_lan_prewarm()
        self.ctx.logger.info(
            "麦麦电话闹钟配置已更新: 总开关=%s 任务数=%d version=%s",
            self._enabled(),
            len(self.config.jobs),
            version,
        )

    # ──── 定时器 ────

    def _enabled(self) -> bool:
        return bool(self.config.wake.enabled)

    def _restart_timer(self) -> None:
        if not self._enabled():
            return
        # 必须先把上一条收摊。on_config_update / 各个保存接口都会调到这里，
        # 双击保存、或宿主重放配置时，旧写法会直接覆盖 self._task，
        # 旧循环就成了没人管的野任务：_stop_timer 只等得到最新那条，
        # 卸载插件后残留的那条还在按 20 秒一轮拨号。
        stale = self._task
        if stale is not None and not stale.done():
            stale.cancel()
        self._task = asyncio.create_task(self._loop(), name="wake-call")

    async def _stop_timer(self) -> None:
        task = self._task
        self._task = None
        if task is None:
            return
        task.cancel()
        with contextlib.suppress(asyncio.CancelledError):
            await task

    async def _loop(self) -> None:
        # 自己是不是「当前那条」：_restart_timer 已经 cancel 过旧任务，
        # 这里再判一次，防止取消没来得及生效时两条循环同时空转。
        me = asyncio.current_task()
        while self._task is me:
            try:
                await self._tick()
            except asyncio.CancelledError:
                raise
            except Exception:
                self.ctx.logger.exception("麦麦电话闹钟检查失败")
            await asyncio.sleep(self.config.wake.check_interval_seconds)

    def _due_for(self, job: "JobSection", now: datetime) -> tuple[Optional[datetime], str, bool]:
        """这一刻该补哪一次，该记在哪个日期名下。

        返回 (到期时间, 记账日期, 是否已过宽限期)；到期时间 None 表示现在不该拨。

        跨零点要回看昨天：23:50 的任务在 00:05 仍在宽限期内，而
        `now.replace(hour=23)` 算出来的是**今晚** 23:50，比 now 大，会直接判成
        「还没到」，补拨窗口就永远失效了。
        """
        due = now.replace(hour=job.hour, minute=job.minute, second=0, microsecond=0)
        # 窗口 0 的语义是「只在当分钟内触发」，不是一个精确到秒的瞬间：
        # 检查间隔本身就有 20 秒，按 0 秒算等于永不触发。这里给足一分钟。
        window = max(60, max(0, int(job.catch_up_minutes)) * 60)
        if now < due:
            prev = due - timedelta(days=1)
            if (now - prev).total_seconds() <= window:
                return prev, prev.strftime("%Y-%m-%d"), False
            return None, "", False
        if (now - due).total_seconds() > window:
            return None, due.strftime("%Y-%m-%d"), True
        return due, due.strftime("%Y-%m-%d"), False

    async def _tick(self) -> None:
        if not self._enabled() or self._busy:
            return
        now = datetime.now()
        for job in list(self.config.jobs):
            # 一次只拨一通：上一个任务还没拨完，剩下的等下一轮（宽限期内会补上）。
            if self._busy:
                break
            if not job.enabled:
                continue
            due, fire_date, missed = self._due_for(job, now)
            jstate = self._job_state(job.id)
            if due is None:
                if missed and jstate.get("skipped_date") != fire_date:
                    jstate["skipped_date"] = fire_date
                    self._save_state()
                    self.ctx.logger.info("任务「%s」已错过宽限期，本次跳过", job.label or job.id)
                continue
            if jstate.get("last_fired_date") == fire_date:
                continue
            attempts = self._attempts_today(fire_date, job.id)
            if attempts >= MAX_ATTEMPTS:
                # 打满就别再每 20 秒空转一遍了，并且留一条日志——
                # 否则事后只看到「今天没响」，查不出是已经试了 3 次放弃的。
                if jstate.get("skipped_date") != fire_date:
                    jstate["skipped_date"] = fire_date
                    self._save_state()
                    self.ctx.logger.warning(
                        "任务「%s」今天已失败 %s 次，放弃今日拨打（最后一次原因：%s）",
                        job.label or job.id,
                        attempts,
                        jstate.get("last_error") or "未知",
                    )
                continue
            await self._run_job(job, now, fire_date, attempts)

    async def _run_job(self, job: "JobSection", now: datetime, today: str, attempts: int) -> None:
        self._busy = True
        try:
            ok, error = await self._fire(job)
        except asyncio.CancelledError:
            raise
        except Exception as exc:  # noqa: BLE001
            # 不能让内部异常变成「这一通没发生过」：那样 20 秒后 tick 会再拨一次，
            # 用户早上会连收好几通电话。这里统一按失败记账，交给重试逻辑处理。
            ok, error = False, f"内部异常: {exc!r}"
            self.ctx.logger.exception("任务「%s」执行过程中抛出未处理异常", (job.label or job.id))
        finally:
            self._busy = False

        jstate = self._job_state(job.id)
        if ok:
            jstate["last_fired_date"] = today
            jstate["last_fired_at"] = now.isoformat(timespec="seconds")
            jstate.pop("attempts", None)
            jstate.pop("skipped_date", None)
            # 成功必须覆盖上一次的失败记录，否则侧边栏会永远停在历史错误上
            jstate["last_result"] = "拨出成功"
            jstate.pop("last_error", None)
            self._save_state()
            self.ctx.logger.info(
                "任务「%s」已拨出: %s", job.label or job.id, now.isoformat(timespec="seconds")
            )
            return

        jstate["attempts"] = {"date": today, "count": attempts + 1}
        jstate["last_result"] = f"失败: {error}"
        jstate["last_error"] = error
        self._save_state()
        self.ctx.logger.error(
            "任务「%s」失败(%s/%s): %s", job.label or job.id, attempts + 1, MAX_ATTEMPTS, error
        )
        if attempts + 1 < MAX_ATTEMPTS:
            await asyncio.sleep(RETRY_DELAY_SECONDS)

    # ──── 主流程 ────

    async def _fire(self, job: Optional["JobSection"] = None) -> tuple[bool, str]:
        text = await self._gen_text(job)
        # 空台词不能在这里一刀切：守门开着时它是「改说备用台词」的输入，
        # 在这之前 return 会让 _guard_text 里那段兜底永远跑不到（叫起床一声不响）。
        if not text and not bool(self.config.guard.enabled):
            return False, "生成台词失败或为空"
        # 送 TTS 之前先过守门：模型/中转站抽风吐一大段报错时，这段文本按字数计费，
        # 念出来还很难听。判废就换本地备用台词，字数超限就截断。
        text, guard_note = self._guard_text(text, job)
        if not text:
            return False, "台词为空"
        if guard_note:
            self.ctx.logger.warning("台词守门：%s", guard_note)
        self.ctx.logger.info("任务「%s」台词: %s", (job.label if job else "") or "默认", text)
        state = self._job_state(job.id if job else "")
        state["last_text"] = text
        state["last_guard"] = guard_note
        self._save_state()

        if not self.config.sip.enabled:
            self.ctx.logger.info("SIP 拨号已关闭，仅生成台词（调试模式）")
            return True, ""

        audio_dir = self._audio_dir()
        try:
            wav = await self._synthesize(text, audio_dir)
        except Exception as exc:
            return False, f"语音合成失败: {exc!r}"

        last_error = ""
        for attempt in range(1, self.config.sip.retry_times + 2):
            try:
                last_error = await self._dial(wav)
            except Exception as exc:
                last_error = repr(exc)
            if not last_error:
                if attempt > 1:
                    self.ctx.logger.info("任务第 %s 次拨号接通", attempt)
                return True, ""
            self.ctx.logger.warning("任务第 %s 次拨号失败: %s", attempt, last_error)
            if attempt <= self.config.sip.retry_times:
                await asyncio.sleep(self.config.sip.retry_interval_seconds)
        return False, last_error

    def _bot_config_path(self) -> Optional[Path]:
        """定位本 bot 的 bot_config.toml（插件在 bots/<id>/plugins/<name>/ 下）。"""
        here = Path(__file__).resolve()
        for base in here.parents[:4]:
            for candidate in (base / "config" / "bot_config.toml", base / "bot_config.toml"):
                if candidate.is_file():
                    return candidate
        return None

    def _bot_persona_raw(self) -> str:
        """现读 bot_config.toml 里的人设原文（不裁剪）。"""
        path = self._bot_config_path()
        if path is None:
            return ""
        try:
            import tomllib

            data = tomllib.loads(path.read_text(encoding="utf-8"))
        except Exception:  # noqa: BLE001 - 配置格式问题不该拖垮叫醒
            self.ctx.logger.warning("读 bot_config.toml 失败，本次不注入人设: %s", path)
            return ""
        raw = str((data.get("personality") or {}).get("personality") or "").strip()
        if not raw:
            # 顶层字段为空时，退回 selected_profile 指向的那条人设。
            sec = data.get("personality") or {}
            want = str(sec.get("selected_profile") or "").strip()
            for prof in sec.get("profiles") or []:
                if str(prof.get("name") or "").strip() == want:
                    raw = str(prof.get("personality") or "").strip()
                    break
        return raw

    def _bot_persona(self) -> str:
        """兼容旧行为：人设第一段 + 截 300 字。"""
        raw = self._bot_persona_raw()
        if not raw:
            return ""
        # 只取第一段：后面通常是大段关系/暧昧设定，早上叫人起床用不上，还白烧 token。
        return re.split(r"\n\s*\n", raw)[0].strip()[:300]

    def _persona_source(self) -> str:
        """当前人设来源：follow / custom。

        [persona].source 为空时按旧的 use_bot_persona 推断，兼容 0.1.x 的配置。
        """
        src = (self.config.persona.source or "").strip().lower()
        if src in {"follow", "custom"}:
            return src
        return "follow" if bool(getattr(self.config.wake, "use_bot_persona", True)) else "custom"

    def _persona_text(self) -> tuple[str, str]:
        """返回这次真正要拼进提示词的人设，以及一句来源说明。"""
        p = self.config.persona
        if self._persona_source() == "custom":
            text = (p.text or "").strip()
            if text:
                return text[:PERSONA_INJECT_LIMIT], "插件内人设"
            # 独立人设被清空了，退回跟随设置，总比一句人设都没有强。
            fallback = "插件内人设为空，临时跟随设置"
        else:
            fallback = "MaiBot 设置"
        raw = self._bot_persona_raw()
        if not raw:
            return "", ""
        if bool(p.first_paragraph_only):
            raw = re.split(r"\n\s*\n", raw)[0].strip()
        return raw[:PERSONA_INJECT_LIMIT], fallback

    def _ensure_persona_snapshot(self) -> None:
        """首次启用时把 MaiBot 的人设全文存一份到插件里。

        目的：插件打包上传给别人时，一装上就有一份完整人设可用，
        不用先去翻 bot_config.toml；之后在侧边栏里改这份也不会影响 MaiBot。
        """
        p = self.config.persona
        if bool(p.initialized):
            return
        raw = self._bot_persona_raw()
        if not raw:
            # 宿主里还没写人设：先把 source 迁移落盘，快照留到下次启动再试。
            if not (p.source or "").strip():
                updates = {"source": self._persona_source()}
                try:
                    self._write_config({"persona": updates})
                    self._apply_to_memory({"persona": updates})
                except Exception:  # noqa: BLE001 - 落盘失败不该拦住叫醒
                    self.ctx.logger.warning("人设来源迁移写盘失败", exc_info=True)
            self.ctx.logger.info("MaiBot 里还没有人设，语音人设栏位先留空")
            return
        updates = {
            "text": raw,
            "source": self._persona_source(),
            "initialized": True,
            "synced_at": datetime.now().isoformat(timespec="seconds"),
        }
        try:
            self._write_config({"persona": updates})
        except Exception:  # noqa: BLE001
            self.ctx.logger.warning("人设快照写盘失败，本次只在内存生效", exc_info=True)
        self._apply_to_memory({"persona": updates})
        self.ctx.logger.info("首次启用：已把 MaiBot 人设全文(%d 字)存进语音人设栏位", len(raw))

    async def _gen_text(self, job: Optional["JobSection"] = None) -> str:
        wake = self.config.wake
        intent = (job.intent if job and job.intent.strip() else wake.intent) or DEFAULT_INTENT
        hour = job.hour if job else wake.hour
        minute = job.minute if job else wake.minute
        try:
            task_text = intent.format(hour=hour, minute=f"{minute:02d}", label=(job.label if job else ""))
        except (KeyError, IndexError, ValueError):
            task_text = intent

        persona, note = self._persona_text()
        if persona:
            self.ctx.logger.info("台词人设取自%s(%d 字): %s…", note, len(persona), persona[:36])
            # 人设原文常带「正在上网聊天」这类场景，和打电话冲突，先声明一次场景覆盖。
            prompt = (
                f"{persona}\n\n"
                "（以上是你的设定。现在你正在给他打电话，不是群里聊天，也没人跟你搭话，"
                "你只管按下面的要求把那一两句说出口。）\n\n"
                f"{task_text}"
            ).strip()
        else:
            prompt = task_text

        task = ((job.llm_task if job and job.llm_task.strip() else wake.llm_task) or "").strip()
        result: Any = {}
        if task:
            try:
                # 指定任务：replyer = 她平时聊天用的模型，写出来的口吻才像本人。
                result = await self.ctx.llm.generate(prompt, max_tokens=300, task_name=task)
            except Exception:
                self.ctx.logger.warning("台词模型任务 %s 调用失败，回退宿主默认任务", task, exc_info=True)
                result = {}

        raw = ""
        if isinstance(result, dict):
            if not result.get("success", True):
                self.ctx.logger.warning("模型返回失败: %s", result.get("error") or result)
            raw = str(result.get("response") or "")

        # 聊天模型偶尔会回空（提示词不像聊天场景），空一次就退回插件默认任务补一次。
        if not self._clean_text(raw) and task:
            self.ctx.logger.info("任务 %s 没给出可用台词，回退默认任务重试", task)
            try:
                result = await self.ctx.llm.generate(prompt, max_tokens=300)
            except Exception:
                self.ctx.logger.exception("生成台词时模型调用失败")
                return ""
            if isinstance(result, dict):
                if not result.get("success", True):
                    self.ctx.logger.warning("模型返回失败: %s", result.get("error") or result)
                raw = str(result.get("response") or "")

        limit = int(job.max_chars) if job else int(wake.max_chars)
        return self._clean_text(raw)[:limit].strip()

    @staticmethod
    def _clean_text(text: str) -> str:
        text = (text or "").replace("\r", "").strip()
        if not text:
            return ""
        first = next((line.strip() for line in text.split("\n") if line.strip()), "")
        first = _PREFIX_RE.sub("", first)
        first = first.strip().strip('"“”\'‘’「」')
        return first.strip()

    # ──── 台词守门（内容闸 + 字数闸）────

    def _ban_words(self) -> list[str]:
        """当前生效的禁用词：自己填的优先，留空用内置默认表。"""
        raw = (self.config.guard.ban_words or "").strip()
        if not raw:
            return list(DEFAULT_BAN_WORDS)
        parts = re.split(r"[\n,，、;；|]+", raw)
        return [part.strip().lower() for part in parts if part.strip()]

    def _guard_hit(self, text: str) -> str:
        """命中禁用词就返回那个词，否则返回空串。"""
        # 压缩空白：模型常把「rate   limit」拆成多空格，或一句话里换行折行。
        low = re.sub(r"\s+", " ", (text or "").lower())
        for word in self._ban_words():
            if word in low:
                return word
        return ""

    def _fallback_pool(self) -> list[str]:
        raw = self.config.guard.fallback_lines or ""
        lines = [line.strip() for line in raw.splitlines() if line.strip()]
        return lines or list(DEFAULT_FALLBACK_LINES)

    def _fallback_line(self) -> str:
        pool = self._fallback_pool()
        # 备用台词一晚上可能被用几次，尽量别和上一句重复。
        last = str(self._state.get("last_fallback") or "")
        choices = [line for line in pool if line != last] or pool
        line = random.choice(choices)
        self._state["last_fallback"] = line
        return line

    def _guard_cap(self) -> int:
        """守门的字数上限，永远落在 10~300 之间。

        不在 pydantic 字段上加 ge/le：那里校验失败会让整个插件加载不起来，
        而配置是可能被手工改坏的。读的时候夹一下，最坏也只是数值不对，不会连累其他功能。
        """
        try:
            value = int(self.config.guard.max_chars)
        except (AttributeError, TypeError, ValueError):
            return 80
        return min(300, max(10, value))

    def _guard_text(self, text: str, job: Optional["JobSection"] = None) -> tuple[str, str]:
        """过内容闸和字数闸，返回（最终台词, 说明）。说明非空表示动过手脚，要记日志。"""
        guard = self.config.guard
        note = ""
        if bool(guard.enabled):
            # 模型整段挂掉时 _gen_text 会返回空串。以前这种情况直接判「生成失败」不打，
            # 但闹钟电话最不能接受的就是一声不响 —— 守门开着就改说备用台词，照常拨出去。
            if not (text or "").strip():
                text = self._fallback_line()
                note = "模型没给出可用台词，已改说备用台词"
                self.ctx.logger.warning("模型返回为空或不可用，改说备用台词：%s", text)
            hit = self._guard_hit(text)
            if hit:
                original = text
                text = self._fallback_line()
                note = f"命中禁用词「{hit}」，已改说备用台词"
                # 原始返回只留前 200 字进日志：它可能是几百字英文，全存下来没意义。
                self.ctx.logger.warning(
                    "台词命中禁用词 %r，改说备用台词（原返回 %d 字）: %s",
                    hit,
                    len(original),
                    original[:200],
                )

        # 字数闸：守门上限 / 任务上限取最小。上限本身在配置里做过合法化，
        # 这里再兜一次 —— 配置被手工改坏时不能让「读取状态」整个抛异常。
        caps = [self._guard_cap() if bool(guard.enabled) else 10 ** 6]
        caps.append(int(job.max_chars) if job is not None else int(self.config.wake.max_chars))
        limit = max(1, min(caps))
        if len(text) > limit:
            text = text[:limit].strip()
            note = note or f"超出 {limit} 字，已截断"

        return text.strip(), note

    # ──── 语音合成 ────

    def _tts_format(self, backend: Optional[str] = None) -> str:
        """当前后端（或指定后端）产出的音频容器格式，决定临时文件后缀。"""
        tts = self.config.tts
        backend = (backend or tts.backend or "edge").strip().lower()
        if backend == "openai":
            fmt = tts.openai_format or tts.response_format
        elif backend == "minimax":
            fmt = tts.minimax_format
        elif backend == "doubao":
            fmt = tts.doubao_format
        else:
            fmt = "mp3"  # edge-tts 写出来就是 mp3
        fmt = (fmt or "mp3").strip().lower().lstrip(".")
        return fmt if fmt in {"mp3", "wav", "ogg", "opus", "pcm", "aac", "flac", "m4a"} else "mp3"

    async def _tts_generate(
        self, text: str, raw: Path, backend: Optional[str] = None
    ) -> None:
        """按 backend 把文本合成为文件，落到 raw。

        backend 只是「这一次用哪个」，**不改 self.config** —— 试听就是靠这个参数
        临时换后端；以前直接改 self.config.tts.backend 再在 finally 改回来，
        和定时任务撞车时会把对方刚选的音色/后端覆盖掉。
        """
        chosen = (backend or self.config.tts.backend or "edge").strip().lower()
        if chosen == "openai":
            await self._tts_openai(text, raw)
        elif chosen == "minimax":
            await self._tts_minimax(text, raw)
        elif chosen == "doubao":
            await self._tts_doubao(text, raw)
        else:
            await self._tts_edge(text, raw)

    async def _synthesize(
        self, text: str, outdir: Path, backend: Optional[str] = None
    ) -> Path:
        """合成一段待播的音频。

        backend 指定「这一次」用哪个后端，默认跟随配置。试拨固定传 edge：
        打测试电话只为听通不通、响不响，不该逼用户先把正式音色换成 edge
        再换回去——换的过程中定时任务还可能正好触发，读到一个不该用的后端。
        """
        outdir.mkdir(parents=True, exist_ok=True)
        backend = (backend or self.config.tts.backend or "edge").strip().lower()
        raw = outdir / f"raw.{self._tts_format(backend)}"
        try:
            await self._tts_generate(text, raw, backend)
            if not raw.exists() or raw.stat().st_size < 1024:
                raise RuntimeError(f"{backend} 后端未产出有效音频")
        except Exception as exc:
            # 兜底：豆包 / MiniMax / OpenAI 只要报错（欠费、限流、鉴权变动、服务抖动），
            # 以前整通电话直接不打。叫起床最不能接受的就是"一声都没响"，
            # 所以退回 edge（免费、免密钥），音色不同但叫她起来够用了。
            if backend == "edge":
                raise
            self.ctx.logger.warning("TTS(%s) 合成失败，自动退回 edge：%r", backend, exc)
            raw = outdir / "raw.mp3"
            with contextlib.suppress(Exception):
                raw.unlink()  # 清掉可能的半成品，免得 ffmpeg 读到残缺文件
            try:
                await self._tts_edge(text, raw)
            except Exception as exc2:
                raise RuntimeError(
                    f"{backend} 合成失败({exc!r})，edge 兜底也失败({exc2!r})"
                ) from exc2
            if not raw.exists() or raw.stat().st_size < 1024:
                raise RuntimeError(f"{backend} 与 edge 兜底均未产出有效音频")
            self.ctx.logger.info("已用 edge 兜底完成合成（%s 后端不可用）", backend)
        wav = outdir / "wake.wav"
        # 台词只说一遍，后面补静音：接通后才从头播，说完就安静，不再循环重复。
        await self._to_wav(raw, wav, seconds=PLAY_SECONDS, loop=False)
        # 响铃阶段要用的静音源。以前把台词文件当 alert，响铃时就在播，
        # 等 20 秒后接起来那句早说完了 —— 这就是"接了没声音"的一个来源。
        silence = outdir / "silence.wav"
        if not silence.exists() or silence.stat().st_size < 16000:
            await self._silence_wav(silence, seconds=PLAY_SECONDS + 60)
        return wav

    async def _tts_edge(self, text: str, raw: Path) -> None:
        tts = self.config.tts
        voice = (tts.edge_voice or tts.voice or "zh-CN-XiaoyiNeural").strip()
        rate = (tts.edge_rate or tts.rate or "+0%").strip()
        vendor = Path(__file__).resolve().parent / "vendor"
        env = dict(os.environ)
        if vendor.is_dir():
            env["PYTHONPATH"] = str(vendor) + (
                os.pathsep + env["PYTHONPATH"] if env.get("PYTHONPATH") else ""
            )
        cmd = [
            sys.executable,
            "-m",
            "edge_tts",
            "--voice",
            voice,
            "--text",
            text,
            "--write-media",
            str(raw),
        ]
        if rate and rate not in ("+0%", "0%", ""):
            cmd += ["--rate", rate]
        proc = await asyncio.create_subprocess_exec(
            *cmd,
            env=env,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
        )
        try:
            _, err = await asyncio.wait_for(proc.communicate(), timeout=tts.timeout)
        except asyncio.TimeoutError:
            proc.kill()
            raise RuntimeError("edge-tts 合成超时")
        if proc.returncode != 0 or not raw.exists() or raw.stat().st_size == 0:
            raise RuntimeError(f"edge-tts 失败: {err.decode(errors='ignore')[:200]}")

    async def _tts_openai(self, text: str, raw: Path) -> None:
        tts = self.config.tts
        url = (tts.openai_url or tts.api_url or "").strip()
        if not url:
            raise RuntimeError("openai 后端缺少接口地址（openai_url）")
        key = (tts.openai_key or tts.api_key or "").strip()
        model = (tts.openai_model or tts.api_model or "tts-1").strip()
        voice = (tts.openai_voice or "alloy").strip()
        fmt = (tts.openai_format or tts.response_format or "mp3").strip().lower()
        import httpx  # 延迟导入，避免 edge 模式下的无用依赖

        headers = {"Content-Type": "application/json"}
        if key:
            headers["Authorization"] = f"Bearer {key}"
        payload = {
            "model": model,
            "input": text,
            "voice": voice,
            "response_format": fmt,
            "speed": float(tts.openai_speed or 1.0),
        }
        async with httpx.AsyncClient(timeout=tts.timeout) as client:
            resp = await client.post(url, json=payload, headers=headers)
        if resp.status_code >= 400:
            raise RuntimeError(f"openai 兼容接口 HTTP {resp.status_code}: {resp.text[:300]}")
        if not resp.content:
            raise RuntimeError("openai 兼容接口返回空音频")
        raw.write_bytes(resp.content)

    async def _tts_minimax(self, text: str, raw: Path) -> None:
        """MiniMax T2A v2：返回 audio 字段是 hex 编码的音频。"""
        tts = self.config.tts
        key = tts.minimax_key.strip()
        if not key:
            raise RuntimeError("MiniMax 后端缺少 minimax_key")
        import base64

        import httpx

        url = (tts.minimax_url or "https://api.minimaxi.com/v1/t2a_v2").strip()
        params = {"GroupId": tts.minimax_group_id.strip()} if tts.minimax_group_id.strip() else None
        payload = {
            "model": (tts.minimax_model or "speech-2.6-turbo").strip(),
            "text": text,
            "stream": False,
            "voice_setting": {
                "voice_id": (tts.minimax_voice or "female-shaonv").strip(),
                "speed": float(tts.minimax_speed or 1.0),
                "vol": 1.0,
                "pitch": 0,
            },
            "audio_setting": {
                "sample_rate": 32000,
                "bitrate": 128000,
                "format": (tts.minimax_format or "mp3").strip().lower(),
                "channel": 1,
            },
        }
        headers = {"Authorization": f"Bearer {key}", "Content-Type": "application/json"}
        async with httpx.AsyncClient(timeout=tts.timeout) as client:
            resp = await client.post(url, json=payload, headers=headers, params=params)
        if resp.status_code >= 400:
            raise RuntimeError(f"MiniMax HTTP {resp.status_code}: {resp.text[:300]}")
        try:
            data = resp.json()
        except Exception:  # noqa: BLE001
            raise RuntimeError(f"MiniMax 返回非 JSON: {resp.text[:300]}")
        base = data.get("base_resp") or {}
        if base.get("status_code") not in (0, None):
            raise RuntimeError(f"MiniMax 出错 {base.get('status_code')}: {base.get('status_msg')}")
        audio = ((data.get("data") or {}).get("audio")) or ""
        if not audio:
            raise RuntimeError(f"MiniMax 返回空音频: {json.dumps(data, ensure_ascii=False)[:200]}")
        try:
            blob = bytes.fromhex(audio)
        except ValueError:
            blob = base64.b64decode(audio)
        if not blob:
            raise RuntimeError("MiniMax 音频解码后为空")
        raw.write_bytes(blob)

    async def _tts_doubao(self, text: str, raw: Path) -> None:
        tts = self.config.tts
        is_v1 = (tts.doubao_api or "v3").strip().lower() == "v1"
        if is_v1:
            if not tts.doubao_app_id.strip() or not tts.doubao_token.strip():
                raise RuntimeError("豆包 v1 后端缺少 doubao_app_id / doubao_token")
            await self._tts_doubao_v1(text, raw)
        else:
            # 新版控制台只有 API Key，没有 AppID 这个东西；旧版那套 AppID + Access Token
            # 官方已经说了会下线，所以这里不再兼容，一律走 X-Api-Key。
            if not tts.doubao_token.strip():
                raise RuntimeError("豆包后端缺 API Key：填控制台「API Key 管理」里那串就行，不需要 AppID")
            await self._tts_doubao_v3(text, raw)

    async def _tts_doubao_v3(self, text: str, raw: Path) -> None:
        """火山引擎语音合成 2.0：NDJSON 流式返回，每行 data 是一段 base64 音频。"""
        import base64

        import httpx

        tts = self.config.tts
        url = (tts.doubao_url or "https://openspeech.bytedance.com/api/v3/tts/unidirectional").strip()
        header_map = {
            "X-Api-Key": tts.doubao_token.strip(),
            "X-Api-Resource-Id": (tts.doubao_resource_id or "seed-tts-2.0").strip(),
            "X-Api-Request-Id": uuid.uuid4().hex,
            "Content-Type": "application/json",
        }
        payload = {
            "user": {"uid": "wake-call"},
            "req_params": {
                "text": text,
                "speaker": tts.doubao_voice.strip(),
                "audio_params": {
                    "format": (tts.doubao_format or "mp3").strip().lower(),
                    "sample_rate": int(tts.doubao_sample_rate or 24000),
                    # 接口用百分比整数表示语速偏移：0 = 正常。
                    "speech_rate": int(round((float(tts.doubao_speed or 1.0) - 1.0) * 100)),
                },
            },
        }
        chunks: list[str] = []
        async with httpx.AsyncClient(timeout=tts.timeout) as client:
            async with client.stream("POST", url, json=payload, headers=header_map) as resp:
                if resp.status_code >= 400:
                    body = (await resp.aread()).decode(errors="ignore")
                    raise RuntimeError(f"豆包 HTTP {resp.status_code}: {body[:300]}")
                async for line in resp.aiter_lines():
                    line = line.strip()
                    if not line:
                        continue
                    try:
                        obj = json.loads(line)
                    except json.JSONDecodeError:
                        continue
                    code = obj.get("code")
                    if code not in (0, 20000000, 20000001, None):
                        raise RuntimeError(f"豆包返回错误 {code}: {obj.get('message')}")
                    data = obj.get("data")
                    if isinstance(data, str) and data:
                        chunks.append(data)
        if not chunks:
            raise RuntimeError("豆包没有返回音频数据（检查 speaker / resource_id 是否正确）")
        raw.write_bytes(b"".join(base64.b64decode(part) for part in chunks))

    async def _tts_doubao_v1(self, text: str, raw: Path) -> None:
        """火山引擎经典版 /api/v1/tts：一次性返回 base64 音频。"""
        import base64

        import httpx

        tts = self.config.tts
        url = (tts.doubao_url or "").strip() or "https://openspeech.bytedance.com/api/v1/tts"
        if not tts.doubao_voice.strip():
            raise RuntimeError("豆包 v1 后端缺少 doubao_voice（voice_type）")
        payload = {
            "app": {
                "appid": tts.doubao_app_id.strip(),
                "token": tts.doubao_token.strip(),
                "cluster": (tts.doubao_cluster or "volcano_tts").strip(),
            },
            "user": {"uid": "wake-call"},
            "audio": {
                "voice_type": tts.doubao_voice.strip(),
                "encoding": (tts.doubao_format or "mp3").strip().lower(),
                "speed_ratio": float(tts.doubao_speed or 1.0),
            },
            "request": {
                "reqid": uuid.uuid4().hex,
                "text": text,
                "operation": "query",
            },
        }
        headers = {
            # 注意这里是 "Bearer;" 分号，不是空格，写错会 401。
            "Authorization": f"Bearer;{tts.doubao_token.strip()}",
            "Content-Type": "application/json",
        }
        async with httpx.AsyncClient(timeout=tts.timeout) as client:
            resp = await client.post(url, json=payload, headers=headers)
        if resp.status_code >= 400:
            raise RuntimeError(f"豆包 HTTP {resp.status_code}: {resp.text[:300]}")
        try:
            data = resp.json()
        except Exception:  # noqa: BLE001
            raise RuntimeError(f"豆包返回非 JSON: {resp.text[:300]}")
        # 经典版成功码是 3000，失败时 code=3001/3003 等。
        if int(data.get("code") or 0) not in (3000, 0):
            raise RuntimeError(f"豆包出错 {data.get('code')}: {data.get('message')}")
        audio = data.get("data") or ""
        if not audio:
            raise RuntimeError("豆包返回空音频")
        raw.write_bytes(base64.b64decode(audio))

    async def _silence_wav(self, dst: Path, seconds: int = 120) -> None:
        """造一段纯静音 wav，用作响铃阶段的音源，避免台词在响铃时就播完。"""
        ffmpeg = shutil.which("ffmpeg") or "/usr/bin/ffmpeg"
        if not Path(ffmpeg).exists():
            raise RuntimeError(MISSING_FFMPEG)
        cmd = [
            ffmpeg, "-y", "-loglevel", "error",
            "-f", "lavfi", "-i", "anullsrc=r=8000:cl=mono",
            "-t", str(seconds),
            "-c:a", "pcm_s16le",
            str(dst),
        ]
        proc = await asyncio.create_subprocess_exec(
            *cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE
        )
        _, err = await asyncio.wait_for(proc.communicate(), timeout=60)
        if proc.returncode != 0 or not dst.exists():
            raise RuntimeError(f"生成静音失败: {err.decode(errors='ignore')[:200]}")

    async def _to_wav(
        self, src: Path, dst: Path, seconds: int = 40, loop: bool = True, fmt: str = "wav"
    ) -> None:
        ffmpeg = shutil.which("ffmpeg") or "/usr/bin/ffmpeg"
        if not Path(ffmpeg).exists():
            raise RuntimeError(MISSING_FFMPEG)
        # loop=True 时循环拼接（旧行为）；loop=False 时只说一遍，后面补静音。
        cmd = [
            ffmpeg,
            "-y",
            "-loglevel",
            "error",
        ]
        if loop:
            cmd += ["-stream_loop", "-1"]
        cmd += ["-i", str(src)]
        if not loop:
            cmd += ["-af", "apad"]
        cmd += [
            "-t",
            str(seconds),
            # 必须与下游编码严格一致：G.711(PCMU/PCMA) 是 8000/1 窄带单声道，
            # 音频源也用 8000/1，这样 baresip 不需要 auresamp 重采样（本机无此模块）。
            "-ar",
            "8000",
            "-ac",
            "1",
        ]
        # fmt=mp3 只给侧边栏试听用：8k 采样率已经决定了"电话音"，换成 32kbps mp3
        # 只是把体积压到 1/6，听感不变，base64 塞回前端也不会太大。
        if fmt == "mp3":
            cmd += ["-c:a", "libmp3lame", "-b:a", "32k"]
        else:
            cmd += ["-c:a", "pcm_s16le"]
        cmd.append(str(dst))
        proc = await asyncio.create_subprocess_exec(
            *cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE
        )
        _, err = await asyncio.wait_for(proc.communicate(), timeout=60)
        if proc.returncode != 0 or not dst.exists():
            raise RuntimeError(f"ffmpeg 失败: {err.decode(errors='ignore')[:200]}")

    @staticmethod
    async def _hangup(proc) -> None:
        """让 baresip 自己挂断退出，不听话才 kill。

        直接 SIGKILL 的话 SIP 会话会停在「已接通」状态（没有 BYE），
        手机那头会一直停在通话界面、等它自己的超时。`/hangup` 走正常挂断流程，
        `/quit` 让进程收摊；两条一起写，进程还在就直接退。
        """
        try:
            if proc.returncode is None and proc.stdin is not None:
                proc.stdin.write(b"/hangup\n/quit\n")
                await proc.stdin.drain()
        except (OSError, RuntimeError, AttributeError):
            # 管道已经关了：说明进程自己没了，后面 returncode 判断会兜住。
            pass
        if proc.returncode is None:
            try:
                await asyncio.wait_for(proc.wait(), timeout=1.5)
            except (asyncio.TimeoutError, asyncio.CancelledError):
                pass
        if proc.returncode is None:
            with contextlib.suppress(ProcessLookupError):
                proc.kill()
            try:
                await proc.wait()
            except (Exception, asyncio.CancelledError):
                pass

    # ──── SIP 拨号 ────

    async def _dial(self, wav: Path, ring_seconds: Optional[int] = None) -> str:
        """拨号入口：先看能不能内网直呼，不行/没接通就回退公网账号。"""
        sip = self.config.sip
        lan = None
        if sip.lan_call_enabled:
            lan = await self._lan_callee()
            if lan:
                self.ctx.logger.info("同网段探测到 SIP 对端 %s，走内网直呼（媒体不出局域网）", lan[1])
                self._clear_lan_miss()
            else:
                # 这一行很关键：出问题时看日志立刻能分清「走的内网还是公网」，
                # 不用再猜是内网没找到人、还是内网拨了没接通。
                self.ctx.logger.info("这轮没找到可直呼的内网对端，直接走公网账号")
        reason = await self._dial_once(wav, ring_seconds, lan)
        if reason and lan and sip.lan_fallback_public:
            self.ctx.logger.warning("内网直呼没接通（%s），回退公网账号再拨一次", reason)
            reason = await self._dial_once(wav, ring_seconds, None)
        return reason

    async def _dial_once(
        self,
        wav: Path,
        ring_seconds: Optional[int] = None,
        lan: Optional[tuple[str, str, int, str]] = None,
    ) -> str:
        sip = self.config.sip
        ring_seconds = int(ring_seconds or sip.ring_seconds)
        bin_path = Path(sip.baresip_bin)
        if not bin_path.exists():
            raise RuntimeError(f"找不到 baresip: {bin_path}")
        # lan 有值就走内网地址，否则用公网账号里的被叫 URI。
        callee = lan[0] if lan else sip.callee_aor.strip()
        if not callee:
            raise RuntimeError("未配置被叫账号")
        # /dial 是写给 baresip stdin 的命令行，换行等于多塞一条命令进去。
        if any(ch in callee for ch in "\r\n"):
            raise RuntimeError("被叫账号里有换行符，baresip 会把它当成两条命令，请删掉")

        silence = wav.parent / "silence.wav"
        if not silence.exists():
            await self._silence_wav(silence, seconds=PLAY_SECONDS + 60)

        confdir = Path(tempfile.mkdtemp(prefix="wakecall-sip-"))
        # accounts 里是明文密码。默认权限跟 umask 走，同机其他用户能读到；
        # 正常情况下收摊会 rmtree，但被 SIGKILL（OOM 最常见）时 finally 不执行，
        # 目录会留在 /tmp 里。所以这里把权限收到最紧，on_load 再扫一遍残留。
        with contextlib.suppress(OSError):
            os.chmod(confdir, 0o700)
        # 报文先在内存里攒着，收摊时落盘；即使中途被取消也能留下证据。
        chunks: list[str] = []
        dial_log = self._dial_log_path()
        self._last_dial_log = dial_log
        try:
            module_path = self._resolve_module_path()
            lines = [
                "sip_listen 0.0.0.0:0",
                # 收到的音频直接丢弃：不能写回正在播放的那个 wav，否则会互相踩踏。
                "audio_player aufile,/dev/null",
                # 响铃阶段给静音，接通后再用 /ausrc 换成台词（见 _pump）。
                f"audio_source aufile,{silence}",
                f"audio_alert aufile,{silence}",
                f"module_path {module_path}",
                "module stdio.so",
                "module aufile.so",
                # 只用 G.711(PCMU)。Linphone 对 PCMU 是原生支持，
                # 实测只提供 Opus 时它会直接回 488 Not acceptable here。
                "module g711.so",
                "module account.so",
                "module menu.so",
                "",
            ]
            (confdir / "config").write_text("\n".join(lines), encoding="utf-8")

            aor = sip.caller_aor.strip()
            user = sip.caller_user.strip() or self._user_from_aor(aor)
            # accounts 是一行一个账号、分号分隔参数：值里混进 ; 或换行，
            # 等于让「账号名」去改写 auth_pass / outbound 这些参数。
            self._check_sip_param("主叫用户名", user)
            self._check_sip_param("主叫密码", sip.caller_pass)
            if any(ch in aor for ch in '<>"\r\n'):
                raise RuntimeError('主叫账号里不能出现 < > " 这三个字符')
            params = [
                f"auth_user={user}",
                f"auth_pass={sip.caller_pass}",
                # 必须写在账号行里！写在全局 config 里 baresip 1.0.0 完全不认，
                # 仍会同时提供 PCMU/PCMA，手机会去挑 PCMA，而 PCMA 在这条链路上零字节。
                # 固定单编码：两端都只会用这一个，省掉协商出意外的机会。
                "audio_codecs=pcmu/8000/1",
            ]
            # Linphone 的出局代理就是账号域名本身，显式写出来免得多走一次 DNS 解析。
            if lan:
                # 直呼模式绝不能写 outbound：它会把该账号的所有请求强制塞给服务器，
                # 内网 INVITE 也跟着绕出去，等于白做。
                # regint=0 关掉注册——内网直呼不需要注册，也免得对着解析不出的
                # sip2sip.info 反复重试，把日志刷满、还拖慢拨号。
                accounts = f"<sip:{user}@{lan[3]}:5060>;regint=0;{';'.join(params)}\n"
            else:
                # 端口和传输层都由 _sip_outbound() 统一拼，不再写死 :5060
                outbound = self._sip_outbound()
                if outbound:
                    params.append(f'outbound="{outbound}"')
                accounts = f"<{aor}>;{';'.join(params)}\n"
            (confdir / "accounts").write_text(accounts, encoding="utf-8")
            with contextlib.suppress(OSError):
                os.chmod(confdir / "accounts", 0o600)
            with contextlib.suppress(OSError):
                os.chmod(confdir / "config", 0o600)

            # 不能启动即拨：注册耗时可能长达 40 秒，抢跑会被服务器回 407 直接拒掉。
            #
            # 必须经 sh 中转一次，不是为了别的，只为了把 timerslack 压下来。
            # Android 给后台进程的默认 timer slack 是 40ms（实测 /proc/self/timerslack_ns
            # = 40000000），baresip 靠 20ms 定时器喂音频帧，被松弛一推就变成 40~60ms 一帧：
            # 20ms 的 sleep 实测睡 59.5ms，等于每秒只发出 4000 个采样（PCMU 应为 8000），
            # 听感就是声音发闷、卡顿、像被拉长。改成 1µs 后 sleep(20ms) 实测 20.1ms。
            # exec 之后该属性跟着进程走，所以 sh 只做「写文件 + exec」这一件事。
            proc = await asyncio.create_subprocess_exec(
                "sh",
                "-c",
                'echo 1000 > /proc/self/timerslack_ns 2>/dev/null; exec "$@"',
                "wakecall",  # $0，占位用
                str(bin_path),
                "-f",
                str(confdir),
                # -s 打开 SIP 报文跟踪：不打开的话失败后只能看到一句「180 Ringing」，
                # 压根分不清是没注册上、没送达、还是媒体没协商通。
                "-s",
                stdin=asyncio.subprocess.PIPE,
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.STDOUT,
                cwd=str(confdir),
            )

            dialed = False
            answered = False
            closed = False

            async def _pump() -> None:
                nonlocal dialed, answered, closed
                assert proc.stdout is not None
                while True:
                    line = await proc.stdout.readline()
                    if not line:
                        break
                    text = line.decode(errors="ignore")
                    chunks.append(text)
                    low = text.lower()
                    if not dialed and ("registered successfully" in low or "Registration successful" in text):
                        dialed = True
                        # 留半秒让注册事务彻底落定，再发 INVITE。
                        await asyncio.sleep(0.5)
                        try:
                            assert proc.stdin is not None
                            proc.stdin.write(f"/dial {callee}\n".encode())
                            await proc.stdin.drain()
                        except Exception:  # noqa: BLE001 - 管道已关就只有这一种可能
                            dialed = False
                    elif dialed and not answered and "call established" in low:
                        answered = True
                        # 接通这一刻才把音源切到台词：响铃时一个字都不放，
                        # 接起来才从头开始说，而且只说一遍。
                        await asyncio.sleep(0.3)
                        try:
                            assert proc.stdin is not None
                            proc.stdin.write(f"/ausrc aufile,{wav}\n".encode())
                            await proc.stdin.drain()
                        except Exception:  # noqa: BLE001
                            pass
                    elif answered and not closed and ("call closed" in low or "call: closed" in low):
                        # 对端先挂了：不用再傻等到台词时长结束。
                        closed = True

            pump = asyncio.create_task(_pump())

            async def _direct_dial() -> None:
                """内网直呼没有注册事务可等，进程起来就能发 INVITE。

                给 1.2 秒是让 baresip 把 SIP socket 和 RTP 端口绑好——太早写进去
                会被 menu 模块当成「还没起好」的输入丢掉。
                """
                nonlocal dialed
                await asyncio.sleep(1.2)
                try:
                    assert proc.stdin is not None
                    proc.stdin.write(f"/dial {callee}\n".encode())
                    await proc.stdin.drain()
                    dialed = True
                except Exception:  # noqa: BLE001
                    pass

            direct = asyncio.create_task(_direct_dial()) if lan else None
            try:
                # 先给注册留出时间（最多 REG_WAIT 秒），拨出后再按通话时长计时。
                wait_deadline = time.monotonic() + REG_WAIT
                while not dialed and time.monotonic() < wait_deadline:
                    if proc.returncode is not None:
                        break
                    await asyncio.sleep(0.2)
                if dialed:
                    # 响铃阶段等到接听为止（最多 ring_seconds）；接通后再按播放时长续时。
                    ring_deadline = time.monotonic() + ring_seconds
                    while proc.returncode is None and time.monotonic() < ring_deadline:
                        if answered:
                            break
                        await asyncio.sleep(0.2)
                    if answered:
                        # baresip 是常驻 UA：对端挂了、台词播完了，它也不会自己退出。
                        # 以前这里死等 proc.wait()，只会满 70 秒再被 SIGKILL ——
                        # 那一下是硬杀，连 BYE 都发不出去，手机那头会一直停在通话界面。
                        # 现在按「台词时长」计时到点就主动挂断，让对端收到正常的 BYE。
                        play_deadline = time.monotonic() + PLAY_SECONDS
                        while proc.returncode is None and time.monotonic() < play_deadline:
                            if closed:
                                break
                            await asyncio.sleep(0.2)
                    else:
                        raise asyncio.TimeoutError
                else:
                    await asyncio.wait_for(proc.wait(), timeout=5)
            except asyncio.TimeoutError:
                # 没人接 / 时长到了：也要走优雅挂断，见 _hangup。
                await self._hangup(proc)
            finally:
                if direct:
                    direct.cancel()
                    with contextlib.suppress(asyncio.CancelledError, Exception):
                        await direct
                pump.cancel()
                with contextlib.suppress(asyncio.CancelledError, Exception):
                    await pump
                # 兜底收摊：被取消（通话中点了保存 / 卸载插件）或抛异常时，
                # 上面那个 TimeoutError 分支根本不会执行，baresip 就变成孤儿进程——
                # 那通电话不会挂断、一直占着 SIP 会话，下次再拨就是两通同时在响。
                if proc.returncode is None:
                    await self._hangup(proc)

            log = "".join(chunks)
            low = log.lower()
            ordered = _sip_code_list(log)
            # 只看这通呼叫的状态序列：REGISTER 阶段的 401、INVITE 的 407 挑战都是
            # 正常鉴权握手，不能当故障。真正的结论在最后一条 INVITE 之后的响应里。
            call_trace = log[log.rfind("INVITE sip:"):] if "INVITE sip:" in log else ""
            call_codes = _sip_code_list(call_trace)
            final = call_codes[-1] if call_codes else ""
            invite_final = _sip_invite_final(call_trace)

            if "established" in low or invite_final.startswith("2"):
                reason = ""
            elif "180" in call_codes or "ringing" in low:
                # 180 只说明呼叫到了对方终端并开始振铃，不代表接起来有声音。
                reason = "手机响了但没人接（180 Ringing）"
            elif has_any(ordered, "110") or "push sent" in low:
                reason = "服务器把呼叫转成了推送唤醒（110 Push sent），手机没醒过来"
            elif final == "404" or "not found" in low:
                reason = "对端账号不存在（404）"
            elif final == "403" or "forbidden" in low:
                reason = "认证被拒（403），检查密码"
            elif final in {"401", "407"}:
                # 只有最终响应就是挑战、之后没有任何后续，才算凭据真有问题。
                reason = f"需要认证但凭据无效（{final}），这通呼叫被挡在鉴权这一步"
            elif final == "486" or "busy" in low:
                reason = "对方忙（486）"
            elif final in {"408", "480", "487", "500", "503"}:
                reason = f"服务器回了 {final}，呼叫没送达被叫"
            elif "registration" in low and "failed" in low:
                reason = (
                    "主叫 SIP 账号注册失败：先查密码，再确认没在别处用同一个账号登录"
                    "（同一账号多处登录会互相踢下线）"
                )
            elif not dialed:
                if lan:
                    reason = "内网直呼的 INVITE 没能发出去（对端可能在 5060 上只收 TCP）"
                elif "registered successfully" not in low:
                    reason = (
                        f"主叫 SIP 账号 {REG_WAIT} 秒内没注册上："
                        "多半是 UDP 5060 出不去，或账号密码不对"
                    )
                else:
                    reason = "注册成功但拨号命令没能发出"
            # 只有 100 Trying 之后一路静默：服务器接受了呼叫并转了出去，但对端一个字节都没回。
            # 这几乎一定是被叫客户端没在真实接收（账号没登录 / 进程被系统冻结 / 连接已死）。
            elif call_codes or "trying" in low:
                reason = "服务器已转接，但手机端没有任何应答（Linphone 未在线接收）"
            else:
                reason = "未接通（无 established）"

            digest = _dial_digest(log)
            seq = "→".join(ordered[-8:]) or "无"
            if reason:
                self.ctx.logger.warning(
                    "拨号失败: %s ｜ 状态序列 %s ｜ %s ｜ 完整报文: %s",
                    reason,
                    seq,
                    digest or "(无关键行)",
                    dial_log,
                )
            else:
                self.ctx.logger.info(
                    "拨号接通 ｜ 状态序列 %s ｜ %s ｜ 完整报文: %s", seq, digest or "(无关键行)", dial_log
                )
            return reason
        finally:
            if chunks:
                self._write_dial_log(dial_log, chunks)
            shutil.rmtree(confdir, ignore_errors=True)

    @staticmethod
    def _check_sip_param(label: str, value: str) -> None:
        """baresip 的 accounts 文件用 ; 分隔参数、用换行分隔账号。

        值里混进这些字符，轻则认证永远失败（报 403，查半天），
        重则改写同一行里的 outbound / regint。这里提前拦住并把原因说清楚。
        """
        bad = [ch for ch in ';"\r\n' if ch in (value or "")]
        if bad:
            shown = "、".join({"\r": "回车", "\n": "换行", ";": "分号", '"': "引号"}[c] for c in bad)
            raise RuntimeError(f"{label}里含 baresip 不接受的字符（{shown}），请改掉再拨")

    @staticmethod
    def _user_from_aor(aor: str) -> str:
        match = re.search(r"sip:([^@]+)@", aor or "")
        return match.group(1) if match else ""

    @staticmethod
    def _host_from_aor(aor: str) -> str:
        """从 sip:user@host[:port] 里取 host[:port]，去掉 ;参数 和 > 结尾。

        端口必须留着：用户在主叫账号里写 :5070 就是在说服务器在 5070。
        以前这里统一截断、再由调用方补 :5060，等于把用户写的端口悄悄吃掉了，
        自建私有 SIP 改过端口的用户会一直连不上，还查不出原因。
        """
        match = re.search(r"sip:[^@]+@([^;>\s]+)", aor or "")
        return match.group(1) if match else ""

    def _sip_server(self) -> str:
        """实际要用的服务器：显式配置优先，留空则回落到主叫域名。

        sip2sip 属于「账号域名 ≠ 代理域名」的那种：sip2sip.info 的 SRV 是 .（服务不可用）、
        两个 A 记录也都不通，只有 proxy.sipthor.net 能用，所以这里必须允许覆盖。
        """
        explicit = self.config.sip.server.strip()
        if explicit:
            return explicit
        return self._host_from_aor(self.config.sip.caller_aor.strip())

    @staticmethod
    def _split_host_port(value: str) -> tuple[str, int]:
        """把 host[:port] 拆成 (host, port)，支持 [IPv6]:port；没写端口返回 0。

        server 允许用户自己带端口（自建 SIP 常改成 5080 之类），
        这一步是「不要再无脑补 :5060」的前提。
        """
        text = (value or "").strip()
        if not text:
            return "", 0
        if text.startswith("["):
            end = text.find("]")
            if end < 0:
                return "", 0
            host = text[1:end]
            rest = text[end + 1 :]
            # 方括号要留着：SIP URI 里的 IPv6 字面量必须写成 [addr]
            return f"[{host}]", _as_port(rest[1:]) if rest.startswith(":") else 0
        colons = text.count(":")
        if colons == 0:
            return text, 0
        if colons == 1:
            host, _, port = text.partition(":")
            return host.strip(), _as_port(port)
        # 多个冒号且没有方括号：当裸 IPv6 看，补上方括号，没有端口
        return f"[{text}]", 0

    def _sip_outbound(self) -> str:
        """baresip accounts 行里的 outbound 值，形如 sip:1.2.3.4:5080;transport=tcp。

        以前这里写死 `sip:{server}:5060`，云服务器用户把 server 填成 1.2.3.4:5080
        就会拼出 `sip:1.2.3.4:5080:5060` 这种非法 URI，baresip 直接不认。
        现在：端口按用户写的来，没写才补 5060；transport 只在明确填了 udp/tcp 时才加。
        """
        server = self._sip_server()
        if not server:
            return ""
        host, port = self._split_host_port(server)
        if not host:
            return ""
        # host 要拼进带引号的参数里，混进引号或分号就能改写整行 accounts
        if any(ch in host for ch in ';"<>\r\n '):
            raise RuntimeError(f"SIP 服务器地址「{server}」里有非法字符，请只填 host 或 host:port")
        uri = f"sip:{host}:{port or 5060}"
        transport = (self.config.sip.transport or "").strip().lower()
        if transport in ("udp", "tcp"):
            uri += f";transport={transport}"
        return uri

    def _safe_outbound(self) -> str:
        """给状态接口用的版本：配置写坏了也不能让整个侧边栏读不出来。"""
        try:
            return self._sip_outbound()
        except Exception:  # noqa: BLE001 - 诊断字段，失败就空着
            return ""

    def _resolve_module_path(self) -> Path:
        """baresip 模块目录：配置的优先，不存在就按常见发行版路径试一遍。

        云端用户第一次部署最容易踩的就是这个：Ubuntu 装在
        /usr/lib/x86_64-linux-gnu/baresip/modules、源码编译在 /usr/local/lib/...，
        默认值 /usr/lib/baresip/modules 一填就 module 全加载失败，
        报错还只写「module not found」，根本看不出是路径问题。
        """
        configured = Path(self.config.sip.module_path)
        if configured.is_dir():
            return configured
        candidates = (
            "/usr/lib/baresip/modules",
            "/usr/lib/x86_64-linux-gnu/baresip/modules",
            "/usr/lib/aarch64-linux-gnu/baresip/modules",
            "/usr/lib/arm-linux-gnueabihf/baresip/modules",
            "/usr/local/lib/baresip/modules",
            "/usr/lib64/baresip/modules",
            "/opt/homebrew/lib/baresip/modules",
        )
        for cand in candidates:
            if cand != str(configured) and Path(cand).is_dir():
                self.ctx.logger.info(
                    "配置的 baresip 模块目录 %s 不存在，自动改用 %s", configured, cand
                )
                return Path(cand)
        return configured

    # ──── 内网直呼 ────

    def _local_ipv4(self) -> str:
        """本机在局域网里的 IPv4。

        先读接口表挑 WLAN 那个地址，读不到才用 UDP connect 兜底。
        为什么不能只用 UDP connect：手机同时插卡又连 WiFi 时，只要 WiFi 那一刻没有
        默认路由（校园网未认证就是这样），内核会把「连 223.5.5.5」的包交给移动数据，
        拿到的是运营商内网 10.x —— 拿它去算 /20 网段，永远扫不到同一 WiFi 里的对端。
        """
        now = time.monotonic()
        cached = str(_LOCAL_IP_CACHE.get("ip") or "")
        # 有地址就缓存 10 秒；没地址只缓存 1 秒，网络刚起来时别卡太久。
        ttl = LOCAL_NET_TTL if cached else 1.0
        if now - float(_LOCAL_IP_CACHE.get("ts") or 0) < ttl:
            return cached

        wlan = self._wlan_ipv4()
        if wlan:
            _LOCAL_IP_CACHE.update(ip=wlan, ts=now)
            return wlan

        import socket as _socket

        for probe in ("223.5.5.5", "114.114.114.114"):
            try:
                with _socket.socket(_socket.AF_INET, _socket.SOCK_DGRAM) as sock:
                    sock.settimeout(0.4)
                    sock.connect((probe, 53))
                    ip = sock.getsockname()[0]
                if ip and not ip.startswith("127."):
                    _LOCAL_IP_CACHE.update(ip=ip, ts=now)
                    return ip
            except OSError:
                continue
        _LOCAL_IP_CACHE.update(ip="", ts=now)
        return ""

    @staticmethod
    def _wlan_ipv4() -> str:
        """从 `ip addr` 里挑出 WLAN 接口的地址；没有 WLAN 就挑第一个非虚拟接口。"""
        try:
            out = subprocess.run(
                ["ip", "-4", "-o", "addr", "show"],
                capture_output=True,
                text=True,
                timeout=3,
            ).stdout
        except (OSError, subprocess.SubprocessError):
            return ""
        fallback = ""
        for line in out.splitlines():
            match = re.match(r"\d+:\s+(\S+?)(?:@\S+)?\s+inet\s+(\d{1,3}(?:\.\d{1,3}){3})/", line)
            if not match:
                continue
            name, ip = match.group(1).lower(), match.group(2)
            if name == "lo" or ip.startswith("127."):
                continue
            # 移动数据 / 隧道 / 热点桥接这类接口不是「这张局域网」的地址。
            if name.startswith(("rmnet", "ccmni", "clat", "tun", "dummy", "p2p", "sit")):
                continue
            if name.startswith(("wlan", "wl", "swlan", "ap")):
                return ip
            if not fallback:
                fallback = ip
        return fallback

    @staticmethod
    def _options_payload(host: str, port: int, local_ip: str, branch: str) -> bytes:
        """拼一条 OPTIONS。整段扫描要发几千条，所以单独抽出来复用。"""
        return (
            f"OPTIONS sip:{host} SIP/2.0\r\n"
            f"Via: SIP/2.0/UDP {local_ip}:5062;branch=z9hG4bK{branch};rport\r\n"
            "Max-Forwards: 70\r\n"
            f"From: <sip:probe@{local_ip}>;tag={branch}\r\n"
            f"To: <sip:{host}>\r\n"
            f"Call-ID: {branch}@{local_ip}\r\n"
            "CSeq: 1 OPTIONS\r\n"
            f"Contact: <sip:probe@{local_ip}:5062>\r\n"
            "User-Agent: MaiBot-wake-call-probe\r\n"
            "Content-Length: 0\r\n\r\n"
        ).encode()

    def _sip_options_probe(self, host: str, port: int, timeout: float, local_ip: str) -> str:
        """发一条 SIP OPTIONS，返回对端的状态行；没人应答返回空串。

        为什么用 OPTIONS 而不是直接拨：OPTIONS 不建立会话、不响铃、对端也不会记账，
        纯粹问一句「你在这儿吗」。Linphone / FreeSWITCH / 各种 SBC 都会回 200 或 401，
        这两种都证明 5060 上真有一个 SIP 栈在听。

        必须校验应答以 `SIP/2.0` 开头：同一端口上可能坐着完全不相干的 UDP 服务，
        随意回一个包就会被当成「找到对端」，接着把电话拨到一台无关设备上。
        """
        import socket as _socket

        branch = uuid.uuid4().hex[:12]
        payload = self._options_payload(host, port, local_ip, branch)
        try:
            with _socket.socket(_socket.AF_INET, _socket.SOCK_DGRAM) as sock:
                sock.settimeout(timeout)
                sock.sendto(payload, (host, port))
                data, _ = sock.recvfrom(2048)
            if not data.startswith(b"SIP/2.0"):
                return ""
            return data.decode("utf-8", "replace").split("\r\n", 1)[0]
        except OSError:
            return ""

    def _scan_subnet(self, prefix: str, local_ip: str, timeout: float) -> list[tuple[str, str]]:
        """并发扫 /24 的 5060，返回 [(ip, 状态行)]。

        只在用户开了内网直呼时才跑，且结果缓存 10 分钟；254 个 UDP 包一起发，
        实测 1.5 秒内全部回来。绝不做 /16 那种全网段扫描。
        """
        import socket as _socket
        from concurrent.futures import ThreadPoolExecutor

        targets = [f"{prefix}{i}" for i in range(1, 255) if f"{prefix}{i}" != local_ip]

        def _one(ip: str) -> tuple[str, str]:
            return ip, self._sip_options_probe(ip, 5060, timeout, local_ip)

        with ThreadPoolExecutor(max_workers=64) as pool:
            results = list(pool.map(_one, targets))
        return [item for item in results if item[1]]

    def _port_range(self) -> tuple[int, int]:
        """本机内核给 bind(0) 分配的临时端口段——对端 Linphone 的 SIP 端口就落在这里。"""
        try:
            raw = Path("/proc/sys/net/ipv4/ip_local_port_range").read_text().split()
            low, high = int(raw[0]), int(raw[1])
            if 1024 <= low < high <= 65535:
                return low, high
        except (OSError, ValueError, IndexError):
            pass
        return 32768, 60999

    def _default_gateway(self) -> str:
        """找默认网关。开热点的手机通常就是网关，端口缓存丢了可以拿它当扫描起点。

        实测 proot 里 /proc/net/route 是 Permission denied（Android 限制），
        所以还要退回 `ip route show table all` 和 resolv.conf 两条路——
        前者能读到 table 1040 里的 default via，后者 DHCP 下发的 DNS 一般就是网关。
        """
        try:
            for line in Path("/proc/net/route").read_text().splitlines()[1:]:
                fields = line.split()
                if len(fields) > 2 and fields[1] == "00000000":
                    raw = int(fields[2], 16)
                    return ".".join(str((raw >> (8 * (3 - i))) & 0xFF) for i in range(4))
        except (OSError, ValueError, IndexError):
            pass

        import subprocess

        try:
            out = subprocess.run(
                ["ip", "route", "show", "table", "all"],
                capture_output=True,
                text=True,
                timeout=3,
            ).stdout
            for line in out.splitlines():
                parts = line.split()
                # 只要带 via 的（"default dev dummy0" 这种不算）
                if len(parts) >= 3 and parts[0] == "default" and parts[1] == "via":
                    if re.fullmatch(r"\d{1,3}(?:\.\d{1,3}){3}", parts[2]):
                        return parts[2]
        except (OSError, subprocess.SubprocessError):
            pass

        try:
            for line in Path("/etc/resolv.conf").read_text().splitlines():
                parts = line.split()
                if len(parts) >= 2 and parts[0] == "nameserver":
                    cand = parts[1]
                    if re.fullmatch(r"\d{1,3}(?:\.\d{1,3}){3}", cand) and not cand.startswith("127."):
                        return cand
        except OSError:
            pass
        return ""

    def _lan_scan_allowed(self) -> bool:
        """扫一次要给对端发两万多个包，失败后冷却 10 分钟，别每通电话都来一遍。"""
        last_fail = float(self._state.get("lan_scan_fail_ts") or 0)
        return time.time() - last_fail > LAN_SCAN_COOLDOWN

    def _scan_lan_sip_port(self, host: str, local_ip: str) -> Optional[int]:
        """扫临时端口段，找出哪个端口上有 SIP 栈在应答。

        为什么需要这一步：Linphone 的 SIP 端口由内核随机分配（实测 52038），
        这一版 App 的 UI 里又把固定端口的开关删掉了，所以缓存里的端口一旦失效
        （App 重启 / 换 WiFi / 手机重启），只能靠这趟扫描把它找回来。

        只发 OPTIONS：不响铃、不建会话、对端不记账。边发边收，命中就停，
        实测 800pps 下 11 秒左右命中。

        两个踩过的坑（都实测复现过，别改回去）：
        1. Via / Contact 里必须写「真正发这个包的那个 socket」的端口。之前用另一个
           临时 socket 探端口后关掉，对端把 200 OK 回给那个已释放的端口，永远收不到。
        2. sendto 打到未监听端口时，Linux 会把上一次的 ICMP ECONNREFUSED 报给下一次
           调用。捕获后必须 continue 而不是 break，否则整批只发几个包就停了。
        """
        import socket as _socket

        low, high = self._port_range()
        tag = uuid.uuid4().hex[:6]

        sock = _socket.socket(_socket.AF_INET, _socket.SOCK_DGRAM)
        try:
            sock.setsockopt(_socket.SOL_SOCKET, _socket.SO_RCVBUF, 4 << 20)
            sock.bind(("0.0.0.0", 0))
            src_port = sock.getsockname()[1]

            def payload(port: int) -> bytes:
                return (
                    f"OPTIONS sip:{host}:{port} SIP/2.0\r\n"
                    f"Via: SIP/2.0/UDP {local_ip}:{src_port};branch=z9hG4bK{tag}{port}\r\n"
                    "Max-Forwards: 70\r\n"
                    f"From: <sip:probe@{local_ip}>;tag={port}\r\n"
                    f"To: <sip:{host}:{port}>\r\n"
                    f"Call-ID: scan{tag}-{port}@probe\r\n"
                    "CSeq: 1 OPTIONS\r\n"
                    f"Contact: <sip:probe@{local_ip}:{src_port}>\r\n"
                    "User-Agent: MaiBot-wake-call-scan\r\n"
                    "Content-Length: 0\r\n\r\n"
                ).encode()

            sock.setblocking(False)

            def harvest() -> Optional[int]:
                """把已经回来的应答读干净，认出端口号就返回。"""
                while True:
                    try:
                        data, _ = sock.recvfrom(4096)
                    except (BlockingIOError, InterruptedError):
                        return None
                    except OSError:
                        return None
                    text = data.decode("utf-8", "replace")
                    if not text.startswith("SIP/2.0") or tag not in text:
                        continue
                    for line in text.split("\r\n"):
                        if line.lower().startswith("call-id:"):
                            tail = line.split(":", 1)[1].strip()
                            tail = tail.split(f"scan{tag}-", 1)[-1].split("@", 1)[0]
                            if tail.isdigit():
                                return int(tail)

            budget_end = time.monotonic() + LAN_SCAN_BUDGET
            # 每批 80 个、间隔 20ms。实测这个节奏下对端不会积压，
            # 发太快（每秒几千个）会把 Linphone 的接收队列顶满，反而扫不到。
            batch = 80
            fails = 0
            for start in range(low, high + 1, batch):
                if time.monotonic() > budget_end:
                    break
                for port in range(start, min(start + batch, high + 1)):
                    try:
                        sock.sendto(payload(port), (host, port))
                        fails = 0
                    except OSError:
                        # 未监听端口回的 ICMP 会被内核挂到下一次 sendto 上，跳过继续。
                        fails += 1
                        if fails > 50:
                            break
                hit = harvest()
                if hit:
                    return hit
                time.sleep(0.02)
            # 发完了再给反应慢一点的对端留一点时间
            tail_end = time.monotonic() + max(1.5, float(self.config.sip.lan_probe_timeout))
            while time.monotonic() < tail_end:
                hit = harvest()
                if hit:
                    return hit
                time.sleep(0.02)
            return None
        finally:
            sock.close()

    async def _lan_callee(self) -> Optional[tuple[str, str, int, str]]:
        """找出可以内网直呼的对端，返回 (拨号 URI, host, port, 本机 IP)。

        分层，从最便宜的开始（端口每次 App 启动都会变，IP 在同一张网络里很稳）：
          L1 探缓存 —— 1 个包；
          L2 对同一台主机重扫端口段 —— 端口变了、IP 没变（最常见）；
          L3 扫网关端口段 —— 对方开热点时它就是网关；
          L4 手填了 IP 就扫那台 —— 写 IP 就行，端口不用填；
          L5 扫同网段 5060 —— 对方把端口固定过的情况。
        「ping 扫活跃主机」那一层太慢（几十秒），只在后台预热里跑，拨号现场不做。
        找不到就返回 None，调用方照常走公网账号。
        """
        sip = self.config.sip
        local_ip = await asyncio.to_thread(self._local_ipv4)
        if not local_ip:
            self._note_lan_miss("", "读不到本机局域网 IP")
            return None
        callee_user = self._user_from_aor(sip.callee_aor.strip())

        def uri_for(h: str, p: int) -> str:
            return f"sip:{callee_user}@{h}:{p}" if callee_user else f"sip:{h}:{p}"

        def miss(reason: str) -> None:
            """记录这次为什么没找到，然后照常返回 None 走公网。"""
            self._note_lan_miss(local_ip, reason)
            return None

        cached = self._cache_get(local_ip)
        host = str(cached.get("host") or "")
        port = int(cached.get("port") or 0)

        # L1：一个包就能确认缓存还活着
        host_up = True
        if host and port:
            alive = await asyncio.to_thread(
                self._sip_options_probe, host, port, sip.lan_probe_timeout, local_ip
            )
            if alive:
                return uri_for(host, port), host, port, local_ip
            # 先看这台机器还在不在：DHCP 换过地址时旧 IP 可能已经没人了，
            # 那时去扫它两万多个端口要白等 20 秒（实测），不如直接整段找旧端口。
            host_up = await asyncio.to_thread(self._tcp_alive, host)
            if host_up:
                self.ctx.logger.info("L1 缓存的对端 %s:%s 不应答，按同一台主机重扫端口段", host, port)
            else:
                self.ctx.logger.info("L1 的 %s 已经不在这张网里（TCP 无回包），跳过端口段扫描", host)

        # L2：端口每次 App 启动都会变，但 IP 在同一张网络里很稳 → 只重扫这一台
        if host and host_up and self._reheal_allowed():
            self.ctx.logger.info("L2 对 %s 重扫临时端口段找 SIP 端口（不响铃）", host)
            found = await asyncio.to_thread(self._scan_lan_sip_port, host, local_ip)
            if found:
                self._cache_put(local_ip, host, found, "scan")
                self.ctx.logger.info("L2 命中 %s:%s，已写入缓存", host, found)
                return uri_for(host, found), host, found, local_ip
            self._state["lan_reheal_ts"] = time.time()
            if str(cached.get("source") or "") == "reuse":
                # 这是从别的 /24 借来的地址，扫不到就说明它确实不在这张网里
                self._note_reuse_fail(local_ip)
            self._save_state()
            self.ctx.logger.info("L2 没扫到，这台地址可能已经换人，交给后台预热继续找")

        # L4：手填目标。只写 IP 也行，端口留空由这里扫出来。
        # 这一段必须排在整段补救之前：用户亲手写了地址，就是最确定的信息来源，
        # 不该让「拿旧端口扫四千个地址」抢在它前面白等几秒。
        explicit = sip.lan_target.strip()
        if explicit:
            ehost, _, raw_port = explicit.partition(":")
            ehost = ehost.strip()
            if raw_port.isdigit():
                eport = int(raw_port)
                status = await asyncio.to_thread(
                    self._sip_options_probe, ehost, eport, sip.lan_probe_timeout, local_ip
                )
                if not status:
                    self.ctx.logger.info("内网直呼目标 %s:%s 没应答，改走公网账号", ehost, eport)
                    return miss(f"手填的目标 {ehost}:{eport} 没应答")
                return uri_for(ehost, eport), ehost, eport, local_ip
            if ehost and self._lan_scan_allowed():
                self.ctx.logger.info("内网直呼目标 %s 没写端口，直接扫它的临时端口段", ehost)
                found = await asyncio.to_thread(self._scan_lan_sip_port, ehost, local_ip)
                if found:
                    self._cache_put(local_ip, ehost, found, "manual")
                    self.ctx.logger.info("手填的 %s 扫到端口 %s，已写入缓存", ehost, found)
                    return uri_for(ehost, found), ehost, found, local_ip
                self.ctx.logger.info("手填的 %s 没扫到 SIP 应答，改走公网账号", ehost)
                return miss(f"手填的 {ehost} 扫不到 SIP 应答")

        # L2.5：IP 换了、端口没变 —— 拿记住的端口扫本机整段。
        # 这是校园网/DHCP 最真实的情况：对方的 App 一直挂着（端口保留），
        # 但手机重连一次 WiFi 就换了个 /24 的地址。只扫一个端口，几秒钟的事。
        # 放在手填之后：手填是明确意图，整段扫描是猜测，猜测不该比明确意图先跑。
        # 拨号现场用 60 秒的短冷却，不继承预热循环的退避——见 _dial_subnet_allowed。
        known_port = port or self._last_known_port()
        # 这一层有没有真的扫过整段，决定最后给用户的提示是「扫了没找到」
        # 还是「按规则没扫」——两者该采取的动作完全不同。
        deep_scanned = False
        # 是「扫了没人」还是「被冷却挡着没扫」，给用户的结论完全不同。
        blocked_by_cooldown = False
        if known_port and sip.lan_subnet_scan and self._dial_subnet_allowed():
            self.ctx.logger.info(
                "L2.5 拿旧端口 %s 扫本机 /%d 找对端（IP 变了、App 没重启时会命中）",
                known_port,
                self._subnet_prefix(),
            )
            deep_scanned = True
            moved = await asyncio.to_thread(self._scan_subnet_for_port, local_ip, known_port)
            self._state["lan_subnet_scan_ts"] = time.time()
            self._save_state()
            if moved:
                self._cache_put(local_ip, moved, known_port, "subnet")
                self.ctx.logger.info("L2.5 命中 %s:%s，已写入缓存", moved, known_port)
                return uri_for(moved, known_port), moved, known_port, local_ip
            self.ctx.logger.info("L2.5 整段没找到（对端可能也重开了 App，换了端口）")
        elif known_port and sip.lan_subnet_scan:
            # 不再静默跳过：否则用户只看到「没找到」，会以为是没扫到人。
            blocked_by_cooldown = True
            self.ctx.logger.info(
                "L2.5 距上次扫描不足 %d 秒，这次不重扫", int(DIAL_SUBNET_COOLDOWN)
            )

        # L3：对方开热点时它就是网关。除了「这张网络还没缓存要试一次」，
        #     缓存主机不应答时也要试——同网段里 DHCP 换了 IP，旧 host 会一直探不通，
        #     只扫那一台就永远找不到人。手填了目标就不再猜网关（用户已经指了具体机器）。
        if not explicit and self._lan_scan_allowed() and not self._is_public_net(local_ip):
            gateway = await asyncio.to_thread(self._default_gateway)
            if gateway and gateway != host:
                self.ctx.logger.info("L3 这张网络还没有缓存，先扫网关 %s 的临时端口段（不响铃）", gateway)
                found = await asyncio.to_thread(self._scan_lan_sip_port, gateway, local_ip)
                if found:
                    self._cache_put(local_ip, gateway, found, "scan")
                    self.ctx.logger.info("L3 命中网关 %s:%s，已写入缓存", gateway, found)
                    return uri_for(gateway, found), gateway, found, local_ip
            self._state["lan_scan_fail_ts"] = time.time()
            self._save_state()

        # L5：同网段 5060（便宜，2 秒，对方固定过端口时才可能命中）
        # 但公共网络里这也是 254 台陌生设备，一样不打。
        if self._is_public_net(local_ip):
            if deep_scanned:
                return miss(
                    f"公共网络：已经拿端口 {known_port} 扫过本机 /{self._subnet_prefix()}"
                    " 和记住过的网段，没找到人"
                )
            if blocked_by_cooldown:
                return miss(f"距上次扫描不到 {int(DIAL_SUBNET_COOLDOWN)} 秒，这次没重扫")
            return miss("公共网络：按规则不扫陌生设备，所以这次没找")
        now = time.monotonic()
        entries = _LAN_CACHE.get("entries")
        if not entries or now - float(_LAN_CACHE.get("ts") or 0) > LAN_CACHE_TTL:
            prefix = local_ip.rsplit(".", 1)[0] + "."
            entries = await asyncio.to_thread(self._scan_subnet, prefix, local_ip, sip.lan_probe_timeout)
            _LAN_CACHE["ts"] = now
            _LAN_CACHE["entries"] = entries

        if not entries:
            return miss("本网段 5060 端口没有任何 SIP 应答")
        # 同一个网段里可能不止一个 SIP 设备（路由器、别人的软电话）。
        # 优先挑应答里带被叫用户名的那个；只有一个候选且没得选时就用它。
        matched = [item for item in entries if callee_user and callee_user in item[1]]
        chosen = matched[0] if matched else (entries[0] if len(entries) == 1 else None)
        if not chosen:
            self.ctx.logger.info(
                "同网段有 %d 个 SIP 设备但没一个认得被叫 %s，改走公网账号：%s",
                len(entries),
                callee_user or "(空)",
                ", ".join(ip for ip, _ in entries[:5]),
            )
            return miss(
                f"同网段有 {len(entries)} 个 SIP 设备，但认不出被叫 {callee_user or '(空)'}"
            )
        h = chosen[0]
        return uri_for(h, 5060), h, 5060, local_ip

    def _local_net(self, local_ip: str = "") -> tuple[str, int]:
        """本机的 (IP, 掩码前缀)。

        判断「是不是同一个局域网」不能写死 /24：实测这套环境本机 10.0.0.5、
        网关 10.0.15.254，掩码 /20 —— 按 /24 算会把网关当成「别的网络」，缓存刚学会
        就被自己丢掉，内网直呼永远用不上。所以从 `ip addr` 读真实掩码，读不到才退回 /24。
        """
        ip = (local_ip or "").strip() or self._local_ipv4()
        if not ip:
            return "", 24
        now = time.monotonic()
        if _LOCAL_NET_CACHE.get("ip") == ip and now - float(_LOCAL_NET_CACHE.get("ts") or 0) < LOCAL_NET_TTL:
            return ip, int(_LOCAL_NET_CACHE.get("prefix") or 24)
        try:
            out = subprocess.run(
                ["ip", "-4", "-o", "addr", "show"],
                capture_output=True,
                text=True,
                timeout=3,
            ).stdout
        except (OSError, subprocess.SubprocessError):
            return ip, 24
        for line in out.splitlines():
            match = re.search(r"inet (\d{1,3}(?:\.\d{1,3}){3})/(\d{1,2})", line)
            if match and match.group(1) == ip:
                prefix = int(match.group(2))
                if 8 <= prefix <= 32:
                    _LOCAL_NET_CACHE.update(ip=ip, prefix=prefix, ts=now)
                    return ip, prefix
        return ip, 24

    @staticmethod
    def _in_same_net(host: str, local_ip: str, prefix: int) -> bool:
        """按掩码比较两个 IPv4 是否同网。"""
        def to_int(value: str) -> Optional[int]:
            parts = (value or "").strip().split(".")
            if len(parts) != 4:
                return None
            number = 0
            for part in parts:
                if not part.isdigit() or not 0 <= int(part) <= 255:
                    return None
                number = (number << 8) | int(part)
            return number

        host_num, local_num = to_int(host), to_int(local_ip)
        if host_num is None or local_num is None:
            return False
        mask = (0xFFFFFFFF << (32 - prefix)) & 0xFFFFFFFF if prefix else 0
        return (host_num & mask) == (local_num & mask)

    def _same_lan(self, host: str, local_ip: str) -> bool:
        """host 与本机是否属于同一局域网（按真实掩码，不写死 /24）。

        换了 WiFi / 热点之后，缓存里的地址会落到另一个网络里：拿它探测只会白等一个超时，
        拿它当扫描目标更糟——会去扫已经不存在的那段网络，整趟 18 秒全白费，还永远扫不到人。
        所以换网后必须先识别并丢掉这类缓存。
        """
        ip, prefix = self._local_net(local_ip)
        if not ip:
            return False
        return self._in_same_net(host, ip, prefix)

    def _drop_foreign_peer(self, local_ip: str, where: str) -> bool:
        """缓存的对端不在本机网段就丢掉，返回是否丢过。

        顺手把 lan_scan_fail_ts 也清掉：那次失败是旧网段的事，
        留着会让新网络白白多等 10 分钟冷却。
        """
        peer = self._state.get("lan_peer") or {}
        host = str(peer.get("host") or "")
        if not host or self._same_lan(host, local_ip):
            return False
        self.ctx.logger.info(
            "%s：缓存的内网对端 %s:%s 和本机 %s 不在同一网段（换过网络），丢掉后按当前网段重找",
            where,
            host,
            peer.get("port") or "?",
            local_ip,
        )
        self._state.pop("lan_peer", None)
        self._state.pop("lan_scan_fail_ts", None)
        self._save_state()
        return True

    # ──── 按网段分别缓存的对端 ────

    def _net_key(self, local_ip: str) -> str:
        """按 /24 归一化的网络标识，作为「每张网络各记一份」的键。

        掩码可能是 /16（校园网、部分路由器），但设备落在哪个 /24 跟「是不是同一台机器」
        没关系，所以统一按 /24 归并：换回以前连过的网络时能直接复用当时那台主机。
        """
        ip = (local_ip or "").strip()
        if not re.fullmatch(r"\d{1,3}(?:\.\d{1,3}){3}", ip):
            return ""
        return ip.rsplit(".", 1)[0] + ".0/24"

    @staticmethod
    def _same16_key(ip: str) -> str:
        """a.b.c.d → a.b.0.0/16。

        校园网这种大二层里，本机和接电话那台经常落在不同 /24（实测 10.0.0.x 对 10.0.4.x），
        但它们仍属同一张网，可以互相直连。所以「换 /24 了」不该等于「彻底失忆」。
        """
        s = (ip or "").strip()
        if not re.fullmatch(r"\d{1,3}(?:\.\d{1,3}){3}", s):
            return ""
        return ".".join(s.split(".")[:2]) + ".0.0/16"

    def _cache_get(self, local_ip: str) -> Dict[str, Any]:
        key = self._net_key(local_ip)
        if not key:
            return {}
        item = (self._state.get("lan_cache") or {}).get(key) or {}
        if isinstance(item, dict) and item.get("host"):
            return dict(item)
        # 本 /24 没有记录时，允许复用同一 /16 里最近成功过的那台主机。
        # 否则校园网每天换个 /24 就得重新手填 IP，用起来像坏了。
        return self._cache_reuse(local_ip)

    def _cache_reuse(self, local_ip: str) -> Dict[str, Any]:
        """跨 /24 复用：同一 /16 里最近写入的那条记录。

        只在「本 /24 完全没记录」时生效，且试失败一次就熄火（见 _note_reuse_fail），
        免得换到一张真正不同的网络后，每轮都白扫 14 秒。
        """
        zone = self._same16_key(local_ip)
        if not zone or self._state.get("lan_reuse_off") == zone:
            return {}
        cache = self._state.get("lan_cache") or {}
        best: Dict[str, Any] = {}
        for item in cache.values():
            if not isinstance(item, dict) or not item.get("host"):
                continue
            if self._same16_key(str(item.get("host"))) != zone:
                continue
            if str(item.get("ts") or "") > str(best.get("ts") or ""):
                best = dict(item)
        if best:
            best["source"] = "reuse"
        return best

    def _note_reuse_fail(self, local_ip: str) -> None:
        """跨 /24 复用试过一次不成就熄火，别每轮都白扫一遍端口段。"""
        zone = self._same16_key(local_ip)
        if zone:
            self._state["lan_reuse_off"] = zone
            self._save_state()

    def _note_lan_miss(self, local_ip: str, reason: str) -> None:
        """记下这轮为什么没找到内网对端，侧栏直接把下一步告诉用户。

        只往日志里写「没找到」是不够的：用户分不清是「没扫」（撞了冷却）
        还是「扫了没人应答」，也就不知道该不该手填一次 IP。这里把原因和
        实际扫过的范围一起留下来，侧栏照着显示。
        """
        self._state["lan_miss"] = {
            "ts": datetime.now().isoformat(timespec="seconds"),
            "local_ip": local_ip,
            "reason": reason,
            "prefix": self._subnet_prefix(),
        }
        self._save_state()

    def _clear_lan_miss(self) -> None:
        if self._state.pop("lan_miss", None) is not None:
            self._save_state()

    def _cache_put(self, local_ip: str, host: str, port: int, source: str) -> None:
        key = self._net_key(local_ip)
        if not key or not host or not port:
            return
        cache = dict(self._state.get("lan_cache") or {})
        cache[key] = {
            "host": host,
            "port": int(port),
            "ts": datetime.now().isoformat(timespec="seconds"),
            "source": source,
        }
        # 只留最近几张网络，别让 state.json 无限长
        if len(cache) > LAN_PEER_CACHE_MAX:
            ordered = sorted(cache.items(), key=lambda kv: str((kv[1] or {}).get("ts") or ""), reverse=True)
            cache = dict(ordered[:LAN_PEER_CACHE_MAX])
        self._state["lan_cache"] = cache
        # lan_peer 是老字段，侧边栏和旧逻辑还在读，保持同步
        self._state["lan_peer"] = dict(cache[key])
        self._state.pop("lan_scan_fail_ts", None)
        # 对上人了，L2.5 的退避立刻归零：下次真失联时又该从 5 分钟起步
        self._state["lan_subnet_miss"] = 0
        # 这一轮真的找到了人，跨段复用的「熄火」标记就该解除
        self._state.pop("lan_reuse_off", None)
        self._save_state()

    def _tcp_alive(self, host: str) -> bool:
        """用 TCP 连接探活：收到 RST（ConnectionRefused）就说明这台机器在线。

        这是主探活手段，因为 ICMP 在很多热点/路由器上被过滤 ——
        实测这台 B 机 UDP 的 SIP 探得到、ping 却是 100% 丢包。
        端口关着不要紧，内核会回 RST，那只证明「人在这儿」。
        """
        import socket as _socket

        for port in (80, 443):
            sock = _socket.socket(_socket.AF_INET, _socket.SOCK_STREAM)
            sock.settimeout(0.35)
            try:
                sock.connect((host, port))
                return True
            except ConnectionRefusedError:
                return True
            except OSError:
                continue
            finally:
                sock.close()
        return False

    def _host_alive(self, host: str) -> bool:
        """探活总入口：先 TCP（可靠），再 ICMP（兜底）。

        ICMP 必须发 2 个包：第一包经常在 ARP 解析期间丢掉，只发 1 个会把在线设备误判成离线。
        两样都不通不代表没开 SIP（有的设备全屏蔽入站），所以结论只用来「跳过明显死掉的地址」。
        """
        import subprocess

        if self._tcp_alive(host):
            return True
        try:
            done = subprocess.run(
                ["ping", "-c", "2", "-i", "0.2", "-W", "1", host],
                capture_output=True,
                timeout=4,
            )
            return done.returncode == 0
        except (OSError, subprocess.SubprocessError):
            return False

    def _sweep_hosts(self, local_ip: str) -> list[str]:
        """ping 扫本 /24，返回活跃主机（不含自己）。254 个 64 并发，实测 3~5 秒。"""
        from concurrent.futures import ThreadPoolExecutor

        prefix = local_ip.rsplit(".", 1)[0] + "."
        targets = [f"{prefix}{i}" for i in range(1, 255) if f"{prefix}{i}" != local_ip]
        with ThreadPoolExecutor(max_workers=64) as pool:
            alive = list(pool.map(self._host_alive, targets))
        return [ip for ip, ok in zip(targets, alive) if ok]

    def _is_public_net(self, local_ip: str, refresh: bool = False) -> bool:
        """这张网是不是「公共网络」——校园网 / 公司 / 酒店，本 /24 里几十上百台设备。

        公共网络里什么都不扫：接听端往往在自己 /24 之外，扫也扫不到；
        几万个探测包打到陌生设备上既扰民，也容易被网络中心盯上。
        只保留「记住过的那台主机」这条路（L1/L2），没有就让用户手填一次 IP。

        refresh=False 时只读缓存，未知一律当「不是公共网络」，
        这样拨号现场不会为了判断而先去扫一遍网段。
        """
        cache = _PUBLIC_NET_CACHE
        fresh = (
            cache.get("ip") == local_ip
            and time.monotonic() - float(cache.get("ts") or 0) < PUBLIC_NET_TTL
        )
        if fresh:
            return bool(cache.get("public"))
        if not refresh or not self._same16_key(local_ip):
            return False
        hosts = self._sweep_hosts(local_ip)
        is_public = len(hosts) > LAN_SWEEP_MAX_HOSTS
        cache.update({
            "ip": local_ip,
            "public": is_public,
            "count": len(hosts),
            "ts": time.monotonic(),
        })
        if is_public:
            self.ctx.logger.info(
                "本网段有 %d 台活跃设备，判定为公共网络：不扫网关、不扫陌生设备，"
                "只复用记住过的那台主机（没有就在「内网直呼」里手填接听端 IP，端口可留空）",
                len(hosts),
            )
        return is_public

    def _subnet_prefix(self) -> int:
        """整段补救扫描的前缀。读取时夹在 16~24，配置被改坏也不该让插件起不来。"""
        try:
            value = int(self.config.sip.lan_subnet_prefix)
        except (TypeError, ValueError):
            value = 20
        return max(16, min(24, value))

    def _minutes_to_next_job(self) -> Optional[float]:
        """离「下一个会打电话的任务」还有多少分钟；没有任务或算不出来返回 None。

        只用来决定 L2.5 要不要临时加班，算错也不该影响拨号，所以异常一律吞掉。
        """
        try:
            now = datetime.now()
            best: Optional[float] = None
            for job in self.config.jobs:
                if not getattr(job, "enabled", False):
                    continue
                try:
                    at = now.replace(
                        hour=int(job.hour), minute=int(job.minute), second=0, microsecond=0
                    )
                except (TypeError, ValueError):
                    continue
                if at < now:
                    at += timedelta(days=1)
                left = (at - now).total_seconds() / 60.0
                if best is None or left < best:
                    best = left
            return best
        except Exception:  # noqa: BLE001 - 算不出来就当没有任务，不影响主流程
            return None

    def _subnet_scan_cooldown(self, public: bool) -> float:
        """L2.5 这次要等多久才能再扫。"""
        if not public:
            return LAN_SUBNET_COOLDOWN
        try:
            miss = int(self._state.get("lan_subnet_miss") or 0)
        except (TypeError, ValueError):
            miss = 0
        left = self._minutes_to_next_job()
        if left is not None and left <= LAN_PREWAKE_MINUTES:
            return LAN_SUBNET_COOLDOWN
        return LAN_SUBNET_BACKOFF[min(max(miss, 0), len(LAN_SUBNET_BACKOFF) - 1)]

    def _subnet_scan_allowed(self, public: bool = False) -> bool:
        waited = time.time() - float(self._state.get("lan_subnet_scan_ts") or 0)
        return waited > self._subnet_scan_cooldown(public)

    def _dial_subnet_allowed(self) -> bool:
        """拨号现场能不能再扫一次整段。

        只要求 60 秒内没扫过，不继承预热循环攒下的退避（最长 60 分钟）。
        拨号是「现在就要打」，为了省 7 秒的探测而多花 80 秒走公网是本末倒置。
        """
        waited = time.time() - float(self._state.get("lan_subnet_scan_ts") or 0)
        return waited > DIAL_SUBNET_COOLDOWN

    def _last_known_port(self) -> int:
        """缓存里最近一次成功过的 SIP 端口，跨网段也算。

        整段补救扫描就靠它当「名字」：只要对方 App 没重启，端口就不会变，
        换到哪个 /24 都能用这一个端口把人找回来。
        """
        cache = self._state.get("lan_cache") or {}
        best: Dict[str, Any] = {}
        for item in cache.values():
            if not isinstance(item, dict) or not item.get("port"):
                continue
            if str(item.get("ts") or "") > str(best.get("ts") or ""):
                best = item
        try:
            return int(best.get("port") or 0)
        except (TypeError, ValueError):
            return 0

    def _options_scan(self, targets: list[str], port: int, local_ip: str) -> Optional[str]:
        """对一批地址的同一个端口发 SIP OPTIONS，谁回了 SIP/2.0 就返回谁。

        必须用 UDP OPTIONS 而不是 TCP connect：Linphone 的 SIP 端口是 UDP 监听的，
        TCP 连不上（实测拿 TCP 扫整段会把真正的对端漏掉）。

        实现上刻意**不用线程池**：/20 有 4000 多个地址，起 400 个线程（每个一个 socket）
        在 proot 里是实打实的 OOM 风险；而且 map + with 的组合在命中之后还要等整批
        超时才退出，命中越靠后浪费越多。这里改成「一个非阻塞 socket 全发出去、再统一收」：
        包少、无栈开销，命中立刻就能返回，实测比线程池快 3 倍以上。
        """
        import select
        import socket as _socket

        if not targets:
            return None
        target = int(port)
        sock = _socket.socket(_socket.AF_INET, _socket.SOCK_DGRAM)
        try:
            sock.bind(("0.0.0.0", 0))
            sock.setblocking(False)
            # 同一个 branch 足够：我们只按来源 IP 认人，不靠 Call-ID 配对。
            branch = uuid.uuid4().hex[:12]
            for index, ip in enumerate(targets):
                payload = self._options_payload(ip, target, local_ip, branch)
                # 发送缓冲会满（4000 多个包约 2MB），满了就退让 2ms 再塞，
                # 不能吞掉这个包——吞掉就等于那台设备没被扫过。
                for _ in range(40):
                    try:
                        sock.sendto(payload, (ip, target))
                        break
                    except (BlockingIOError, InterruptedError):
                        time.sleep(0.002)
                    except OSError:
                        break
                # 每 64 个包让一下 CPU，避免把整段一次性灌出去挤掉别的网络请求。
                if index % 64 == 63:
                    time.sleep(0.001)
            deadline = time.monotonic() + LAN_SCAN_COLLECT
            while time.monotonic() < deadline:
                ready, _, _ = select.select([sock], [], [], 0.2)
                if not ready:
                    continue
                try:
                    data, addr = sock.recvfrom(2048)
                except (BlockingIOError, InterruptedError):
                    continue
                except OSError:
                    # 前面的包招回来的 ICMP 端口不可达会在这里冒出来，跳过即可。
                    continue
                if data.startswith(b"SIP/2.0"):
                    return addr[0]
            return None
        finally:
            sock.close()

    def _historical_subnet_prefixes(self, local_ip: str) -> list[str]:
        """历史命中过的 /24 前缀（同一 /16 内，排除本机所在 /24）。

        L2.5 默认只扫本机 /20，覆盖不到离得远的那一段
        （本机 10.0.129.x、对端漂到 10.0.200.x 就正好在 /20 之外）。
        而缓存本来就按 /24 分键存着，把历史段捞出来优先扫几乎不花成本：
        一个 /24 只有 253 个包，命中即止，比把本机段放大到 /19 更省、也更准。
        """
        zone = self._same16_key(local_ip)
        if not zone:
            return []
        cur = local_ip.rsplit(".", 1)[0] + "."
        out: list[str] = []
        for key in (self._state.get("lan_cache") or {}):
            net = str(key).split("/", 1)[0]
            if not re.fullmatch(r"\d{1,3}(?:\.\d{1,3}){3}", net):
                continue
            if self._same16_key(net) != zone:
                continue
            prefix = net.rsplit(".", 1)[0] + "."
            if prefix != cur and prefix not in out:
                out.append(prefix)
        return out[:LAN_HISTORY_SUBNET_MAX]

    def _scan_subnet_for_port(self, local_ip: str, port: int) -> Optional[str]:
        """拿已知端口扫本机整段，把「换了 IP 但 App 没重启」的对端找回来。

        为什么有效：Linphone 的监听端口只在 App 重启时重新分配，重连 WiFi、
        DHCP 换地址时端口保持不变。所以那个端口可以当「名字」用 ——
        校园网里本机和手机天天落在不同 /24，靠它就不用每次重填地址。
        实测 /20（4094 个地址）单 socket 收发 2.9 秒、内存只涨 0.4MB；/24 不到 1 秒。
        """
        import ipaddress

        if not local_ip or not port:
            return None

        # 先扫历史命中过的 /24：校园网里对端经常落在本机 /20 之外的另一段，
        # 而这条路每个段只要 253 个包，命中即止。全部落空再回退扫本机整段。
        for prefix in self._historical_subnet_prefixes(local_ip):
            targets = [f"{prefix}{i}" for i in range(1, 255) if f"{prefix}{i}" != local_ip]
            if not targets:
                continue
            hit = self._options_scan(targets, int(port), local_ip)
            if hit:
                self.ctx.logger.info(
                    "L2.5 在历史网段 %s0/24 命中 %s（本机 /%d 那段没扫）",
                    prefix,
                    hit,
                    self._subnet_prefix(),
                )
                return hit

        want = self._subnet_prefix()
        net = None
        # 配了 /16 或 /18 时地址数会超过上限（6 万 / 1.6 万个），直接返回 None 会让
        # 日志说「整段没扫到」，用户以为功能坏了。这里往下收敛到放得下的最大范围，
        # 并且明确告诉他实际扫了多少 —— 宁可少扫一点，也不能静默失效。
        for prefix in range(want, 25):
            try:
                cand = ipaddress.ip_network(f"{local_ip}/{prefix}", strict=False)
            except ValueError:
                return None
            if cand.num_addresses - 2 <= LAN_SUBNET_MAX_HOSTS:
                net = cand
                if prefix != want:
                    self.ctx.logger.info(
                        "找回范围 /%d 超出单次上限（%d 个地址），本次收敛到 /%d",
                        want,
                        LAN_SUBNET_MAX_HOSTS,
                        prefix,
                    )
                break
        if net is None:
            return None
        targets = [str(host) for host in net.hosts() if str(host) != local_ip]
        if not targets:
            return None
        return self._options_scan(targets, int(port), local_ip)

    def _reheal_allowed(self) -> bool:
        return time.time() - float(self._state.get("lan_reheal_ts") or 0) > LAN_REHEAL_COOLDOWN

    def _note_lan_peer(self, addr: tuple[str, int], data: bytes) -> None:
        """记下同网段对端的 (IP, 端口)。这是内网直呼最可靠的端口来源。"""
        try:
            host, port = str(addr[0]), int(addr[1])
        except (TypeError, ValueError, IndexError):
            return
        local_ip = self._local_ipv4()
        if not local_ip or host == local_ip or port <= 0:
            return
        # 只认同一个局域网：按真实掩码判断，不能写死 /24 ——
        # 校园网 / 大二层里本机和网关经常不在同一 /24，写死会把真正的对端挡在外面。
        if not self._same_lan(host, local_ip):
            return
        prev = self._cache_get(local_ip)
        if str(prev.get("host")) == host and int(prev.get("port") or 0) == port:
            return  # 端口没变，不重复写盘
        self._cache_put(local_ip, host, port, "learned")
        self.ctx.logger.info("学到内网对端 %s:%s（来自它的主动发包），下次拨号优先直呼这里", host, port)

    async def _start_lan_listener(self) -> None:
        """开启 5060 监听，用来学习对端端口。只在开了内网直呼时才占用这个端口。"""
        if self._lan_transport is not None:
            return
        loop = asyncio.get_running_loop()
        try:
            transport, _ = await loop.create_datagram_endpoint(
                lambda: _LanProbeProtocol(self),
                local_addr=("0.0.0.0", 5060),
            )
        except OSError as exc:
            # 端口被别人占着不是致命问题：还能靠扫描 /24 和手动填 IP 工作。
            self.ctx.logger.info("5060 绑定失败（%s），暂时学不到对端端口，内网直呼改用扫描/手填", exc)
            return
        self._lan_transport = transport
        peer = self._state.get("lan_peer") or {}
        detail = f"，上次学到 {peer.get('host')}:{peer.get('port')}" if peer.get("host") else ""
        self.ctx.logger.info("内网对端学习已开启（监听 5060）%s", detail)

    async def _stop_lan_listener(self) -> None:
        if self._lan_transport is not None:
            with contextlib.suppress(Exception):
                self._lan_transport.close()
            self._lan_transport = None
            self.ctx.logger.info("内网对端学习已停止")

    def _start_lan_prewarm(self) -> None:
        """后台预热内网对端端口。

        拨号现场扫描两万多个端口要等 4~8 秒，闹钟电话不该被这个拖住。
        所以插件一加载就在后台先摸一遍，之后每 10 分钟复查一次：端口变了就地更新，
        真正拨号时永远是命中缓存、零等待。
        """
        if not self.config.sip.lan_scan_enabled:
            return
        if self._prewarm_task and not self._prewarm_task.done():
            return
        self._prewarm_task = asyncio.create_task(self._lan_prewarm_loop())
        self.ctx.logger.info("内网端口预热已启动（后台运行，不影响拨号）")

    async def _stop_lan_prewarm(self) -> None:
        if self._prewarm_task is not None:
            self._prewarm_task.cancel()
            with contextlib.suppress(asyncio.CancelledError, Exception):
                await self._prewarm_task
            self._prewarm_task = None
            self.ctx.logger.info("内网端口预热已停止")

    async def _lan_prewarm_loop(self) -> None:
        # 先歇 40 秒，别和 QQ 登录、插件加载抢资源
        await asyncio.sleep(40)
        last_ip = ""
        while True:
            try:
                if not self.config.sip.lan_call_enabled:
                    return
                cur = await asyncio.to_thread(self._local_ipv4)
                if last_ip and cur and cur != last_ip:
                    # 换网络了：网关和 IP 都可能变。缓存按网段分开存，
                    # 所以这里不动缓存，只清掉全局失败冷却，立刻按这张网络找。
                    self._state.pop("lan_scan_fail_ts", None)
                    self._save_state()
                    self.ctx.logger.info(
                        "本机地址 %s → %s（换过网络），按这张网络的历史缓存找内网对端", last_ip, cur
                    )
                if cur:
                    last_ip = cur
                await self._lan_prewarm_once()
            except asyncio.CancelledError:
                raise
            except Exception as exc:  # 预热失败绝不能影响主流程
                self.ctx.logger.info("内网端口预热出错（已忽略）：%s", exc)
            # L1 只发 1 个包，所以查得勤：对方 App 重启换端口后最多 1 分钟自愈。
            # 重扫（14 秒那种）由 _reheal_allowed / _lan_scan_allowed 各自限流。
            await asyncio.sleep(LAN_PREWARM_INTERVAL)

    def _prewarm_log(self, state: str, msg: str, *args: Any) -> None:
        """预热循环的日志：只在「状态真的变了」的时候打 info。

        这个循环 60 秒一轮。对端整晚不在网里时，原来每分钟都打一句同样的话，
        一天 1400 条同质日志，把真正有用的信息全埋了。状态没变就降成 debug：
        出事要查的时候看得到，平时不刷屏。
        """
        if self._state.get("lan_prewarm_state") == state:
            self.ctx.logger.debug(msg, *args)
            return
        self._state["lan_prewarm_state"] = state
        self._save_state()
        self.ctx.logger.info(msg, *args)

    async def _lan_prewarm_once(self) -> None:
        sip = self.config.sip
        if not sip.lan_scan_enabled or not self.config.sip.lan_call_enabled:
            return
        if self._busy:  # 正在打电话，别去打扰
            return
        local_ip = await asyncio.to_thread(self._local_ipv4)
        if not local_ip:
            return
        # 缓存按网段分开存，所以这里只需要保证 lan_peer 镜像不会指到别的网络
        self._drop_foreign_peer(local_ip, "内网端口预热")
        cached = self._cache_get(local_ip)
        host = str(cached.get("host") or "")
        port = int(cached.get("port") or 0)

        # L1：一个包验缓存
        host_up = True
        if host and port:
            alive = await asyncio.to_thread(
                self._sip_options_probe, host, port, sip.lan_probe_timeout, local_ip
            )
            if alive:
                self._prewarm_log("ok", "内网对端 %s:%s 在线，缓存可用", host, port)
                return  # 缓存还能用，什么都不用做
            host_up = await asyncio.to_thread(self._tcp_alive, host)
            if host_up:
                self._prewarm_log(
                    "port_changed", "L1 缓存 %s:%s 不应答（对方 App 重启过？）", host, port
                )
            else:
                self._prewarm_log("host_gone", "L1 的 %s 已经不在这张网里", host)
        elif not host:
            self._prewarm_log("no_cache", "还没有内网对端记录，等对方先发包或手填一次 IP")

        # L2：端口每次 App 启动都会变，但 IP 在同一张网络里很稳 → 只重扫这一台
        if host and host_up and self._reheal_allowed():
            self.ctx.logger.info("L2 对 %s 重扫临时端口段（端口会随 App 重启变化）", host)
            found = await asyncio.to_thread(self._scan_lan_sip_port, host, local_ip)
            self._state["lan_reheal_ts"] = time.time()
            if not found and str(cached.get("source") or "") == "reuse":
                # 跨 /24 借来的地址扫不到：这张 /16 里它确实不在了，先熄火别每轮白扫
                self._note_reuse_fail(local_ip)
            self._save_state()
            if found:
                self._cache_put(local_ip, host, found, "prewarm")
                self.ctx.logger.info("L2 自愈成功：%s:%s，拨号时直接命中", host, found)
                return
            self.ctx.logger.info("L2 没扫到，这台地址可能已经换人了")

        # 公共网络判定提到 L2.5 之**前**：判定成立后 L2.5 要按退避表放慢。
        # 原来放在 L2.5 之后，等于「承诺公共网络不扫」却每 5 分钟往 4094 个地址发包。
        public = await asyncio.to_thread(self._is_public_net, local_ip, True)

        # 整段补救要一个「名字」，缓存里的端口优先；缓存被挤掉时回退到历史最近端口。
        known_port = port or self._last_known_port()

        # L2.5：IP 换了、端口没变 —— 拿旧端口扫历史 /24，再扫本机整段。
        # 校园网 DHCP 每天给一个新 /24，这一步是「不用重填地址」的关键。
        if known_port and sip.lan_subnet_scan and self._subnet_scan_allowed(public):
            self.ctx.logger.info(
                "L2.5 拿旧端口 %s 找对端（历史 /24 优先，再扫本机 /%d；下次冷却 %d 秒）",
                known_port,
                self._subnet_prefix(),
                int(self._subnet_scan_cooldown(public)),
            )
            moved = await asyncio.to_thread(self._scan_subnet_for_port, local_ip, known_port)
            self._state["lan_subnet_scan_ts"] = time.time()
            if moved:
                self._cache_put(local_ip, moved, known_port, "prewarm")
                self._save_state()
                self.ctx.logger.info("L2.5 自愈成功：%s:%s，拨号时直接命中", moved, known_port)
                return
            try:
                miss = int(self._state.get("lan_subnet_miss") or 0)
            except (TypeError, ValueError):
                miss = 0
            self._state["lan_subnet_miss"] = min(miss + 1, len(LAN_SUBNET_BACKOFF) - 1)
            self._save_state()
            self.ctx.logger.info(
                "L2.5 没扫到（连续 %d 次），%s",
                self._state["lan_subnet_miss"],
                "公共网络里按退避放慢" if public else "5 分钟后重试",
            )

        # 公共网络到此为止：网关是学校/公司的核心设备，扫它两万多个端口既没意义又招人烦。
        # 这里只花 3 秒判一次（结果缓存 10 分钟），判定成立就只留 L1/L2/L2.5 这条路。
        if public:
            return

        # 重扫是有代价的（一次近 3 万个包），失败后按冷却来；这里说清楚在等什么，
        # 否则日志里看起来像是「预热凭空停了」。
        if not self._lan_scan_allowed():
            fail_at = float(self._state.get("lan_scan_fail_ts") or 0)
            left = int(max(0.0, LAN_SCAN_COOLDOWN - (time.time() - fail_at)))
            self.ctx.logger.info("端口扫描冷却中（还剩 %d 秒），这轮只验了缓存", left)
            return

        # L3：网关（对方开热点时它就是网关）
        gateway = await asyncio.to_thread(self._default_gateway)
        if gateway and gateway != host:
            self.ctx.logger.info("L3 扫网关 %s 的临时端口段（不响铃）", gateway)
            found = await asyncio.to_thread(self._scan_lan_sip_port, gateway, local_ip)
            if found:
                self._cache_put(local_ip, gateway, found, "prewarm")
                self.ctx.logger.info("L3 命中网关 %s:%s，已写入缓存", gateway, found)
                return

        # L4：完全没线索时的兜底 —— 探活扫出活跃主机，逐台试（限量，最坏 4 台 × 14 秒）
        if self._lan_scan_allowed():
            hosts = await asyncio.to_thread(self._sweep_hosts, local_ip)
            if len(hosts) > LAN_SWEEP_MAX_HOSTS:
                # 校园网 / 酒店 / 公司这类公共网络：几十上百台设备，接听端还常在别的 /24。
                # 这时候逐台扫端口既没用又是在骚扰别人的机器，直接放弃自动发现。
                self._state["lan_scan_fail_ts"] = time.time()
                self._save_state()
                self.ctx.logger.info(
                    "L4 本网段有 %d 台活跃设备，判定为公共网络，跳过逐台端口扫描"
                    "（这类网络请在内网直呼里手填接听端的 IP，端口可留空）",
                    len(hosts),
                )
                return
            skip = {local_ip, host, gateway}
            candidates = [h for h in hosts if h not in skip][:LAN_SWEEP_LIMIT]
            if candidates:
                self.ctx.logger.info(
                    "L4 本网段 %d 台活跃，按顺序试这几台：%s", len(hosts), ", ".join(candidates)
                )
            for cand in candidates:
                found = await asyncio.to_thread(self._scan_lan_sip_port, cand, local_ip)
                if found:
                    self._cache_put(local_ip, cand, found, "prewarm")
                    self.ctx.logger.info("L4 命中 %s:%s，已写入缓存", cand, found)
                    return
            self._state["lan_scan_fail_ts"] = time.time()
            self._save_state()
            self.ctx.logger.info("五层都没找到内网对端，10 分钟内不再重扫（等对方主动发包或换网络）")

    # ──── 状态与路径 ────

    def _audio_dir(self) -> Path:
        base = self._state_path.parent if self._state_path else Path(__file__).resolve().parent / "data"
        path = base / "audio"
        path.mkdir(parents=True, exist_ok=True)
        return path

    def _dial_log_path(self) -> Path:
        """每次拨号的 baresip 完整报文单独存一份，事后不用再猜断在哪一步。"""
        base = self._state_path.parent if self._state_path else Path(__file__).resolve().parent / "data"
        with contextlib.suppress(OSError):
            folder = base / "logs"
            folder.mkdir(parents=True, exist_ok=True)
            return folder / datetime.now().strftime("baresip-%Y%m%d-%H%M%S.log")
        return Path(tempfile.gettempdir()) / "baresip-last.log"

    def _write_dial_log(self, path: Path, chunks: list[str]) -> None:
        try:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("".join(chunks), encoding="utf-8")
            # 只留最近 30 份，别把手机空间吃光。
            olds = sorted(path.parent.glob("baresip-*.log"))
            for old in olds[:-DIAL_LOG_KEEP]:
                with contextlib.suppress(OSError):
                    old.unlink()
        except Exception:  # noqa: BLE001 - 日志写不进去也不该影响拨打
            with contextlib.suppress(Exception):
                self.ctx.logger.warning("写拨号报文失败: %s", path, exc_info=True)

    def _resolve_state_path(self) -> Path:
        with contextlib.suppress(Exception):
            data_dir = getattr(self.ctx.paths, "data_dir", None)
            if data_dir:
                path = Path(str(data_dir)) / STATE_FILENAME
                path.parent.mkdir(parents=True, exist_ok=True)
                return path
        fallback = Path(__file__).resolve().parent / "data"
        fallback.mkdir(parents=True, exist_ok=True)
        return fallback / STATE_FILENAME

    def _load_state(self) -> Dict[str, Any]:
        if not self._state_path or not self._state_path.exists():
            return {}
        try:
            return dict(json.loads(self._state_path.read_text(encoding="utf-8")))
        except Exception:
            self.ctx.logger.warning("麦麦电话闹钟状态文件损坏，按空状态启动: %s", self._state_path)
            return {}

    def _save_state(self) -> None:
        if not self._state_path:
            return
        # 先写临时文件再 os.replace：直接覆盖写如果正好被 kill（proot 里 OOM、
        # 用户强停 App）会留下半截 JSON，下次启动按空状态走 —— 今天已经拨过的任务
        # 会被当成没拨，早上连打好几通。replace 是原子的，最坏也是保留旧文件。
        tmp = self._state_path.with_suffix(self._state_path.suffix + ".tmp")
        try:
            tmp.write_text(json.dumps(self._state, ensure_ascii=False, indent=2), encoding="utf-8")
            os.replace(tmp, self._state_path)
        except Exception:
            self.ctx.logger.exception("麦麦电话闹钟状态写入失败")
            with contextlib.suppress(OSError):
                tmp.unlink()

    def _job_state(self, jid: str) -> Dict[str, Any]:
        """按任务拿今天的记录（拨没拨过、试了几次、上次说了什么）。"""
        key = (jid or "").strip() or "default"
        jobs = self._state.setdefault("jobs", {})
        state = jobs.get(key)
        if not isinstance(state, dict):
            state = {}
            jobs[key] = state
        return state

    def _migrate_state(self) -> None:
        """把 0.1.x 的顶层记录搬进第一个任务下，省得今天已经拨过的任务被重拨。"""
        if self._state.get("jobs"):
            return
        target = self.config.jobs[0].id if self.config.jobs else "morning"
        moved: Dict[str, Any] = {}
        for key in (
            "last_fired_date",
            "last_fired_at",
            "last_text",
            "last_result",
            "last_error",
            "attempts",
            "skipped_date",
        ):
            if key in self._state:
                moved[key] = self._state.pop(key)
        if moved:
            self._state["jobs"] = {(target or "morning"): moved}
            self._save_state()
            self.ctx.logger.info("旧拨打记录已迁移到任务 %s 下", target)

    def _attempts_today(self, today: str, jid: str = "") -> int:
        attempts = self._job_state(jid).get("attempts") or {}
        if isinstance(attempts, dict) and attempts.get("date") == today:
            with contextlib.suppress(TypeError, ValueError):
                return int(attempts.get("count") or 0)
        return 0

    # ──── WebUI 侧边栏 API ────

    def _persona_public(self) -> Dict[str, Any]:
        """给页面用的人设视图：插件内那份全文 + 这次真正会注入的内容。"""
        p = self.config.persona
        raw = self._bot_persona_raw()
        first = re.split(r"\n\s*\n", raw)[0].strip() if raw else ""
        effective, note = self._persona_text()
        text = (p.text or "").strip()
        prev = self._state.get("persona_prev") or {}
        return {
            "source": self._persona_source(),
            "text": p.text or "",
            "text_len": len(text),
            "first_paragraph_only": bool(p.first_paragraph_only),
            "initialized": bool(p.initialized),
            "synced_at": p.synced_at or "",
            "bot_available": bool(raw),
            "bot_len": len(raw),
            "bot_first_len": len(first),
            "effective": effective,
            "effective_len": len(effective),
            "effective_note": note,
            "limit": PERSONA_INJECT_LIMIT,
            "prev_len": len(str(prev.get("text") or "")),
            "prev_at": str(prev.get("at") or ""),
        }

    def _guard_public(self) -> Dict[str, Any]:
        """给页面用的守门视图。

        词表 / 台词池留空时页面显示的是「内置默认」占位，而不是空框——
        否则用户会以为没生效，实际后台正用着内置那份。
        """
        # 这里整段兜异常：状态接口是页面唯一的入口，任何一项读崩了都会让整页空白，
        # 用户看到的就是「插件里的东西全没了」，比数值不对难排查得多。
        try:
            g = self.config.guard
            words = (g.ban_words or "").strip()
            lines = (g.fallback_lines or "").strip()
            enabled = bool(g.enabled)
            cap = self._guard_cap()
            ban_count = len(self._ban_words()) if enabled else 0
            pool_count = len(self._fallback_pool())
        except Exception:  # noqa: BLE001
            self.ctx.logger.exception("读取台词守门配置失败，页面用默认值兜底")
            return {
                "enabled": True,
                "max_chars": 80,
                "ban_words": "",
                "ban_words_custom": False,
                "ban_words_default": "\n".join(DEFAULT_BAN_WORDS),
                "ban_words_count": len(DEFAULT_BAN_WORDS),
                "fallback_lines": "",
                "fallback_custom": False,
                "fallback_default": "\n".join(DEFAULT_FALLBACK_LINES),
                "fallback_count": len(DEFAULT_FALLBACK_LINES),
            }
        return {
            "enabled": enabled,
            "max_chars": cap,
            "ban_words": words,
            "ban_words_custom": bool(words),
            "ban_words_default": "\n".join(DEFAULT_BAN_WORDS),
            "ban_words_count": ban_count,
            "fallback_lines": lines,
            "fallback_custom": bool(lines),
            "fallback_default": "\n".join(DEFAULT_FALLBACK_LINES),
            "fallback_count": pool_count,
        }

    def _tts_public(self) -> Dict[str, Any]:
        """给页面用的 TTS 配置：密钥只回「有没有填」，不回明文。"""
        t = self.config.tts
        return {
            "backend": (t.backend or "edge").strip().lower(),
            "timeout": int(t.timeout),
            "edge_voice": t.edge_voice,
            "edge_rate": t.edge_rate,
            "openai_url": t.openai_url or t.api_url,
            "openai_key_set": bool((t.openai_key or t.api_key).strip()),
            "openai_model": t.openai_model or t.api_model,
            "openai_voice": t.openai_voice,
            "openai_format": t.openai_format or t.response_format,
            "openai_speed": float(t.openai_speed or 1.0),
            "minimax_url": t.minimax_url,
            "minimax_key_set": bool(t.minimax_key.strip()),
            "minimax_group_id": t.minimax_group_id,
            "minimax_model": t.minimax_model,
            "minimax_voice": t.minimax_voice,
            "minimax_format": t.minimax_format,
            "minimax_speed": float(t.minimax_speed or 1.0),
            "doubao_api": t.doubao_api,
            "doubao_url": t.doubao_url,
            "doubao_token_set": bool(t.doubao_token.strip()),
            "doubao_resource_id": t.doubao_resource_id,
            "doubao_voice": t.doubao_voice,
            "doubao_format": t.doubao_format,
            "doubao_speed": float(t.doubao_speed or 1.0),
            "doubao_sample_rate": int(t.doubao_sample_rate),
            "last_preview": self._state.get("last_preview") or "",
        }

    @API("webui_status", description="读取麦麦电话闹钟的配置、每个任务的下次拨打时间与最近结果", version="1")
    async def webui_status(self) -> Dict[str, Any]:
        sip = self.config.sip
        wake = self.config.wake
        now = datetime.now()
        today = now.strftime("%Y-%m-%d")
        jobs = [self._job_public(job) for job in self.config.jobs]
        active = [job for job in self.config.jobs if job.enabled]
        if active:
            soon = min(active, key=self._next_at_for)
            next_at = self._next_at_for(soon)
            next_job = soon.label or soon.id
        else:
            next_at = ""
            next_job = ""

        bin_path = Path(sip.baresip_bin)
        # 用兜底后的实际路径，云端用户的「环境自检」才不会误报模块目录不存在
        module_dir = self._resolve_module_path()
        account_ready = bool(sip.caller_aor.strip() and sip.caller_pass.strip() and sip.callee_aor.strip())
        return {
            "now": now.isoformat(timespec="seconds"),
            "ticking": self._task is not None and not self._task.done(),
            "busy": self._busy,
            "wake_enabled": bool(wake.enabled),
            "sip_enabled": bool(sip.enabled),
            "check_interval_seconds": int(wake.check_interval_seconds),
            "default_max_chars": int(wake.max_chars),
            "default_llm_task": wake.llm_task,
            "default_intent": DEFAULT_INTENT,
            "next_at": next_at,
            "next_job": next_job,
            "jobs": jobs,
            "job_count": len(jobs),
            "jobs_enabled": len(active),
            "caller_aor": sip.caller_aor,
            "caller_pass_set": bool(sip.caller_pass.strip()),
            "callee_aor": sip.callee_aor,
            "server": self._sip_server(),
            "transport": (sip.transport or "").strip().lower(),
            # 实际拼进 accounts 的 outbound，云端排查时一眼能看出端口/传输层对不对
            "outbound": self._safe_outbound(),
            "ring_seconds": int(sip.ring_seconds),
            "retry_times": int(sip.retry_times),
            "retry_interval_seconds": int(sip.retry_interval_seconds),
            "lan_call_enabled": bool(sip.lan_call_enabled),
            "lan_target": sip.lan_target,
            "lan_scan_enabled": bool(sip.lan_scan_enabled),
            "lan_fallback_public": bool(sip.lan_fallback_public),
            "lan_subnet_scan": bool(sip.lan_subnet_scan),
            "lan_subnet_prefix": self._subnet_prefix(),
            "local_ip": self._local_ipv4(),
            "lan_peer": self._state.get("lan_peer") or {},
            "lan_miss": self._state.get("lan_miss") or {},
            "tts_backend": self.config.tts.backend,
            "tts_voice": self.config.tts.edge_voice,
            "tts": self._tts_public(),
            "guard": self._guard_public(),
            "persona": self._persona_public(),
            "baresip_ok": bin_path.exists(),
            "ffmpeg_ok": shutil.which("ffmpeg") is not None,
            "modules_ok": module_dir.is_dir(),
            "account_ready": account_ready,
            "last_test_at": self._state.get("last_test_at") or "",
            "last_preview": self._state.get("last_preview") or "",
            "attempts_today": sum(item["attempts_today"] for item in jobs),
            "today": today,
        }

    @API("webui_save", description="保存总开关、SIP 账号与通话参数（时间与提示词在任务列表里）", version="1")
    async def webui_save(
        self,
        wake_enabled: bool = True,
        sip_enabled: bool = True,
        caller_aor: str = "",
        caller_pass: str = "",
        callee_aor: str = "",
        ring_seconds: int = 45,
        retry_times: int = 2,
        # 内网直呼：同网段时把 INVITE 直接发给对端 IP，媒体不出局域网。
        lan_call_enabled: bool = False,
        lan_target: str = "",
        lan_scan_enabled: bool = True,
        lan_fallback_public: bool = True,
        # 整段补救：IP 变了但端口没变时，拿旧端口扫一遍本机网段。
        # prefix 传 0/非法值 = 保持原设定（老页面不带这个字段）。
        lan_subnet_scan: bool = True,
        lan_subnet_prefix: int = 0,
        # 默认空 = 不动后端；页面没传这个字段时不能把用户选的豆包写回 edge。
        tts_backend: str = "",
        tts_voice: str = "",
        # 兼容升级前缓存在浏览器里的旧页面：它还会发 hour/minute。
        # 宿主对未声明参数是直接拒绝的，所以这两个必须收下，不能装作没有。
        hour: int = -1,
        minute: int = -1,
    ) -> Dict[str, Any]:
        if type(ring_seconds) is not int or not 10 <= ring_seconds <= 180:
            raise ValueError("单次通话时长必须是 10-180 秒")
        if type(retry_times) is not int or not 0 <= retry_times <= 5:
            raise ValueError("重拨次数必须是 0-5")
        tts_backend = (tts_backend or "").strip().lower()
        if tts_backend and tts_backend not in {"edge", "openai", "minimax", "doubao"}:
            raise ValueError("语音后端只能是 edge / openai / minimax / doubao")
        # 页面还没加载完就点保存时，空值不能把已有账号清掉。
        # 把页面原始提交值单独记下来：之前「保存被叫却回退成自己的号」查了很久，
        # 就是因为日志只打了回填后的值，分不清到底是页面没传、还是后端改错了。
        page_caller = (caller_aor or "").strip()
        page_callee = (callee_aor or "").strip()
        caller_aor = self._normalize_aor(page_caller) or (self.config.sip.caller_aor or "")
        callee_aor = self._normalize_aor(page_callee) or (self.config.sip.callee_aor or "")
        for label, value in (("主叫", caller_aor), ("被叫", callee_aor)):
            if value and not re.fullmatch(r"sip:[^@\s]+@[^@\s]+", value):
                raise ValueError(f"{label}账号格式应为 sip:用户名@域名，例如 sip:abc@sip2sip.info")

        # 内网目标允许留空（自动探测），非空时只收「主机名或 IP[:端口]」这种形态，
        # 免得有人把 sip: 前缀或空格塞进来，baresip 那边会当成非法 URI 直接静默失败。
        lan_target = (lan_target or "").strip()
        if lan_target and not re.fullmatch(r"[A-Za-z0-9.\-]{1,64}(:\d{1,5})?", lan_target):
            raise ValueError("内网直呼目标应形如 10.0.0.5 或 10.0.0.5:5060（留空=自动探测）")

        updates: Dict[str, Dict[str, Any]] = {
            "wake": {
                "enabled": bool(wake_enabled),
            },
            "sip": {
                "enabled": bool(sip_enabled),
                "caller_aor": caller_aor,
                "callee_aor": callee_aor,
                "ring_seconds": ring_seconds,
                "retry_times": retry_times,
                "lan_call_enabled": bool(lan_call_enabled),
                "lan_target": lan_target,
                "lan_scan_enabled": bool(lan_scan_enabled),
                "lan_fallback_public": bool(lan_fallback_public),
                "lan_subnet_scan": bool(lan_subnet_scan),
            },
        }
        # 前缀只在页面真的传了合法值时才改，避免旧页面把用户调好的 /24 冲回默认。
        if type(lan_subnet_prefix) is int and 16 <= lan_subnet_prefix <= 24:
            updates["sip"]["lan_subnet_prefix"] = lan_subnet_prefix
        # 密码留空 = 保持原样，避免页面上明文来回传。
        if caller_pass.strip():
            updates["sip"]["caller_pass"] = caller_pass.strip()
        # TTS 的细节字段由「语音合成」卡片自己的保存按钮负责，这里只同步后端与 edge 音色，
        # 免得两个按钮互相覆盖对方刚填的值。
        if tts_backend:
            updates["tts"] = {"backend": tts_backend}
            if tts_voice.strip():
                updates["tts"]["edge_voice"] = tts_voice.strip()
        self._write_config(updates)
        self._apply_to_memory(updates)

        # 旧页面兼容收尾：升级前的 HTML 只有一个时间，改时间发的是 hour/minute。
        # 落到第一个启用任务上，免得「在旧页面改了时间却什么都没发生」。
        moved = ""
        if 0 <= hour <= 23 and 0 <= minute <= 59 and self.config.jobs:
            target = next((j for j in self.config.jobs if j.enabled), self.config.jobs[0])
            if (target.hour, target.minute) != (hour, minute):
                target.hour = hour
                target.minute = minute
                self._write_jobs(self.config.jobs)
                moved = f"{target.label or target.id} → {hour:02d}:{minute:02d}"

        await self._stop_timer()
        self._restart_timer()
        self.ctx.logger.info(
            "侧边栏保存配置: enabled=%s 任务=%d 主叫=%s 被叫=%s 页面提交(主叫=%r 被叫=%r) 密码=%s%s",
            wake_enabled,
            len(self.config.jobs),
            caller_aor or "(空)",
            callee_aor or "(空)",
            page_caller,
            page_callee,
            "已更新" if caller_pass.strip() else "未改动",
            f" 旧版页面改了时间({moved})" if moved else "",
        )
        return {"saved": True, "wake_enabled": bool(wake_enabled), "next_at": self._next_at_text()}

    @API(
        "webui_save_jobs",
        description="保存整个任务列表（新增/改名/改时间/改提示词/删除），payload 是 JSON 数组字符串",
        version="1",
    )
    async def webui_save_jobs(self, payload: str = "") -> Dict[str, Any]:
        if self._busy:
            raise ValueError("正在拨打中，等这一通结束再改任务")
        raw = (payload or "").strip()
        if not raw:
            raise ValueError("没有收到任务数据")
        try:
            items = json.loads(raw)
        except Exception as exc:  # noqa: BLE001
            raise ValueError(f"任务数据不是合法 JSON: {exc}") from exc
        if not isinstance(items, list):
            raise ValueError("任务数据应该是数组")
        if len(items) > MAX_JOBS:
            raise ValueError(f"最多 {MAX_JOBS} 个任务，现在给了 {len(items)} 个")

        jobs: list[JobSection] = []
        seen: set[str] = set()
        for index, item in enumerate(items, 1):
            if not isinstance(item, dict):
                raise ValueError(f"第 {index} 个任务格式不对")
            label = str(item.get("label") or "").strip()[:20] or f"任务{index}"
            hour = item.get("hour")
            minute = item.get("minute")
            if type(hour) is not int or not 0 <= hour <= 23:
                raise ValueError(f"「{label}」的小时要填 0-23")
            if type(minute) is not int or not 0 <= minute <= 59:
                raise ValueError(f"「{label}」的分钟要填 0-59")
            catch_up = item.get("catch_up_minutes", 30)
            if type(catch_up) is not int or not 0 <= catch_up <= 720:
                raise ValueError(f"「{label}」的补打宽限要填 0-720 分钟")
            max_chars = item.get("max_chars", self.config.wake.max_chars)
            if type(max_chars) is not int or not 10 <= max_chars <= 200:
                raise ValueError(f"「{label}」的字数上限要填 10-200")
            intent = str(item.get("intent") or "").strip()
            if not intent:
                intent = DEFAULT_INTENT
            if len(intent) > 2000:
                raise ValueError(f"「{label}」的提示词太长了，控制在 2000 字以内")
            jid = str(item.get("id") or "").strip()[:16]
            if not jid or jid in seen:
                jid = f"job{int(time.time())}{index}"
            seen.add(jid)
            jobs.append(
                JobSection(
                    id=jid,
                    label=label,
                    enabled=bool(item.get("enabled", True)),
                    hour=hour,
                    minute=minute,
                    catch_up_minutes=catch_up,
                    max_chars=max_chars,
                    intent=intent,
                    llm_task=str(item.get("llm_task") or "").strip()[:40],
                )
            )

        if not jobs:
            raise ValueError("至少要留一个任务；只想停掉就关掉它的开关，或者关掉总开关")

        self.config.jobs = jobs
        self._write_jobs(jobs)
        # 删掉的任务，它在 state.json 里的记录也一起清掉，免得以后同名任务接上旧记录。
        stale = [jid for jid in (self._state.get("jobs") or {}) if jid not in seen]
        if stale:
            for jid in stale:
                self._state["jobs"].pop(jid, None)
            self._save_state()

        await self._stop_timer()
        self._restart_timer()
        self.ctx.logger.info(
            "侧边栏保存任务: %d 个 → %s",
            len(jobs),
            "；".join(f"{j.label} {j.hour:02d}:{j.minute:02d}{'' if j.enabled else '(停用)'}" for j in jobs),
        )
        return {
            "saved": True,
            "count": len(jobs),
            "jobs": [self._job_public(job) for job in jobs],
            "next_at": self._next_at_text(),
        }

    @API(
        "webui_save_persona",
        description="保存语音人设：切换跟随/独立，写入插件内人设全文（不影响 MaiBot 自己的人设）",
        version="1",
    )
    async def webui_save_persona(
        self, source: str = "", text: str = "", first_paragraph_only: bool = True
    ) -> Dict[str, Any]:
        source = (source or "").strip().lower()
        if source and source not in {"follow", "custom"}:
            raise ValueError("人设来源只能是 follow（跟随设置）或 custom（插件内独立）")
        body = (text or "").replace("\r\n", "\n").replace("\r", "\n").strip()
        if len(body) > PERSONA_INJECT_LIMIT * 2:
            raise ValueError(f"人设太长了（{len(body)} 字），控制在 {PERSONA_INJECT_LIMIT * 2} 字以内")
        if source == "custom" and not body:
            raise ValueError("选了「插件内人设」就不能留空；想回到跟随设置就把来源切回 follow")

        updates: Dict[str, Any] = {"text": body, "first_paragraph_only": bool(first_paragraph_only)}
        if source:
            updates["source"] = source
        # 手动存过一次就算初始化过了，以后启动不再被自动快照覆盖。
        updates["initialized"] = True
        self._stash_persona()
        self._write_config({"persona": updates})
        self._apply_to_memory({"persona": updates})
        self.ctx.logger.info(
            "侧边栏保存人设: source=%s 插件内=%d 字 跟随首段=%s",
            self._persona_source(),
            len(body),
            bool(first_paragraph_only),
        )
        return {"saved": True, "persona": self._persona_public()}

    def _stash_persona(self) -> None:
        """覆盖前先把现在这份存起来。

        人设是纯手写内容，改短了、粘错了没法从别处找回；
        留一版在 state.json 里，页面就能「恢复上一版」。
        """
        old = (self.config.persona.text or "").strip()
        if not old:
            return
        prev = self._state.get("persona_prev") or {}
        if str(prev.get("text") or "").strip() == old:
            return
        self._state["persona_prev"] = {
            "text": old,
            "at": datetime.now().isoformat(timespec="seconds"),
        }
        self._save_state()

    @API(
        "webui_persona_restore",
        description="把上一次被覆盖掉的语音人设换回来（再点一次可换回去）",
        version="1",
    )
    async def webui_persona_restore(self) -> Dict[str, Any]:
        prev = self._state.get("persona_prev") or {}
        text = str(prev.get("text") or "")
        if not text.strip():
            raise ValueError("没有可恢复的上一版人设；这个功能只保留最近一版")
        current = (self.config.persona.text or "").strip()
        updates: Dict[str, Any] = {"text": text, "initialized": True}
        if not (self.config.persona.source or "").strip():
            updates["source"] = "custom"
        # 先换手，再写盘：这样连点两次就是「切回来 / 再切回去」。
        self._state["persona_prev"] = {
            "text": current,
            "at": datetime.now().isoformat(timespec="seconds"),
        }
        self._save_state()
        self._write_config({"persona": updates})
        self._apply_to_memory({"persona": updates})
        self.ctx.logger.info("已恢复上一版人设: %d 字", len(text))
        return {"restored": True, "len": len(text), "persona": self._persona_public()}

    @API(
        "webui_persona_import",
        description="把 MaiBot 设置里的当前人设全文导入插件人设栏位；apply=false 时只看不写",
        version="1",
    )
    async def webui_persona_import(self, apply: bool = True) -> Dict[str, Any]:
        raw = self._bot_persona_raw()
        if not raw:
            return {
                "ok": False,
                "applied": False,
                "bot_len": 0,
                "error": "在 MaiBot 的 bot_config.toml 里没找到人设，先去设置里写上再导入",
            }
        if not apply:
            return {"ok": True, "applied": False, "bot_len": len(raw), "preview": raw[:600]}
        updates: Dict[str, Any] = {
            "text": raw,
            "initialized": True,
            "synced_at": datetime.now().isoformat(timespec="seconds"),
        }
        self._stash_persona()
        self._write_config({"persona": updates})
        self._apply_to_memory({"persona": updates})
        self.ctx.logger.info("从 MaiBot 设置导入人设全文: %d 字", len(raw))
        return {"ok": True, "applied": True, "bot_len": len(raw), "persona": self._persona_public()}

    @API(
        "webui_save_tts",
        description="保存语音合成配置：切换后端、填各家密钥与音色（密钥留空表示保持原值）",
        version="1",
    )
    async def webui_save_tts(
        self,
        backend: str = "",
        timeout: int = 0,
        edge_voice: str = "",
        edge_rate: str = "",
        openai_url: str = "",
        openai_key: str = "",
        openai_model: str = "",
        openai_voice: str = "",
        minimax_url: str = "",
        minimax_key: str = "",
        minimax_group_id: str = "",
        minimax_model: str = "",
        minimax_voice: str = "",
        doubao_api: str = "",
        doubao_url: str = "",
        doubao_app_id: str = "",
        doubao_token: str = "",
        doubao_cluster: str = "",
        doubao_resource_id: str = "",
        doubao_voice: str = "",
    ) -> Dict[str, Any]:
        backend = (backend or "").strip().lower()
        if backend and backend not in {"edge", "openai", "minimax", "doubao"}:
            raise ValueError("语音后端只能是 edge / openai / minimax / doubao")
        if timeout and (type(timeout) is not int or not 5 <= timeout <= 120):
            raise ValueError("合成超时必须留空或填 5-120 秒")
        for label, value in (
            ("openai_url", openai_url),
            ("minimax_url", minimax_url),
            ("doubao_url", doubao_url),
        ):
            if value.strip() and not re.match(r"^https?://", value.strip()):
                raise ValueError(f"{label} 必须以 http:// 或 https:// 开头")

        # 传了哪个键就改哪个，空值一律视为"保持原值"，避免页面没填完就把已有配置清掉。
        values: Dict[str, Any] = {
            "edge_voice": edge_voice,
            "edge_rate": edge_rate,
            "openai_url": openai_url,
            "openai_model": openai_model,
            "openai_voice": openai_voice,
            "minimax_url": minimax_url,
            "minimax_group_id": minimax_group_id,
            "minimax_model": minimax_model,
            "minimax_voice": minimax_voice,
            "doubao_api": doubao_api,
            "doubao_url": doubao_url,
            "doubao_app_id": doubao_app_id,
            "doubao_cluster": doubao_cluster,
            "doubao_resource_id": doubao_resource_id,
            "doubao_voice": doubao_voice,
        }
        updates: Dict[str, Any] = {k: v.strip() for k, v in values.items() if str(v).strip()}
        if backend:
            updates["backend"] = backend
        if timeout:
            updates["timeout"] = int(timeout)
        # 密钥同样"留空不改"，页面上永远不回明文。
        for key, value in (("openai_key", openai_key), ("minimax_key", minimax_key), ("doubao_token", doubao_token)):
            if value.strip():
                updates[key] = value.strip()

        self._write_config({"tts": updates})
        self._apply_to_memory({"tts": updates})
        # 切后端后旧的 raw.* 可能后缀不同，清掉避免下次 ffmpeg 读错文件。
        with contextlib.suppress(Exception):
            for old in self._audio_dir().glob("raw.*"):
                old.unlink()
        self.ctx.logger.info(
            "侧边栏保存语音配置: backend=%s 已填字段=%d", self.config.tts.backend, len(updates)
        )
        return {"saved": True, "backend": self.config.tts.backend, "tts": self._tts_public()}

    @API(
        "webui_save_guard",
        description="保存台词守门设置：总开关、合成前字数上限、禁用词表、备用台词池",
        version="1",
    )
    async def webui_save_guard(
        self,
        enabled: bool = True,
        max_chars: int = 80,
        ban_words: str = "",
        fallback_lines: str = "",
    ) -> Dict[str, Any]:
        if type(max_chars) is not int or not 10 <= max_chars <= 300:
            raise ValueError("合成前字数上限必须是 10-300")
        # 这里不用「留空就不改」：页面会把当前值回填进输入框，
        # 用户清空 = 明确表示「回到内置默认」，所以空值要真的写进去。
        words = re.sub(r"\r\n?", "\n", ban_words or "").strip()[:6000]
        lines = re.sub(r"\r\n?", "\n", fallback_lines or "").strip()[:6000]

        updates: Dict[str, Any] = {
            "enabled": bool(enabled),
            "max_chars": int(max_chars),
            "ban_words": words,
            "fallback_lines": lines,
        }
        self._write_config({"guard": updates})
        self._apply_to_memory({"guard": updates})
        self.ctx.logger.info(
            "侧边栏保存台词守门: 启用=%s 字数上限=%s 禁用词=%s 备用台词=%s",
            bool(enabled),
            int(max_chars),
            "自定义 %d 个" % len(self._ban_words()) if words else "内置 %d 个" % len(DEFAULT_BAN_WORDS),
            "%d 句（自定义）" % len(self._fallback_pool()) if lines else "%d 句（内置）" % len(DEFAULT_FALLBACK_LINES),
        )
        return {"saved": True, "guard": self._guard_public()}

    @API(
        "webui_tts_preview",
        description="用指定后端合成一句试听音频（12 秒、8k 单声道），返回 base64 供页面直接播放",
        version="1",
    )
    async def webui_tts_preview(self, backend: str = "", text: str = "") -> Dict[str, Any]:
        import base64

        if self._busy:
            raise ValueError("正在拨打中，等这一通结束再试听")
        if getattr(self, "_previewing", False):
            raise ValueError("上一次试听还在合成，等它出结果再点")
        want = (backend or "").strip().lower()
        if want and want not in {"edge", "openai", "minimax", "doubao"}:
            raise ValueError("后端只能是 edge / openai / minimax / doubao")
        sample = re.sub(r"\s+", "", (text or "")).strip()[:80] or "主人，八点啦，该起床咯。"

        tts = self.config.tts
        saved = (tts.backend or "edge").strip().lower()
        chosen = want or saved
        # 每次试听独占一个子目录：以前固定写 preview/raw.* + preview.mp3，
        # 连点两下或和定时任务撞车时会互相覆盖，听到的可能是上一句。
        pdir = self._audio_dir() / "preview" / uuid.uuid4().hex[:8]
        pdir.mkdir(parents=True, exist_ok=True)
        started = time.monotonic()
        self._previewing = True
        try:
            raw = pdir / f"raw.{self._tts_format(chosen)}"
            await self._tts_generate(sample, raw, chosen)
            wav = pdir / "preview.mp3"
            await self._to_wav(raw, wav, seconds=10, loop=False, fmt="mp3")
            blob = wav.read_bytes()
        except Exception as exc:  # noqa: BLE001 - 各家错误都原样带给页面
            message = str(exc) or repr(exc)
            self._state["last_preview"] = f"失败({chosen}): {message}"[:200]
            self._save_state()
            self.ctx.logger.warning("TTS 试听失败 backend=%s: %s", chosen, message)
            return {"ok": False, "error": message, "backend": chosen}
        finally:
            self._previewing = False
            shutil.rmtree(pdir, ignore_errors=True)

        elapsed = round(time.monotonic() - started, 2)
        b64 = base64.b64encode(blob).decode()
        self._state["last_preview"] = f"成功({chosen}) {elapsed}s {len(blob) // 1024}KB"
        self._save_state()
        return {
            "ok": True,
            "backend": chosen,
            "text": sample,
            "elapsed": elapsed,
            "bytes": len(blob),
            "audio": f"data:audio/mpeg;base64,{b64}",
        }

    @API("webui_test_call", description="按当前配置立即试拨一次电话，不占用定时次数", version="1")
    async def webui_test_call(
        self, use_model: bool = False, ring_seconds: int = 30, job_id: str = ""
    ) -> Dict[str, Any]:
        if self._busy:
            raise ValueError("正在拨打中，请等这一通结束")
        sip = self.config.sip
        missing = [
            label
            for label, value in (
                ("主叫账号", sip.caller_aor),
                ("主叫密码", sip.caller_pass),
                ("被叫账号", sip.callee_aor),
            )
            if not str(value).strip()
        ]
        if missing:
            raise ValueError("还缺 " + "、".join(missing) + "，先在下面填好并保存")
        if type(ring_seconds) is not int or not 10 <= ring_seconds <= 120:
            raise ValueError("试拨时长必须是 10-120 秒")

        job = self._find_job(job_id)
        if use_model and job is None:
            raise ValueError("要用这个任务自己的提示词试拨，得先带上任务")

        self._busy = True
        try:
            if use_model:
                text = await self._gen_text(job)
                # 和定时拨号同一条规则：守门开着时，空台词改说备用台词照常拨，
                # 而不是甩一句「模型没生成出台词」让用户再去点一次。
                if not text and not bool(self.config.guard.enabled):
                    raise ValueError("模型没有生成出台词，可以关掉「顺带生成新台词」再试")
                # 试拨同样花钱，同样要过守门，否则「试一次」就能把额度试光。
                text, guard_note = self._guard_text(text, job)
                if guard_note:
                    self.ctx.logger.warning("试拨台词守门：%s", guard_note)
            else:
                text = "喂，测试一下，能听见我说话吗？"
            # 试拨固定用 edge：只为验证「通不通、响不响」，不必动正式后端。
            # 这样打完测试电话不用再改回去，也不会和定时任务抢配置。
            self.ctx.logger.info(
                "试拨用 edge 合成（当前正式后端 %s，本次不改配置）",
                (self.config.tts.backend or "edge"),
            )
            wav = await self._synthesize(text, self._audio_dir(), "edge")
            error = await self._dial(wav, ring_seconds)
        finally:
            self._busy = False

        self._state["last_test_at"] = datetime.now().isoformat(timespec="seconds")
        if job is not None:
            state = self._job_state(job.id)
            state["last_text"] = text
            state["last_result"] = "试拨成功" if not error else f"试拨失败: {error}"
            state["last_error"] = error
        else:
            self._state["last_text"] = text
            self._state["last_result"] = "试拨成功" if not error else f"试拨失败: {error}"
            self._state["last_error"] = error
        self._save_state()
        return {
            "ok": not error,
            "error": error,
            "text": text,
            "ring_seconds": ring_seconds,
            "job": (job.label if job else ""),
            "hint": self._dial_hint(error),
            # 失败时页面上直接给路径，不用再回来问「日志在哪」。
            "log": str(getattr(self, "_last_dial_log", "") or ""),
        }

    def _find_job(self, job_id: str) -> Optional[JobSection]:
        key = (job_id or "").strip()
        if not key:
            return None
        for job in self.config.jobs:
            if job.id == key:
                return job
        return None

    @staticmethod
    def _dial_hint(error: str) -> str:
        if not error:
            return ""
        if "110" in error or "推送" in error:
            return (
                "Flexisip 判定手机要靠推送唤醒，所以没有把呼叫直送过去。"
                "去 Linphone 里把这个账号的「推送通知 / Use push notifications」关掉，"
                "让它以后台常驻方式注册，呼叫会直接到达并立刻响铃。"
            )
        if "180" in error:
            return "手机确实响了，链路完全通。只是这段时间没人接，可以调长单次通话时长再试。"
        if "没有任何应答" in error:
            return (
                "主叫和被叫账号都正常、呼叫也送出去了，但手机上一个应答都没有。按这个顺序查："
                "① 最常见也最隐蔽：Linphone 设置 → 通话 → 高级通话设置 →「强制媒体加密」，"
                "把它关掉。Linphone 6 默认开启它，而 baresip 发的是明文音频，"
                "会被当场判为不安全直接丢弃——表现就是手机上有未接记录但完全不响、不弹界面；"
                "② 确认手机上登录的是被叫那个账号；"
                "③ 设置 → 高级设置 → 确认「使用服务使应用程序保持活动状态」和「设备启动时启动」都开着；"
                "④ 系统里给 Linphone 允许自启动、电池不限制。"
            )
        if "403" in error or "407" in error:
            return "密码不对。去 subscribe.linphone.org 确认主叫账号的 SIP 密码，注意不是邮箱密码。"
        if "注册失败" in error:
            return "主叫账号没登上服务器，先确认 sip.linphone.org 能连通、账号密码正确。"
        return "手机没响就检查：Linphone 是否已登录并保持后台、有没有被系统杀掉、被叫地址有没有写错。"

    @API(
        "webui_reset_state",
        description="清空今日已拨记录，让定时器今天可以再拨一次；带 job_id 只清那个任务",
        version="1",
    )
    async def webui_reset_state(self, job_id: str = "") -> Dict[str, Any]:
        states = self._state.get("jobs") or {}
        target = (job_id or "").strip()
        if target:
            states.pop(target, None)
        else:
            states.clear()
        # 一并清掉 0.1.x 留下的顶层记录。
        for key in ("last_fired_date", "last_fired_at", "attempts", "skipped_date"):
            self._state.pop(key, None)
        self._save_state()
        self.ctx.logger.info("已清空今日拨打记录: %s", target or "全部任务")
        return {"reset": True, "scope": target or "all"}

    # ──── 配置文件读改写 ────

    def _next_at_for(self, job: "JobSection") -> str:
        """下次真正会响的时间。

        必须复用 `_due_for()` 的到期判断：跨零点补拨窗口里还欠着昨天那一通时，
        按 `now.replace(hour=...)` 算出来的是**今晚**的时间点，比 now 大，
        侧栏就会显示「下次 23:50」，看着像今天这通已经响过了。
        """
        now = datetime.now()
        due, fire_date, _missed = self._due_for(job, now)
        if due is not None:
            fired = self._job_state(job.id).get("last_fired_date") == fire_date
            if not fired and self._attempts_today(fire_date, job.id) < MAX_ATTEMPTS:
                return due.isoformat(timespec="minutes")
        nxt = now.replace(hour=job.hour, minute=job.minute, second=0, microsecond=0)
        today = now.strftime("%Y-%m-%d")
        if nxt <= now or self._job_state(job.id).get("last_fired_date") == today:
            nxt += timedelta(days=1)
        return nxt.isoformat(timespec="minutes")

    def _next_at_text(self) -> str:
        jobs = [j for j in self.config.jobs if j.enabled]
        if not jobs:
            return ""
        soon = min(jobs, key=self._next_at_for)
        return f"{self._next_at_for(soon)}（{soon.label or soon.id}）"

    def _job_public(self, job: "JobSection") -> Dict[str, Any]:
        today = datetime.now().strftime("%Y-%m-%d")
        state = self._job_state(job.id)
        fired_today = state.get("last_fired_date") == today
        # 拨成功了 attempts 会被清掉，但页面上「今日已拨 1 次」比「0 次」更符合直觉。
        attempts = self._attempts_today(today, job.id) or (1 if fired_today else 0)
        return {
            "id": job.id,
            "label": job.label,
            "enabled": bool(job.enabled),
            "hour": int(job.hour),
            "minute": int(job.minute),
            "catch_up_minutes": int(job.catch_up_minutes),
            "max_chars": int(job.max_chars),
            "intent": job.intent,
            "llm_task": job.llm_task,
            "default_intent": DEFAULT_INTENT,
            "next_at": self._next_at_for(job),
            "last_fired_at": state.get("last_fired_at") or "",
            "last_text": state.get("last_text") or "",
            "last_guard": state.get("last_guard") or "",
            "last_result": state.get("last_result") or "",
            "last_error": state.get("last_error") or "",
            "attempts_today": attempts,
            "fired_today": fired_today,
            "last_dial_log": str(getattr(self, "_last_dial_log", "") or ""),
        }

    def _ensure_jobs(self) -> None:
        """一个任务都没有时，把 0.1.x 的单任务配置迁移成第一个任务。"""
        if self.config.jobs:
            return
        wake = self.config.wake
        job = JobSection(
            id="morning",
            label="叫起床",
            enabled=True,
            hour=int(wake.hour),
            minute=int(wake.minute),
            catch_up_minutes=int(wake.catch_up_minutes),
            max_chars=int(wake.max_chars),
            intent=(wake.intent or DEFAULT_INTENT).strip(),
            llm_task="",
        )
        self.config.jobs = [job]
        try:
            self._write_jobs(self.config.jobs)
        except Exception:  # noqa: BLE001 - 落盘失败不该拦住叫醒
            self.ctx.logger.warning("写入任务列表失败，本次只在内存生效", exc_info=True)
        self.ctx.logger.info("没有任务，已按旧配置生成「%s」%02d:%02d", job.label, job.hour, job.minute)

    def _write_jobs(self, jobs: list) -> None:
        """整块重写 config.toml 里的 [[jobs]]，删掉的任务不会留下残片。"""
        path = self._config_file()
        text = path.read_text(encoding="utf-8") if path.exists() else ""
        lines = text.splitlines()

        start: Optional[int] = None
        for i, line in enumerate(lines):
            if line.strip() == "[[jobs]]":
                start = i
                break
        end = len(lines)
        if start is not None:
            for i in range(start + 1, len(lines)):
                stripped = lines[i].strip()
                if stripped.startswith("[") and stripped != "[[jobs]]":
                    end = i
                    break

        block: list[str] = []
        for job in jobs:
            block.append("[[jobs]]")
            block.append("")
            for key in (
                "id",
                "label",
                "enabled",
                "hour",
                "minute",
                "catch_up_minutes",
                "max_chars",
                "intent",
                "llm_task",
            ):
                block.append(f"{key} = {self._render_toml(getattr(job, key))}")
            block.append("")

        if start is None:
            if lines and lines[-1].strip():
                lines.append("")
            lines.extend(block)
        else:
            lines[start:end] = block
        # 同 _write_config：半截 TOML = 插件加载失败，必须原子替换。
        tmp = path.with_suffix(path.suffix + ".tmp")
        tmp.write_text("\n".join(lines).rstrip("\n") + "\n", encoding="utf-8")
        os.replace(tmp, path)

    def _config_file(self) -> Path:
        return Path(__file__).resolve().parent / "config.toml"

    def _write_config(self, updates: Dict[str, Dict[str, Any]]) -> None:
        path = self._config_file()
        text = path.read_text(encoding="utf-8") if path.exists() else ""
        for section, values in updates.items():
            for key, value in values.items():
                text = self._set_toml_value(text, section, key, value)
        # 和 state.json 一样必须原子写：config.toml 被写成半截就是 TOML 解析失败，
        # 那是整个插件加载不起来（比丢一条设置严重得多）。proot 里 OOM 是常态。
        tmp = path.with_suffix(path.suffix + ".tmp")
        tmp.write_text(text, encoding="utf-8")
        os.replace(tmp, path)

    @staticmethod
    def _set_toml_value(text: str, section: str, key: str, value: Any) -> str:
        lines = text.splitlines()
        header = f"[{section}]"
        start = next((i for i, line in enumerate(lines) if line.strip() == header), None)
        rendered = f"{key} = {WakeCallPlugin._render_toml(value)}"
        if start is None:
            if lines and lines[-1].strip():
                lines.append("")
            lines.extend([header, "", rendered])
            return "\n".join(lines) + "\n"

        end = len(lines)
        for i in range(start + 1, len(lines)):
            stripped = lines[i].strip()
            if stripped.startswith("[") and stripped.endswith("]"):
                end = i
                break
        pattern = re.compile(rf"^\s*{re.escape(key)}\s*=")
        for i in range(start + 1, end):
            if pattern.match(lines[i]):
                lines[i] = rendered
                return "\n".join(lines) + "\n"
        lines.insert(end, rendered)
        return "\n".join(lines) + "\n"

    @staticmethod
    def _render_toml(value: Any) -> str:
        if isinstance(value, bool):
            return "true" if value else "false"
        if isinstance(value, int):
            return str(value)
        # float 必须先判，否则会被 str() 包成带引号的字符串，重新解析时就类型不对了。
        if isinstance(value, float):
            return repr(value)
        return json.dumps(str(value), ensure_ascii=False)

    def _apply_to_memory(self, updates: Dict[str, Dict[str, Any]]) -> None:
        for section, values in updates.items():
            target = getattr(self.config, section, None)
            if target is None:
                continue
            for key, value in values.items():
                with contextlib.suppress(Exception):
                    setattr(target, key, value)

    @staticmethod
    def _normalize_aor(raw: str) -> str:
        value = (raw or "").strip()
        if not value:
            return ""
        if not value.lower().startswith("sip:"):
            value = "sip:" + value
        return value


def create_plugin() -> WakeCallPlugin:
    return WakeCallPlugin()
