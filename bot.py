import asyncio
import html
import json
import logging
import math
import os
import random
import re
import secrets
import shutil
import threading
import time
from collections import defaultdict
from contextlib import asynccontextmanager
from datetime import datetime, timedelta, timezone
from http.server import BaseHTTPRequestHandler, HTTPServer, ThreadingHTTPServer
from urllib.parse import parse_qs, quote, urlparse

from telegram import BotCommand, InlineKeyboardButton, InlineKeyboardMarkup, InputMediaPhoto, Update, ChatPermissions
from telegram.error import BadRequest, RetryAfter, TelegramError
from telegram.ext import Application, CallbackQueryHandler, ChatJoinRequestHandler, ChatMemberHandler, MessageHandler, filters
from treys import Card, Evaluator

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
logger = logging.getLogger(__name__)

# ---------- 全局配置中心 ----------
GAME_STARTING_CHIPS = 50000  # 统一积分初始值（首次使用自动获得）

MIN_ENTRY_CHIPS = 200
EMERGENCY_CHIPS = 2000
EMERGENCY_MAX_USES = 3

# 游戏时间配置 (秒)
TURN_TIMEOUT = 60          # 德州/21点单回合思考时间
ROOM_WAIT_TIMEOUT = 60     # 各游戏等待房统一倒计时（60秒）
RACE_AUTO_START = 120      # 赛车自动开赛时间
RACE_ANIMATION_INTERVAL = 5.0   # 每帧画面停留秒数（间隔越大帧数越少，需与赛程总时长一起权衡）

# 游戏金额配置
BJ_MIN_BET = 100           # 21点最低打字下注
BJ_JOIN_BETS = [500, 1000] # 21点加入下注按钮档位（网页可改）
FIXED_MIN_RAISE = 100      # 德州最低加注额
BLACKJACK_DECKS = 6        # 21点使用6副牌（娱乐场标准）

# 其他配置
DEFAULT_ADMIN = 8929733838
ADMIN_USER_ID = int(os.environ.get("ADMIN_USER_ID", DEFAULT_ADMIN))
# Bot 管理员：种子集合（始终为管理员，防锁死）+ 可动态增删的持久化集合
ADMIN_USER_IDS = {ADMIN_USER_ID}  # 种子管理员，重启后自动恢复，无法被 /deladmin 移除
BOT_ADMINS = set(ADMIN_USER_IDS)  # 运行时管理员集合 = 种子 ∪ 持久化新增，可经 /addadmin /deladmin 动态管理
SMALL_BLIND, BIG_BLIND, ANTE = 0, 0, 200
STALE_TEXT_COMMAND_SECONDS = 120
# ---------- 德州排位赛 ----------
SEASON_START_CHIPS = 20000     # 排位赛起始分（独立账本，7天不清零）
SEASON_MIN_PLAYERS = 20        # 报名满 20 人自动开赛
SEASON_MIN_GAMES = 5           # 上榜最少局数
SEASON_REBUY_COUNT = 3         # 破产应急补分次数
SEASON_REBUY_AMOUNT = 2000     # 每次应急补分
SEASON_DAYS = 7                # 赛季周期（天）
SEASON_BET_PERCENT = 0.2       # 排位赛单局每人投入上限 = 本局落座玩家筹码总和 × 此比例（人少上限低，防串通）
# 自适应数据持久化路径：HF Spaces 开启持久化(/data 存在)→用 /data；否则用当前目录(Serv00/本地均为真实磁盘，持久)
_data_candidates = [
    os.environ.get("DATA_FILE"),
    "/data/bot_data.json" if os.path.isdir("/data") else None,
    "bot_data.json",
    os.path.join(os.path.expanduser("~"), "bot_data.json"),
]
DATA_FILE = next((p for p in _data_candidates if p), "bot_data.json")
# --------------------------------

# ---------- 赛车/德州常量 ----------
HORSE_COUNT = 4
HORSE_NAMES = ["轿车", "出租", "越野", "皮卡"]
HORSE_EMOJI = ["🚗", "🚕", "🚙", "🛻"]
FIXED_BET_AMOUNTS = [100, 200, 500, 1000]
RACE_TRACK_LENGTH = 14
DATA_BACKUP_FILE, DATA_TEMP_FILE = f"{DATA_FILE}.bak", f"{DATA_FILE}.tmp"

# ---------- 网页后台：可在线调整的设置 ----------
# 设置存在独立文件 bot_settings.json，网页保存后立即覆盖内存中的全局常量，无需重启。
SETTINGS_FILE = os.path.join(os.path.dirname(os.path.abspath(DATA_FILE)), "bot_settings.json")
WEB_DEFAULT_PASSWORD = "admin888"  # 首次登录用，登录后请在面板里立即修改
# 左侧菜单分组：(分组键, 显示名, 图标)
SETTINGS_GROUPS = [
    ("dashboard", "群体总览",   "📊"),
    ("texas",     "德州扑克",   "🃏"),
    ("blackjack", "21点",      "♠️"),
    ("jinhua",    "炸金花",     "♣️"),
    ("race",      "赛车",       "🏎️"),
    ("general",   "通用与应急", "⚙️"),
    ("season",    "排位赛",     "🏆"),
    ("points",    "积分系统",   "💰"),
    ("members",   "群组管理",   "👥"),
    ("admin",     "管理员中心", "🛡️"),
    ("security",  "安全",       "🔒"),
]
# 子页面制：有子页的分组在侧边栏折叠展开（照阿福模板）。None=未开通占位页
SUBPAGES = {
    "points": [
        ("set",      "积分设置"),
        ("adjust",   "积分管理"),
        ("cap",      "积分每日上限"),
        ("sign",     "每日签到"),
        ("rule",     "积分规则"),
        ("rp",       "积分红包"),
        ("level",    "积分等级"),
        ("inherit",  "积分继承"),
        ("auction",  "积分拍卖"),
        ("mall",     "积分商城"),
        ("buy",      "购买积分"),
    ],
    "admin": [
        ("auth",      "授权群管理"),
        ("blacklist", "拉黑管理"),
        ("god",       "赌神称号"),
        ("seasonpts", "排位分调整"),
        ("orders",    "商城订单"),
    ],
}
SETTINGS_FIELDS = [
    # (settings键, 模块全局变量名, 面板显示名, 类型, 最小, 最大, 所属分组)
    ("min_entry_chips",         "MIN_ENTRY_CHIPS",         "入座最低积分",              "int",   0,   100000,  "texas"),
    ("fixed_min_raise",         "FIXED_MIN_RAISE",         "最低加注额",                "int",   10,  10000,   "texas"),
    ("turn_timeout",            "TURN_TIMEOUT",            "单回合思考时间(秒·德州/21点共用)", "int", 10, 600, "texas"),
    ("room_wait_timeout",       "ROOM_WAIT_TIMEOUT",       "等待房倒计时(秒)",          "int",   10,  600,     "texas"),
    ("bj_min_bet",              "BJ_MIN_BET",              "最低下注",                  "int",   1,   100000,  "blackjack"),
    ("bj_join_bets",            "BJ_JOIN_BETS",            "加入下注按钮金额(逗号分隔)", "bets",  0,   0,       "blackjack"),
    ("blackjack_decks",         "BLACKJACK_DECKS",         "使用几副牌",                "int",   1,   8,       "blackjack"),
    ("jinhua_ante",             "JINHUA_ANTE",             "底注",                      "int",   1,   100000,  "jinhua"),
    ("jinhua_base",             "JINHUA_BASE",             "单注基准",                  "int",   1,   100000,  "jinhua"),
    ("race_auto_start",         "RACE_AUTO_START",         "自动开赛时间(秒)",          "int",   10,  600,     "race"),
    ("race_animation_interval", "RACE_ANIMATION_INTERVAL", "动画帧间隔(秒)",            "float", 0.5, 30,      "race"),
    ("horse_count",             "HORSE_COUNT",             "赛马数量(匹)",              "int",   2,   8,       "race"),
    ("horse_names",             "HORSE_NAMES",             "赛马名称(逗号分隔)",        "names", 0,   0,       "race"),
    ("horse_emoji",             "HORSE_EMOJI",             "赛马表情(逗号分隔)",        "emoji", 0,   0,       "race"),
    ("race_track_length",       "RACE_TRACK_LENGTH",       "赛道长度(格)",              "int",   5,   50,      "race"),
    ("fixed_bet_amounts",       "FIXED_BET_AMOUNTS",       "下注按钮金额(逗号分隔)",    "bets",  0,   0,       "race"),
    ("game_starting_chips",     "GAME_STARTING_CHIPS",     "新玩家初始积分(全游戏统一)", "int",  100, 1000000, "general"),
    ("small_blind",             "SMALL_BLIND",             "德州小盲注(0=不设盲注)",    "int",   0,   100000,  "general"),
    ("big_blind",               "BIG_BLIND",               "德州大盲注(0=不设盲注)",    "int",   0,   100000,  "general"),
    ("ante",                    "ANTE",                    "德州前注(每人发牌前强制投入)", "int", 0,  100000,  "general"),
    ("stale_text_command_seconds","STALE_TEXT_COMMAND_SECONDS","过期消息忽略(秒,防翻旧账命令)", "int", 5, 3600, "general"),
    ("emergency_chips",         "EMERGENCY_CHIPS",         "归零赠送积分",              "int",   0,   100000,  "general"),
    ("emergency_max_uses",      "EMERGENCY_MAX_USES",      "归零每日赠送次数",          "int",   0,   99,      "general"),
    ("season_start_chips",      "SEASON_START_CHIPS",      "每人起始分",                "int",   100, 1000000, "season"),
    ("season_min_players",      "SEASON_MIN_PLAYERS",      "最少开赛人数",              "int",   2,   50,      "season"),
    ("season_min_games",        "SEASON_MIN_GAMES",        "结算最少局数",              "int",   0,   999,     "season"),
    ("season_days",             "SEASON_DAYS",             "赛季天数",                  "int",   1,   90,      "season"),
    ("season_rebuy_count",      "SEASON_REBUY_COUNT",      "每日重买次数上限",          "int",   0,   20,      "season"),
    ("season_rebuy_amount",     "SEASON_REBUY_AMOUNT",     "每次重买金额",              "int",   0,   1000000, "season"),
    # ---------- 积分系统（子页面制：points/子页键，照阿福模板） ----------
    ("query_cmd",               "QUERY_CMD",               "查询积分指令(不带斜杠)",    "cmd",   0,   0,       "points/set"),
    ("rank_cmd",                "RANK_CMD",                "积分排行指令(不带斜杠)",    "cmd",   0,   0,       "points/set"),
    ("admin_adjust",            "ADMIN_ADJUST_ENABLED",    "管理员可增减积分",          "bool",  0,   1,       "points/set"),
    ("rank_1_emoji",            "RANK_1_EMOJI",            "积分排行第一名表情",        "short", 0,   0,       "points/set"),
    ("rank_2_emoji",            "RANK_2_EMOJI",            "积分排行第二名表情",        "short", 0,   0,       "points/set"),
    ("rank_3_emoji",            "RANK_3_EMOJI",            "积分排行第三名表情",        "short", 0,   0,       "points/set"),
    ("add_msg_tpl",             "ADD_MSG_TPL",             "添加积分提示消息",          "text",  0,   0,       "points/set"),
    ("query_msg_tpl",           "QUERY_MSG_TPL",           "查询积分消息",              "text",  0,   0,       "points/set"),
    ("chat_enabled",            "CHAT_ENABLED",            "聊天积分开关(需关机器人隐私模式)", "bool", 0, 1,    "points/set"),
    ("chat_chars_per",          "CHAT_CHARS_PER",          "每满N个字符记分",           "int",   1,   200,     "points/set"),
    ("chat_reward",             "CHAT_REWARD",             "每满N字符记几分",           "int",   1,   1000,    "points/set"),
    ("points_delete_seconds",   "POINTS_DELETE_SECONDS",   "查询指令删除时间(秒,0=不删)", "int", 0, 300,     "points/set"),
    ("chat_daily_cap",          "CHAT_DAILY_CAP",          "聊天积分每日上限(0=不限)",  "int",   0,   1000000, "points/cap"),
    ("sign_cmd",                "SIGN_CMD",                "签到指令(不带斜杠)",        "cmd",   0,   0,       "points/sign"),
    ("sign_enabled",            "SIGN_ENABLED",            "每日签到开关",              "bool",  0,   1,       "points/sign"),
    ("sign_base_reward",        "SIGN_BASE_REWARD",        "签到基础奖励",              "int",   0,   1000000, "points/sign"),
    ("sign_streak_bonus",       "SIGN_STREAK_BONUS",       "连续签到满7天额外奖励",     "int",   0,   1000000, "points/sign"),
    ("sign_msg_tpl",            "SIGN_MSG_TPL",            "签到成功消息",              "text",  0,   0,       "points/sign"),
    ("redpacket_enabled",       "REDPACKET_ENABLED",       "积分红包开关",              "bool",  0,   1,       "points/rp"),
    ("point_levels",            "POINT_LEVELS",            "积分等级表(每行 等级名:最低积分)", "levels", 0, 0,  "points/level"),
    ("mall_items",              "MALL_ITEMS",              "商城商品表(每行 商品名:价格)", "items", 0, 0,      "points/mall"),
    ("inherit_enabled",         "INHERIT_ENABLED",         "积分转赠(继承)开关",        "bool",  0,   1,       "points/inherit"),
    ("inherit_fee_percent",     "INHERIT_FEE_PERCENT",     "转赠手续费(%,0=无)",        "int",   0,   50,      "points/inherit"),
    ("auction_enabled",         "AUCTION_ENABLED",         "积分拍卖开关",              "bool",  0,   1,       "points/auction"),
    ("auction_step",            "AUCTION_STEP",            "每次加价幅度(积分)",        "int",   10,  100000,  "points/auction"),
    ("auction_duration",        "AUCTION_DURATION",        "拍卖时长(秒)",              "int",   30,  3600,    "points/auction"),
    ("buy_enabled",             "BUY_ENABLED",             "购买积分开关(管理员人工确认)", "bool", 0, 1,     "points/buy"),
    ("buy_min",                 "BUY_MIN",                 "单次最低购买数量",          "int",   100, 1000000, "points/buy"),
    ("buy_max",                 "BUY_MAX",                 "单次最高购买数量",          "int",   100, 10000000,"points/buy"),
]
_settings_lock = threading.Lock()
_web_password = WEB_DEFAULT_PASSWORD  # 运行时由 load_settings 覆盖

# ---------- 积分系统：运行时配置默认值（网页可改） ----------
SIGN_ENABLED = 1
SIGN_BASE_REWARD = 1000
SIGN_STREAK_BONUS = 500
CHAT_ENABLED = 1
CHAT_CHARS_PER = 5
CHAT_REWARD = 1
CHAT_DAILY_CAP = 500
POINTS_DELETE_SECONDS = 30
REDPACKET_ENABLED = 1
POINT_LEVELS = [{"name": "青铜", "value": 0}, {"name": "白银", "value": 5000}, {"name": "黄金", "value": 20000}, {"name": "铂金", "value": 50000}, {"name": "钻石", "value": 100000}]
MALL_ITEMS = []  # [{"name": 商品名, "value": 价格}]
INHERIT_ENABLED = 1
INHERIT_FEE_PERCENT = 0
AUCTION_ENABLED = 1
AUCTION_STEP = 100
AUCTION_DURATION = 60
BUY_ENABLED = 1
BUY_MIN = 1000
BUY_MAX = 100000
RANK_1_EMOJI = "🥇"
RANK_2_EMOJI = "🥈"
RANK_3_EMOJI = "🥉"
QUERY_CMD = "我的积分"
RANK_CMD = "积分排行"
SIGN_CMD = "签到"
ADMIN_ADJUST_ENABLED = 1
MSG_TPL_DEFAULTS = {
    "sign_msg_tpl": "🎉 {name} 签到成功！\n📅 连续签到 {streak} 天｜💰 +{reward}{bonus}\n💰 当前积分：{balance}",
    "query_msg_tpl": "💰 我的积分：{balance}\n{level_line}📅 今日签到：{signed}（连续 {streak} 天）\n💬 今日聊天获得：{today_chat}",
    "add_msg_tpl": "✅ 已给 {target} {verb} {amount} 积分，当前 {balance}。",
}
SIGN_MSG_TPL = MSG_TPL_DEFAULTS["sign_msg_tpl"]
QUERY_MSG_TPL = MSG_TPL_DEFAULTS["query_msg_tpl"]
ADD_MSG_TPL = MSG_TPL_DEFAULTS["add_msg_tpl"]

def _fmt_tpl(key, **kw):
    """按网页模板渲染消息；模板非法/为空时回退默认，绝不因占位符写错而崩。"""
    gname = next((g for k, g, *_r in SETTINGS_FIELDS if k == key), None)
    tpl = globals().get(gname) if gname else None
    fallback = MSG_TPL_DEFAULTS[key]
    try:
        return (tpl or fallback).format(**kw)
    except Exception:
        return fallback.format(**kw)

# 积分系统持久化数据（与主数据同一套脏标记/写盘/备份机制）
sign_data = defaultdict(lambda: defaultdict(dict))   # sign_data[cid][uid] = {"last": "YYYY-MM-DD", "streak": n}
chat_today = defaultdict(lambda: defaultdict(lambda: defaultdict(int)))  # chat_today[date][cid][uid] = 当日聊天已得积分
mall_orders = []                                     # [{"ts","cid","uid","name","item","price"}]
rp_packets = {}                                      # pid -> {"cid","from","left_amt","left_n","grabbed":{uid:amt},"ts","msg_id"}
auctions = {}                                        # cid -> {"item","price","top_uid","end_ts","msg_id","task"} 拍卖（托管竞得者积分）
buy_orders = {}                                      # oid -> {"cid","uid","amount","ts"} 购买积分申请（管理员人工确认）

# ---------- 群组管理数据 ----------
member_profiles = defaultdict(lambda: defaultdict(dict))  # member_profiles[cid][uid] = {"name","first","last","msgs"}
whitelist = defaultdict(set)                         # whitelist[cid] = {uid} 白名单（免疫禁言等）
leave_records = defaultdict(list)                    # leave_records[cid] = [{"ts","uid","name"}] 退群记录(每群留100)
join_requests = defaultdict(list)                    # join_requests[cid] = [{"ts","uid","name"}] 入群申请(每群留100)
admin_logs = []                                      # [{"ts","cid","admin","action","target"}] 管理员操作记录(留300)

def _write_settings_file(cfg: dict, password: str):
    try:
        tmp = f"{SETTINGS_FILE}.tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump({"fields": cfg, "web_password": password}, f, ensure_ascii=False, indent=2)
        os.replace(tmp, SETTINGS_FILE)
    except Exception:
        logger.exception("设置文件写盘失败")

_DYN_CMD_OWNED = {}  # gname -> 上次注册的动态指令名（改名后移除旧指令）

def _sync_dyn_aliases():
    """把网页自定义的指令名（查询积分/签到/积分排行）注册进命令分发表；旧名随之失效。"""
    aliases = globals().get("CMD_ALIASES")
    if aliases is None:
        return
    for gname, fn in (("QUERY_CMD", cmd_my_points), ("SIGN_CMD", cmd_sign), ("RANK_CMD", cmd_points_rank)):
        old = _DYN_CMD_OWNED.get(gname)
        if old and aliases.get(old) is fn:
            aliases.pop(old, None)
        name = globals().get(gname)
        if name:
            aliases[name] = fn
            _DYN_CMD_OWNED[gname] = name

def apply_settings(cfg: dict):
    """把设置字典套用到内存全局常量（带类型与范围校验，非法值跳过）。

    数字字段先套用（HORSE_COUNT 先生效，名称/表情才好做数量联动校验）；
    names/emoji 要求拆分后条数 == 当前 HORSE_COUNT，否则整条跳过；
    bets 要求 1~6 个 1~100000 的正整数，自动去重升序。
    """
    applied = {}
    # 数字字段先套用；赛马三件套（count/names/emoji）抽出单独联动处理
    for key, gname, _label, ftype, lo, hi, _grp in SETTINGS_FIELDS:
        if key not in cfg or ftype not in ("int", "float") or key == "horse_count":
            continue
        try:
            v = float(cfg[key])
            if ftype == "int":
                if v != int(v): raise ValueError
                v = int(v)
            if not (lo <= v <= hi): raise ValueError
        except (ValueError, TypeError):
            continue
        globals()[gname] = v
        applied[key] = v
    # 布尔字段
    for key, gname, _label, ftype, _lo, _hi, _grp in SETTINGS_FIELDS:
        if key in cfg and ftype == "bool":
            v = 1 if str(cfg[key]).strip().lower() in ("1", "on", "true", "yes", "是") else 0
            globals()[gname] = v
            applied[key] = v
    # 等级表 / 商品表：每行 "名称:数值"（支持中英文冒号），按数值升序
    for key, gname, ftype in (("point_levels", "POINT_LEVELS", "levels"), ("mall_items", "MALL_ITEMS", "items")):
        if key not in cfg:
            continue
        raw = cfg[key]
        if isinstance(raw, (list, tuple)):
            lines = raw
        else:
            lines = str(raw).replace("：", ":").splitlines()
        parsed, ok = [], True
        for line in lines:
            line = str(line).strip()
            if not line:
                continue
            name, _, val = line.partition(":")
            name, val = name.strip(), val.strip()
            if not name or len(name) > 12 or any(ch in name for ch in "<>&"):
                ok = False; break
            try:
                v = int(float(val))
            except ValueError:
                ok = False; break
            if not (0 <= v <= 10000000) or (ftype == "items" and v < 1):
                ok = False; break
            parsed.append({"name": name, "value": v})
        if ok and parsed and len(parsed) <= 30:
            parsed.sort(key=lambda x: x["value"])
            globals()[gname] = parsed
            applied[key] = parsed
        elif ok and not parsed and ftype == "items":
            globals()[gname] = []  # 商品表允许清空
            applied[key] = []
    # 文本模板 / 短文本（表情）/ 自定义指令
    for key, gname, _label, ftype, _lo, _hi, _grp in SETTINGS_FIELDS:
        if key not in cfg or ftype not in ("text", "short", "cmd"):
            continue
        v = str(cfg[key]).replace("\r\n", "\n").strip()
        if ftype == "cmd":
            v = v.lstrip("/")
            if not v or len(v) > 16 or re.search(r"[\s<>&@]", v):
                continue
        elif ftype == "short":
            if not v or len(v) > 8:
                continue
        elif len(v) > 1500:
            continue
        globals()[gname] = v
        applied[key] = v
    _sync_dyn_aliases()
    # --- 赛马三件套联动：数量/名称/表情必须一致才提交，否则整体保持原状（防 5 匹马 3 个名字的崩局） ---
    if any(k in cfg for k in ("horse_count", "horse_names", "horse_emoji")):
        def _split(v, maxlen):
            if isinstance(v, (list, tuple)):
                ps = [str(x).strip() for x in v if str(x).strip()]
            else:
                ps = [p.strip() for p in re.split(r"[,，]", str(v)) if p.strip()]
            if ps and all(0 < len(p) <= maxlen and not any(ch in p for ch in "<>&") for p in ps):
                return ps
            return None
        new_count = globals()["HORSE_COUNT"]
        cnt_given = "horse_count" in cfg
        try:
            c = int(float(cfg.get("horse_count")))
            if not (2 <= c <= 8): raise ValueError
            new_count = c
        except (ValueError, TypeError):
            pass
        new_names = _split(cfg["horse_names"], 8) if "horse_names" in cfg else globals()["HORSE_NAMES"]
        new_emoji = _split(cfg["horse_emoji"], 4) if "horse_emoji" in cfg else globals()["HORSE_EMOJI"]
        if new_names and new_emoji and len(new_names) == new_count == len(new_emoji):
            globals()["HORSE_COUNT"], globals()["HORSE_NAMES"], globals()["HORSE_EMOJI"] = new_count, new_names, new_emoji
            if cnt_given: applied["horse_count"] = new_count
            if "horse_names" in cfg: applied["horse_names"] = new_names
            if "horse_emoji" in cfg: applied["horse_emoji"] = new_emoji
    for key, gname, _label, ftype, _lo, _hi, _grp in SETTINGS_FIELDS:
        if key not in cfg or ftype not in ("names", "emoji", "bets") or key in ("horse_names", "horse_emoji"):
            continue
        raw = cfg[key]
        if isinstance(raw, (list, tuple)):
            parts = [str(p).strip() for p in raw if str(p).strip()]
        else:
            parts = [p.strip() for p in re.split(r"[,，]", str(raw)) if p.strip()]
        if ftype == "bets":
            try:
                vals = sorted({int(float(p)) for p in parts})
            except (ValueError, TypeError):
                continue
            if not (1 <= len(vals) <= 6 and all(1 <= v <= 100000 for v in vals)):
                continue
            globals()[gname] = vals
            applied[key] = vals
    return applied

def load_settings():
    """启动时读取 bot_settings.json 并套用；无文件则用代码内默认值。"""
    global _web_password
    try:
        with open(SETTINGS_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        apply_settings(data.get("fields", {}))
        pwd = str(data.get("web_password", "")).strip()
        if pwd:
            _web_password = pwd
        logger.info("设置已从 %s 加载", SETTINGS_FILE)
    except FileNotFoundError:
        logger.info("无设置文件（%s），全部使用默认配置", SETTINGS_FILE)
    except Exception:
        logger.exception("设置文件读取失败，使用默认配置")

def save_settings(cfg: dict, new_password: str = ""):
    """网页保存入口：套用内存 + 与已有存档合并写盘（分页保存互不覆盖）+ 可选改密码。"""
    global _web_password
    with _settings_lock:
        try:
            with open(SETTINGS_FILE, "r", encoding="utf-8") as f:
                stored = json.load(f).get("fields", {})
        except Exception:
            stored = {}
        applied = apply_settings(cfg)
        stored.update(applied)
        if new_password and len(new_password.strip()) >= 4:
            _web_password = new_password.strip()
        _write_settings_file(stored, _web_password)
    return applied
BEIJING_TZ = timezone(timedelta(hours=8))
HAND_NAME_CN = {"High Card":"高牌", "Pair":"一对", "One Pair":"一对", "Two Pair":"两对", "Three of a Kind":"三条", "Straight":"顺子", "Flush":"同花", "Full House":"葫芦", "Four of a Kind":"四条", "Straight Flush":"同花顺", "Royal Flush":"皇家同花顺"}
RANK_ICONS = ["🥇", "🥈", "🥉", "4️⃣", "5️⃣", "6️⃣", "7️⃣", "8️⃣", "9️⃣", "🔟"]


def rank_marker(index):
    if index == 1 and RANK_1_EMOJI: return RANK_1_EMOJI
    if index == 2 and RANK_2_EMOJI: return RANK_2_EMOJI
    if index == 3 and RANK_3_EMOJI: return RANK_3_EMOJI
    return RANK_ICONS[index - 1] if 1 <= index <= len(RANK_ICONS) else f"🔸{index}"


def total_profit_by_game(game_profit, chat_id):
    """聚合某游戏所有日期的盈亏为累计总数。"""
    total = defaultdict(int)
    for dates in game_profit.values():
        for uid, v in dates.get(chat_id, {}).items():
            total[uid] += v
    return dict(total)


# ---------- 数据 ----------
game_chips = defaultdict(lambda: defaultdict(lambda: GAME_STARTING_CHIPS))  # 统一积分钱包（全游戏/签到/红包/商城共用，初始 5W）
AUTHORIZED_GROUPS = set()
BLACKLISTED_USERS = set()  # 被拉黑、禁止使用该机器人的用户（管理员可解封）
race_history = defaultdict(list)
blackjack_history = defaultdict(list) # 新增 21点历史
race_daily_stats = defaultdict(lambda: [0] * HORSE_COUNT)
poker_profit_by_date = defaultdict(lambda: defaultdict(lambda: defaultdict(int)))
race_profit_by_date = defaultdict(lambda: defaultdict(lambda: defaultdict(int)))
blackjack_profit_by_date = defaultdict(lambda: defaultdict(lambda: defaultdict(int)))
jinhua_profit_by_date = defaultdict(lambda: defaultdict(lambda: defaultdict(int)))
race_jackpot = defaultdict(int)
hourly_race_enabled = defaultdict(lambda: False)
daily_emergency_used = defaultdict(lambda: defaultdict(bool))
# 已实扣的游戏下注，用于全系游戏在重启时自动退款。
# 按游戏类型分条存储，避免多游戏并发时记录互相覆盖：
# pending_game_bets[群ID][用户ID]["21"/"horse"] = {"amount": 100, "mode": "official"}
pending_game_bets = defaultdict(lambda: defaultdict(dict))
last_business_date = ""
active_poker_games, active_horse_races = {}, {}
active_blackjack_games = {}
active_jinhua_games = {}
recent_poker_reveals = defaultdict(list)  # 德州单赢结算后临时保存赢家牌（每群一个队列，供可选亮牌按钮使用，新单赢不再覆盖旧的）
# ---------- 德州排位赛状态（独立账本，每日重置不触碰） ----------
season_active = False
season_id = None
season_name = ""
season_start_ts = 0
season_end_ts = 0
season_points = defaultdict(lambda: defaultdict(int))    # season_points[cid][uid] 排位分（下注用）
season_games = defaultdict(lambda: defaultdict(int))     # season_games[cid][uid] 参赛局数
season_joined = defaultdict(set)                          # season_joined[cid] = {uid} 报名集合
season_rebuy = defaultdict(lambda: defaultdict(int))      # season_rebuy[cid][uid] 已用应急补分次数
season_lobby_msg = {}                                       # season_lobby_msg[cid] = 排位大厅看板消息 id（UI 态，不持久化）
season_profit_by_date = defaultdict(lambda: defaultdict(lambda: defaultdict(int)))  # season_profit_by_date[date][cid][uid] = 当日盈亏（赛季每日重置成 2W 前记录；赛季总排行=7日累计之和）
# ---------- 赌神称号（全局唯一，跨群共享荣誉） ----------
user_titles = {}               # user_titles[uid] = {"🎰赌神", ...}  每人拥有的称号集合（赌神全局唯一，其余称号可叠加）
champions_history = []         # [{"season_id","uid","name","score","streak"}] 历届荣誉墙
TITLE_GAMBLING_GOD = "🔱赌神"
title_expiry = {}              # title_expiry[uid][称号] = 到期时间戳（仅限时称号；永久称号不在此）
title_equipped = {}            # title_equipped[uid] = 当前佩戴的称号（玩家手动选择，可覆盖默认显示）
# ---------- 积分商店（称号兑换）：price 价格 / duration 时限秒或 None=永久（统一积分支付） ----------
SHOP_TITLES = {
    # 积分支付（永久，价格从低到高）
    "赌狗":     {"price": 5000, "currency": "game", "duration": None},
    "赌鬼":     {"price": 10000, "currency": "game", "duration": None},
    "赌徒":     {"price": 15000, "currency": "game", "duration": None},
    "散财童子": {"price": 20000, "currency": "game", "duration": None},
    "小赌怡情": {"price": 25000, "currency": "game", "duration": None},
    "见好就收": {"price": 30000, "currency": "game", "duration": None},
    "幸运星":   {"price": 35000, "currency": "game", "duration": None},
    "一夜暴富": {"price": 40000, "currency": "game", "duration": None},
    "鸿运当头": {"price": 45000, "currency": "game", "duration": None},
    "财神爷":   {"price": 55000, "currency": "game", "duration": None},
    "赌怪":     {"price": 65000, "currency": "game", "duration": None},
    "赌侠":     {"price": 85000, "currency": "game", "duration": None},
    "快枪手":   {"price": 105000, "currency": "game", "duration": None},
    "常胜将军": {"price": 135000, "currency": "game", "duration": None},
    "老千":     {"price": 165000, "currency": "game", "duration": None},
    "赌王":     {"price": 200000, "currency": "game", "duration": None},
    "赌霸":     {"price": 240000, "currency": "game", "duration": None},
    "赌魔":     {"price": 280000, "currency": "game", "duration": None},
    "赌圣":     {"price": 320000, "currency": "game", "duration": None},
    "赌尊":     {"price": 360000, "currency": "game", "duration": None},
    "赌皇":     {"price": 400000, "currency": "game", "duration": None},
    "赌帝":     {"price": 450000, "currency": "game", "duration": None},
    "赌仙":     {"price": 500000, "currency": "game", "duration": None},
    "赌魂":     {"price": 550000, "currency": "game", "duration": None},
    "千王之王": {"price": 600000, "currency": "game", "duration": None},
    # 炸金花 / 梭哈系列（永久）
    "金花":     {"price": 20000, "currency": "game", "duration": None},
    "豹子":     {"price": 30000, "currency": "game", "duration": None},
    "一把梭":   {"price": 50000, "currency": "game", "duration": None},
    "闷牌大师": {"price": 80000, "currency": "game", "duration": None},
    "偷鸡圣手": {"price": 100000, "currency": "game", "duration": None},
    "明牌博弈": {"price": 120000, "currency": "game", "duration": None},
    "二三五":   {"price": 150000, "currency": "game", "duration": None},
    "梭哈王":   {"price": 250000, "currency": "game", "duration": None},
    # 德州系列（永久）
    "德州新手": {"price": 2000, "currency": "game", "duration": None},
    "德州小将": {"price": 4000, "currency": "game", "duration": None},
    "德州老千": {"price": 6000, "currency": "game", "duration": None},
    "诈唬大师": {"price": 8000, "currency": "game", "duration": None},
    "葫芦王":   {"price": 10000, "currency": "game", "duration": None},
    "四条王":   {"price": 12000, "currency": "game", "duration": None},
    "同花顺王": {"price": 15000, "currency": "game", "duration": None},
    "皇家同花顺": {"price": 18000, "currency": "game", "duration": None},
    "德扑之王": {"price": 20000, "currency": "game", "duration": None},
    "河牌之王": {"price": 20000, "currency": "game", "duration": None},
}

# 称号图标（展示层）：与 SHOP_TITLES 的 key 一一对应，缺省为空串。赌神自带 🎰 无需在此。
TITLE_ICONS = {
    # 积分支付
    "赌狗": "🐶", "赌鬼": "👻", "赌徒": "🎲", "散财童子": "💸",
    "小赌怡情": "🍵", "见好就收": "🧘", "幸运星": "⭐", "一夜暴富": "💰",
    "鸿运当头": "🍀", "财神爷": "🧧", "赌怪": "👾", "赌侠": "🦸",
    "快枪手": "🔫", "常胜将军": "🏆", "老千": "🃏", "赌王": "👑",
    "赌霸": "🐯", "赌魔": "😈", "赌圣": "✨", "赌尊": "🏔️",
    "赌皇": "🐲", "赌帝": "⚜️", "赌仙": "🧚", "赌魂": "🔥",
    "千王之王": "🎴",
    # 炸金花 / 梭哈系列
    "金花": "🌸", "豹子": "🐆", "一把梭": "💥", "闷牌大师": "🕶️",
    "偷鸡圣手": "🐓", "明牌博弈": "👁️", "二三五": "☄️", "梭哈王": "⚔️",
    # 德州系列
    "德州新手": "🌱", "德州小将": "🎖️", "德州老千": "🎭", "诈唬大师": "😏",
    "葫芦王": "🏠", "四条王": "🀄", "同花顺王": "♠️", "皇家同花顺": "💎",
    "德扑之王": "🤴", "河牌之王": "🌊",
}


def title_icon(title):
    """称号图标，缺省空串。"""
    return TITLE_ICONS.get(title, "")

# ---------- 昵称缓存（持久化）：群里每条消息/回调直接拿 effective_user 真名，避免 get_chat 失败回退成"玩家{uid}" ----------
user_names = {}                # user_names[uid] = "真名"（原始串，输出时再 html.escape）
chat_name_cache = {}           # chat_name_cache[cid] = 群名（入站消息自动缓存，授权列表等无需再调 get_chat）
# 用于老虎机等功能的冷却时间限制。
# 高性能保存逻辑变量
data_dirty = False
save_event = None # 延迟初始化
data_save_lock = threading.Lock()
background_tasks = set()
# 用户级钱包锁：防止同一用户同时进入多个扣款/派彩路径导致并发负分
wallet_locks = defaultdict(asyncio.Lock)

@asynccontextmanager
async def user_wallet_locks(uids):
    """按 uid 全局有序获取多个用户钱包锁，避免死锁。用于多人结算（牛牛/德州等）。"""
    uids = sorted(set(uids))
    for uid in uids:
        await wallet_locks[uid].acquire()
    try:
        yield
    finally:
        for uid in reversed(uids):
            wallet_locks[uid].release()


def now_bj(): return datetime.now(BEIJING_TZ)

def race_id(ts): return datetime.fromtimestamp(ts, timezone.utc).astimezone(BEIJING_TZ).strftime("%Y%m%d-%H%M")
def business_date(now=None):
    now = now or now_bj()
    return (now + timedelta(days=1) if (now.hour, now.minute) >= (23, 50) else now).strftime("%Y-%m-%d")


def current_game_mode():
    """统一正式模式（已移除娱乐时段）。"""
    return "official"




def restore_nested(target, source):

    for cid, users in source.items():
        for uid, value in users.items(): target[int(cid)][int(uid)] = int(value)


def save_data():
    """高性能脏标记保存：确保安全初始化。"""
    global data_dirty
    data_dirty = True
    # 彻底解决 save_event 未初始化导致的挂死问题
    try:
        if save_event is not None:
            save_event.set()
    except Exception:
        pass


def force_save_now():
    """强制立刻执行物理写盘，用于关机等场景。"""
    try:
        with data_save_lock:
            data = {
                "game_chips": {str(cid): dict(users) for cid, users in game_chips.items()},
                "poker_profit_by_date": {date: {str(cid): dict(users) for cid, users in chats.items()} for date, chats in poker_profit_by_date.items()},
                "race_profit_by_date": {date: {str(cid): dict(users) for cid, users in chats.items()} for date, chats in race_profit_by_date.items()},
                "blackjack_profit_by_date": {date: {str(cid): dict(users) for cid, users in chats.items()} for date, chats in blackjack_profit_by_date.items()},
                "jinhua_profit_by_date": {date: {str(cid): dict(users) for cid, users in chats.items()} for date, chats in jinhua_profit_by_date.items()},
                "authorized_groups": list(AUTHORIZED_GROUPS),
                "bot_admins": list(BOT_ADMINS),
                "blacklist": list(BLACKLISTED_USERS),
                "race_jackpot": {str(cid): value for cid, value in race_jackpot.items()},
                "hourly_race_enabled": {str(cid): value for cid, value in hourly_race_enabled.items()},
                "race_history": {str(cid): value[-10:] for cid, value in race_history.items()},
                "blackjack_history": {str(cid): value[-10:] for cid, value in blackjack_history.items()},
                "race_daily_stats": {str(cid): value for cid, value in race_daily_stats.items()},
                "daily_emergency_used": {str(cid): {str(uid): used for uid, used in users.items()} for cid, users in daily_emergency_used.items()},
                "last_business_date": last_business_date,
                "pending_game_bets": {str(cid): {str(uid): val for uid, val in users.items()} for cid, users in pending_game_bets.items()},
                "season_active": season_active,
                "season_id": season_id,
                "season_name": season_name,
                "season_start_ts": season_start_ts,
                "season_end_ts": season_end_ts,
                "season_points": {str(cid): dict(users) for cid, users in season_points.items()},
                "season_games": {str(cid): dict(users) for cid, users in season_games.items()},
                "season_joined": {str(cid): list(users) for cid, users in season_joined.items()},
                "season_rebuy": {str(cid): dict(users) for cid, users in season_rebuy.items()},
                "season_profit_by_date": {date: {str(cid): dict(users) for cid, users in chats.items()} for date, chats in season_profit_by_date.items()},
                "user_titles": {str(uid): sorted(t) for uid, t in user_titles.items()},
                "title_expiry": {str(uid): {t: int(exp) for t, exp in ts.items()} for uid, ts in title_expiry.items()},
                "title_equipped": {str(uid): t for uid, t in title_equipped.items()},
                "champions_history": champions_history,
                "user_names": {str(uid): n for uid, n in user_names.items()},
                "sign_data": {str(cid): {str(uid): dict(v) for uid, v in users.items()} for cid, users in sign_data.items()},
                "chat_today": {date: {str(cid): {str(uid): v for uid, v in users.items()} for cid, users in chats.items()} for date, chats in chat_today.items()},
                "mall_orders": mall_orders[-200:],
                "auctions": {str(cid): {"item": a["item"], "price": a["price"], "top_uid": a["top_uid"],
                                        "step": a.get("step", AUCTION_STEP), "end_ts": a["end_ts"], "msg_id": a["msg_id"]} for cid, a in auctions.items()},
                "buy_orders": {oid: dict(o) for oid, o in buy_orders.items()},
                "member_profiles": {str(cid): {str(uid): dict(v) for uid, v in users.items()} for cid, users in member_profiles.items()},
                "whitelist": {str(cid): sorted(users) for cid, users in whitelist.items()},
                "leave_records": {str(cid): v[-100:] for cid, v in leave_records.items()},
                "join_requests": {str(cid): v[-100:] for cid, v in join_requests.items()},
                "admin_logs": admin_logs[-300:],
            }
            os.makedirs(os.path.dirname(os.path.abspath(DATA_FILE)), exist_ok=True)
            with open(DATA_TEMP_FILE, "w", encoding="utf-8") as file:
                json.dump(data, file, ensure_ascii=False, indent=2)
                file.flush(); os.fsync(file.fileno())
            if os.path.exists(DATA_FILE): shutil.copy2(DATA_FILE, DATA_BACKUP_FILE)
            os.replace(DATA_TEMP_FILE, DATA_FILE)
        return True
    except Exception:
        logger.exception("物理写盘失败")
        return False


async def data_save_worker():
    """后台高性能保存任务：数据变更后 3 秒合并保存；无变更时每 60 秒保底强制保存一次。"""
    global data_dirty
    while True:
        try:
            await asyncio.wait_for(save_event.wait(), timeout=60)
        except asyncio.TimeoutError:
            pass  # 60 秒无触发，走保底保存
        save_event.clear()
        try:
            if data_dirty:
                # 在单独的线程中执行写盘，不阻塞主循环
                await asyncio.to_thread(force_save_now)
                data_dirty = False
        except Exception:
            logger.exception("data_save_worker 写盘异常（已吞并继续）")
        await asyncio.sleep(3)


def load_data():
    global last_business_date, season_active, season_id, season_name, season_start_ts, season_end_ts, user_titles, champions_history, user_names, title_expiry, title_equipped
    source = DATA_FILE if os.path.exists(DATA_FILE) else DATA_BACKUP_FILE
    if not os.path.exists(source): return
    try:
        with open(source, "r", encoding="utf-8") as file: data = json.load(file)
    except Exception:
        if source != DATA_FILE or not os.path.exists(DATA_BACKUP_FILE):
            logger.exception("数据读取失败"); return
        try:
            with open(DATA_BACKUP_FILE, "r", encoding="utf-8") as file: data = json.load(file)
            logger.warning("主数据文件损坏，已从备份恢复")
        except Exception:
            logger.exception("备份读取失败"); return
    try:
        # 兼容旧存档：group_chips 键迁移为统一积分
        restore_nested(game_chips, data.get("game_chips", data.get("group_chips", {})))
        # 统一积分：旧存档的德州专用积分余额一次性并入统一积分（在 game_chips 覆盖恢复之后追加，之后不再单独保存）
        for cid, users in data.get("texas_chips", {}).items():
            try:
                c = int(cid)
                for uid, v in users.items():
                    try: game_chips[c][int(uid)] += int(v)
                    except (ValueError, TypeError): continue
            except (ValueError, TypeError): continue
        for date, chats in data.get("poker_profit_by_date", {}).items(): restore_nested(poker_profit_by_date[date], chats)
        for date, chats in data.get("race_profit_by_date", {}).items(): restore_nested(race_profit_by_date[date], chats)
        for date, chats in data.get("blackjack_profit_by_date", {}).items(): restore_nested(blackjack_profit_by_date[date], chats)
        for date, chats in data.get("jinhua_profit_by_date", {}).items(): restore_nested(jinhua_profit_by_date[date], chats)
        # 德州排位赛状态恢复
        season_active = data.get("season_active", False)
        season_id = data.get("season_id")
        season_name = data.get("season_name", "")
        season_start_ts = data.get("season_start_ts", 0)
        season_end_ts = data.get("season_end_ts", 0)
        restore_nested(season_points, data.get("season_points", {}))
        restore_nested(season_games, data.get("season_games", {}))
        restore_nested(season_rebuy, data.get("season_rebuy", {}))
        for cid, uids in data.get("season_joined", {}).items():
            season_joined[int(cid)] = set(int(u) for u in uids)
        for date, chats in data.get("season_profit_by_date", {}).items(): restore_nested(season_profit_by_date[date], chats)
        # 赌神称号恢复
        user_titles.clear()
        for uid, t in data.get("user_titles", {}).items():
            # 兼容旧数据格式（单个称号字符串）与新格式（称号列表）
            user_titles[int(uid)] = {t} if isinstance(t, str) else set(t)
        title_expiry.clear()
        for uid, ts in data.get("title_expiry", {}).items():
            title_expiry[int(uid)] = {t: int(exp) for t, exp in ts.items()}
        title_equipped.clear()
        for uid, t in data.get("title_equipped", {}).items():
            title_equipped[int(uid)] = t
        # 数据迁移：赌神图标 🎰→🔱（兼容旧数据，避免已持有玩家丢失称号）
        _OLD_GOD = "🎰赌神"
        for _uid, _titles in list(user_titles.items()):
            if _OLD_GOD in _titles:
                _titles.discard(_OLD_GOD)
                _titles.add(TITLE_GAMBLING_GOD)
        for _uid, _t in list(title_equipped.items()):
            if _t == _OLD_GOD:
                title_equipped[_uid] = TITLE_GAMBLING_GOD
        champions_history.clear()
        champions_history.extend(data.get("champions_history", []))
        # 昵称缓存恢复：群里成员真名（避免重启后大量回退成“玩家{uid}”）
        user_names.clear()
        for uid, n in data.get("user_names", {}).items():
            if n: user_names[int(uid)] = n
        # 积分系统数据恢复
        for cid, users in data.get("sign_data", {}).items():
            for uid, v in users.items():
                if isinstance(v, dict): sign_data[int(cid)][int(uid)] = {"last": str(v.get("last", "")), "streak": int(v.get("streak", 0))}
        for date, chats in data.get("chat_today", {}).items():
            for cid, users in chats.items():
                for uid, v in users.items():
                    chat_today[str(date)][int(cid)][int(uid)] = int(v)
        mall_orders.clear()
        mall_orders.extend(data.get("mall_orders", [])[-200:])
        auctions.clear()
        for cid, a in data.get("auctions", {}).items():
            try:
                auctions[int(cid)] = {"item": str(a["item"]), "price": int(a["price"]),
                                      "top_uid": int(a["top_uid"]) if a.get("top_uid") else None,
                                      "step": int(a.get("step", AUCTION_STEP)),
                                      "end_ts": float(a["end_ts"]), "msg_id": a.get("msg_id"), "task": None}
            except (KeyError, ValueError, TypeError): continue
        buy_orders.clear()
        for oid, o in data.get("buy_orders", {}).items():
            try: buy_orders[str(oid)] = {"cid": int(o["cid"]), "uid": int(o["uid"]), "amount": int(o["amount"]), "ts": o.get("ts", "")}
            except (KeyError, ValueError, TypeError): continue
        # 群组管理数据恢复
        for cid, users in data.get("member_profiles", {}).items():
            for uid, v in users.items():
                if isinstance(v, dict): member_profiles[int(cid)][int(uid)] = v
        for cid, uids in data.get("whitelist", {}).items():
            whitelist[int(cid)].update(int(u) for u in uids)
        for cid, v in data.get("leave_records", {}).items():
            leave_records[int(cid)] = list(v)[-100:]
        for cid, v in data.get("join_requests", {}).items():
            join_requests[int(cid)] = list(v)[-100:]
        admin_logs.extend(data.get("admin_logs", [])[-300:])
        AUTHORIZED_GROUPS.update(int(cid) for cid in data.get("authorized_groups", []))
        BOT_ADMINS.clear(); BOT_ADMINS.update(ADMIN_USER_IDS)
        BOT_ADMINS.update(int(x) for x in data.get("bot_admins", []))
        BLACKLISTED_USERS.update(int(x) for x in data.get("blacklist", []))
        for cid, value in data.get("race_jackpot", {}).items(): race_jackpot[int(cid)] = int(value)
        for cid, value in data.get("hourly_race_enabled", {}).items(): hourly_race_enabled[int(cid)] = bool(value)
        for cid, value in data.get("race_history", {}).items(): race_history[int(cid)] = list(value)[-10:]
        for cid, value in data.get("blackjack_history", {}).items(): blackjack_history[int(cid)] = list(value)[-10:]
        for cid, value in data.get("race_daily_stats", {}).items(): race_daily_stats[int(cid)] = list(value)[:HORSE_COUNT]
        for cid, users in data.get("daily_emergency_used", {}).items():
            for uid, used in users.items(): daily_emergency_used[int(cid)][int(uid)] = min(int(used), EMERGENCY_MAX_USES)
        last_business_date = data.get("last_business_date", "")
        # 全系游戏退款恢复逻辑
        for cid, users in data.get("pending_game_bets", {}).items():
            for uid, info in users.items():
                # 兼容旧格式（单条记录）与新格式（按游戏类型分条）
                entries = [info] if "amount" in info else list(info.values())
                for ginfo in entries:
                    wallet = game_chips
                    wallet[int(cid)][int(uid)] += int(ginfo.get("amount", 0))
        pending_game_bets.clear()
        force_save_now()
    except Exception:
        logger.exception("恢复数据失败")


def archive_old_profit_data(keep_days=90):
    """将超过 keep_days 天的盈亏明细归档合并到 _archive，保留累计榜数字不变。"""
    cutoff = (now_bj() - timedelta(days=keep_days)).strftime("%Y-%m-%d")
    for profit_dict in (race_profit_by_date, blackjack_profit_by_date,
                        jinhua_profit_by_date, season_profit_by_date):
        old_dates = [d for d in list(profit_dict.keys()) if d != "_archive" and d < cutoff]
        if not old_dates:
            continue
        archive = profit_dict["_archive"]
        for d in old_dates:
            for cid, users in profit_dict[d].items():
                for uid, v in users.items():
                    archive[cid][uid] += v
            del profit_dict[d]
    logger.info(f"归档完成：保留 {keep_days} 天明细，旧数据已合并至 _archive")


load_data()
archive_old_profit_data()
force_save_now()  # 归档结果立即物理落盘，避免启动后 60 秒内崩溃丢失归档

# ---------- Telegram 工具 ----------
def title_prefix(uid):
    """持称号的玩家在名字前加称号前缀。优先级：手动佩戴 > 赌神 > 最贵商店称号。
    称号均为预设固定串（不含 <>&），HTML/纯文本均安全。"""
    ts = user_titles.get(uid)
    if not ts:
        return ""
    # 过滤已过期的限时称号（避免 daily_reset 清理前仍显示过期称号）
    _exp = title_expiry.get(uid)
    if _exp:
        _now = int(now_bj().timestamp())
        ts = {t for t in ts if t not in _exp or _exp[t] > _now}
    if not ts:
        return ""
    equipped = title_equipped.get(uid)
    if equipped and equipped in ts:
        return f"{title_icon(equipped)}{equipped} "
    if TITLE_GAMBLING_GOD in ts:
        return f"{TITLE_GAMBLING_GOD} "
    best = max((t for t in ts if t in SHOP_TITLES), key=lambda t: SHOP_TITLES[t]["price"], default=None)
    return f"{title_icon(best)}{best} " if best else ""


def _extract_name(chat):
    """从 Chat/User 对象提取展示名；提取不到返回 None。"""
    name = " ".join(part for part in (chat.first_name, chat.last_name) if part)
    return name or (f"@{chat.username}" if getattr(chat, "username", None) else None)


def _remember_name(update):
    """从任意入站 update 抓取发送者真名进 user_names 缓存（零 API 调用，优先于 get_chat）。"""
    u = update.effective_user
    if not u or u.is_bot: return
    name = u.full_name or (f"@{u.username}" if u.username else None)
    if name: user_names[u.id] = name
    # 顺带缓存群名：授权列表等场景无需再调 get_chat（避免被异常静默吞掉导致只显示 ID）
    c = update.effective_chat
    if c and c.title:
        chat_name_cache[c.id] = c.title


async def get_name(app, uid, with_title=True, cid=None):
    """解析玩家展示名。

    解析优先级：1) 群内 get_chat_member(cid, uid)（群里成员必能解，即使没和 bot 私聊）；
    2) get_chat(uid)；3) 已缓存的 user_names。全部失败才回退为“玩家{uid}”。
    解析成功的真名写入 user_names 缓存，减少后续 API 调用与失败率。
    """
    raw = user_names.get(uid)
    if raw is None:
        if cid is not None:
            try:
                member = await app.bot.get_chat_member(cid, uid)
                raw = _extract_name(member.user)
            except Exception:
                raw = None
        if raw is None:
            try:
                raw = _extract_name(await app.bot.get_chat(uid))
            except Exception:
                raw = None
        if raw:
            user_names[uid] = raw
    if not raw:
        raw = f"玩家{uid}"
    base = html.escape(raw)
    return f"{title_prefix(uid)}{base}" if with_title else base


async def safe_send(bot, cid, text, **kwargs):
    for attempt in range(2):
        try: return await bot.send_message(chat_id=cid, text=text, **kwargs)
        except RetryAfter as exc:
            if attempt == 0: await asyncio.sleep(min(exc.retry_after, 5)); continue
        except TelegramError:
            logger.exception("发送消息失败: %s", cid); break
    return None


def split_telegram_text(text, max_bytes=4000):
    """按 UTF-8 字节切分，避免中文结算消息超过 Telegram 的 4096 字节限制。

    切分时保证：① 不切断 <b>/</b> 等 HTML 标签；② 各分片标签自平衡
    （跨分片记住未闭合的 <b>，在下一片开头补开、结尾补闭）。
    """
    parts, remaining = [], text
    open_tags = []  # 跨分片保持打开的 <b> 栈
    while len(remaining.encode("utf-8")) > max_bytes:
        size, cut = 0, 0
        for index, char in enumerate(remaining):
            char_size = len(char.encode("utf-8"))
            if size + char_size > max_bytes: break
            size += char_size; cut = index + 1
        # 优先在换行处切
        newline = remaining.rfind("\n", 0, cut)
        cut = newline if newline > 0 else cut
        # 避免切断 HTML 标签：若切点在 < 与 > 之间，回退到该 < 之前
        open_pos = remaining.rfind("<", 0, cut)
        close_pos = remaining.rfind(">", 0, cut)
        if open_pos > close_pos:
            cut = open_pos
        if cut <= 0:
            # 极端：单标签超长，按字节硬切保底
            size, cut = 0, 0
            for index, char in enumerate(remaining):
                char_size = len(char.encode("utf-8"))
                if size + char_size > max_bytes: break
                size += char_size; cut = index + 1
        body = remaining[:cut]
        open_count = body.count("<b>"); close_count = body.count("</b>")
        pending_before = len(open_tags)
        pending_after = pending_before + open_count - close_count
        if pending_after < 0: pending_after = 0
        # 该分片：开头补上之前遗留的未闭合 <b>，结尾补闭当前仍打开的 <b>
        parts.append(("<b>" * pending_before) + body + ("</b>" * pending_after))
        open_tags = ["b"] * pending_after
        remaining = remaining[cut:].lstrip("\n")
    if remaining:
        pending_before = len(open_tags)
        parts.append(("<b>" * pending_before) + remaining + ("</b>" * pending_before))
    return parts


async def safe_send_long(bot, cid, text, **kwargs):
    last = None
    for index, part in enumerate(split_telegram_text(text)):
        part_kwargs = dict(kwargs)
        if index > 0: part_kwargs.pop("reply_markup", None)  # 只有第一段带键盘，后续段保留 parse_mode
        last = await safe_send(bot, cid, part, **part_kwargs)
        if last is None:
            logger.error("长消息发送失败，群 %s，第 %s 段未送达", cid, index + 1)
            return None
    return last


async def safe_edit(bot, cid, msg_id, text, **kwargs):
    if not msg_id: return None
    try: return await bot.edit_message_text(chat_id=cid, message_id=msg_id, text=text, **kwargs)
    except BadRequest as exc:
        if "Message is not modified" not in str(exc): logger.warning("编辑消息失败: %s", exc)
    except RetryAfter as exc:
        await asyncio.sleep(min(exc.retry_after, 5))
        return await safe_edit(bot, cid, msg_id, text, **kwargs)
    except TelegramError: logger.exception("编辑消息失败")
    return None


async def safe_send_photo(bot, cid, photo, caption, **kwargs):
    for attempt in range(2):
        try: return await bot.send_photo(chat_id=cid, photo=photo, caption=caption, **kwargs)
        except RetryAfter as exc:
            if attempt == 0: await asyncio.sleep(min(exc.retry_after, 5)); continue
        except TelegramError:
            logger.exception("发送图片失败: %s", cid); break
    return None



async def safe_delete(bot, cid, msg_id):
    if msg_id:
        try: await bot.delete_message(chat_id=cid, message_id=msg_id)
        except TelegramError: pass


def card_str(card):
    raw = Card.int_to_pretty_str(card).strip("[]")
    suit = {"♠":"♠️", "♥":"♥️", "♦":"♦️", "♣":"♣️"}.get(raw[-1], raw[-1])
    return f"{suit}{raw[:-1].replace('T', '10')}"


async def action_notice(cid, app, uid, desc):
    message = await safe_send(app.bot, cid, f"🎲 {await get_name(app, uid)} {desc}")
    if message:
        async def delete_later():
            await asyncio.sleep(10); await safe_delete(app.bot, cid, message.message_id)
        asyncio.create_task(delete_later())


async def emergency_if_needed(cid, uid, app, wallet=None, poker=None):
    used = daily_emergency_used[cid][uid]
    wallet = wallet or game_chips
    if wallet[cid][uid] != 0 or used >= EMERGENCY_MAX_USES: return False
    wallet[cid][uid] = EMERGENCY_CHIPS
    if poker and uid in poker.chips: poker.chips[uid] += EMERGENCY_CHIPS
    daily_emergency_used[cid][uid] = used + 1; save_data()
    remaining = EMERGENCY_MAX_USES - daily_emergency_used[cid][uid]
    await safe_send(app.bot, cid, f"🆘 {await get_name(app, uid)} 积分归零，已赠送 {EMERGENCY_CHIPS} 应急积分（今日已补充 {daily_emergency_used[cid][uid]}/{EMERGENCY_MAX_USES} 次，剩余 {remaining} 次）。")
    return True


class BlackjackGame:
    def __init__(self, cid, owner, mode="official"):
        self.chat_id, self.owner_id, self.mode = cid, owner, mode
        self.phase = "waiting" # waiting, playing, dealer_turn, finished
        self.players = [] # uid list
        self.bets = {} # uid -> amount
        self.hands = defaultdict(list) # uid -> cards
        self.dealer_hand = []
        self.deck = []
        self.current_player_idx = 0
        self.game_msg_id = None
        self.action_msg_id = None # 用于置底的动态按钮消息 ID
        self.name_cache = {}
        self.timer_task = None
        self.wait_task = None # 新增等待解散任务变量
        self.settled = False

    def cancel_timer(self):
        if self.timer_task and not self.timer_task.done():
            self.timer_task.cancel()
            
    def cancel_wait(self):
        if self.wait_task and not self.wait_task.done():
            self.wait_task.cancel()

    def add_player(self, uid, bet):
        if self.phase != "waiting" or uid in self.players: return False
        self.players.append(uid)
        self.bets[uid] = bet
        
        # 记录退款保护
        pending_game_bets[self.chat_id][uid]["21"] = {"amount": bet, "mode": self.mode}
        return True

    def start(self):
        if not self.players: return False
        self.phase = "playing"
        self.deck = [r + s for r in "23456789TJQKA" for s in "shdc"] * BLACKJACK_DECKS
        random.shuffle(self.deck)
        # 发初始牌
        for _ in range(2):
            for p in self.players: self.hands[p].append(self.deck.pop())
            self.dealer_hand.append(self.deck.pop())
        return True

    def get_score(self, cards):
        score, aces = 0, 0
        val_map = {**{str(i): i for i in range(2, 10)}, "T": 10, "J": 10, "Q": 10, "K": 10, "A": 11}
        for c in cards:
            score += val_map[c[0]]
            if c[0] == "A": aces += 1
        while score > 21 and aces:
            score -= 10; aces -= 1
        return score

    def is_blackjack(self, cards):
        return len(cards) == 2 and self.get_score(cards) == 21

    def _draw(self):
        """发牌；牌堆耗尽时自动重洗一副新牌，避免抽牌崩溃。"""
        if not self.deck:
            self.deck = [r + s for r in "23456789TJQKA" for s in "shdc"] * BLACKJACK_DECKS
            random.shuffle(self.deck)
        return self.deck.pop()

    def hit(self, uid):
        if self.phase != "playing" or self.players[self.current_player_idx] != uid: return None
        card = self._draw()
        self.hands[uid].append(card)
        score = self.get_score(self.hands[uid])
        if score >= 21: self.next_player()
        return card

    def double_down(self, uid):
        if self.phase != "playing" or self.players[self.current_player_idx] != uid: return False
        # 翻倍：再扣一份钱
        bet = self.bets[uid]
        self.bets[uid] += bet
        
        # 记录退款保护 (更新)
        pending_game_bets[self.chat_id][uid]["21"] = {"amount": self.bets[uid], "mode": self.mode}
        
        # 强制摸一张
        self.hands[uid].append(self._draw())
        # 强制停牌
        self.next_player()
        return True

    def next_player(self):
        self.current_player_idx += 1
        if self.current_player_idx >= len(self.players):
            self.phase = "dealer_turn"

    def dealer_play(self):
        while self.get_score(self.dealer_hand) < 17:
            self.dealer_hand.append(self._draw())
        self.phase = "finished"

    def get_card_str(self, cards, hide_first=False):
        res = []
        for i, c in enumerate(cards):
            if i == 0 and hide_first: res.append("❓")
            else:
                raw = c.replace("T", "10")
                suit = {"s":"♠️", "h":"♥️", "d":"♦️", "c":"♣️"}.get(raw[-1], raw[-1])
                res.append(f"{suit}{raw[:-1]}")
        return " ".join(res)




# ==================== 德州扑克 ====================
def side_pots(total_bets):
    # 必须按投入金额升序构造主池和边池；按用户 ID 排序会跳过部分底池。
    ordered = sorted(
        ((uid, value) for uid, value in total_bets.items() if value > 0),
        key=lambda item: item[1],
    )
    result, previous = [], 0
    for _, level in ordered:
        if level <= previous: continue
        contributors = [uid for uid, amount in ordered if amount >= level]
        result.append(((level - previous) * len(contributors), contributors)); previous = level
    return result


def distribute_side_pots(total_bets, scores):
    payouts = defaultdict(lambda: {"amount": 0, "details": []})
    total_pot = sum(total_bets.values())
    for index, (amount, contributors) in enumerate(side_pots(total_bets)):
        eligible = {uid: scores[uid] for uid in contributors if uid in scores}
        if not eligible:
            # 根因：该层所有贡献者都已弃牌，原逻辑直接 skip，余额靠全局兜底掩盖分配。
            # 修正：弃牌者的投入仍属底池，按扑克规则归入仍存活的最佳牌型（低分=好牌）。
            best_score = min(scores.values())
            winners = sorted(uid for uid, score in scores.items() if score == best_score)
            share, remainder = divmod(amount, len(winners))
            for position, uid in enumerate(winners):
                won = share + (1 if position < remainder else 0)
                payouts[uid]["amount"] += won
                payouts[uid]["details"].append(("主池" if index == 0 else f"边池{index}", won))
            continue
        best = min(eligible.values()); winners = sorted(uid for uid, score in eligible.items() if score == best)
        share, remainder = divmod(amount, len(winners))
        for position, uid in enumerate(winners):
            won = share + (1 if position < remainder else 0)
            payouts[uid]["amount"] += won
            payouts[uid]["details"].append(("主池" if index == 0 else f"边池{index}", won))
    # 守恒兜底：任何因异常边池资格导致的剩余底池，归入当前最佳存活玩家，禁止积分凭空消失。
    allocated = sum(item["amount"] for item in payouts.values())
    unallocated = total_pot - allocated
    if unallocated > 0 and scores:
        best_score = min(scores.values())
        winners = sorted(uid for uid, score in scores.items() if score == best_score)
        share, remainder = divmod(unallocated, len(winners))
        for position, uid in enumerate(winners):
            won = share + (1 if position < remainder else 0)
            payouts[uid]["amount"] += won
            payouts[uid]["details"].append(("底池兜底", won))
    return payouts


class PokerGame:
    def __init__(self, cid, owner, mode=None, season=False):
        self.chat_id, self.owner_id, self.mode, self.phase = cid, owner, mode or current_game_mode(), "waiting"
        self.season = season  # 排位赛模式：用独立 season_points 下注，单手总投入不封顶
        self.players, self.chips, self.initial_chips = [], {}, {}
        self.total_bet, self.round_bets, self.hands = {}, {}, {}
        self.folded, self.all_in, self.acted = set(), set(), set()
        # 短全下抬高下注额时，已行动者必须补齐或弃牌，但不能再次加注。
        self.raise_locked = set()
        self.board, self.deck, self.active = [], [], []
        self.pot = self.current_bet = self.actor_idx = self.dealer_idx = 0
        self.game_msg_id = self.action_msg_id = None
        self.turn_task = self.auto_task = self.wait_task = None
        self.evaluator, self.settled, self.showdown_order = Evaluator(), False, []
        self.max_total_bet = None  # 排位赛单局每人投入上限（仅 season，start 时按总筹码×百分比算）
        self.start_date = now_bj().strftime("%Y-%m-%d")  # 开局业务日，用于排位赛跨午夜补重置判断

    def add(self, uid):
        if self.phase != "waiting" or uid in self.players: return False
        if self.season:
            # 排位赛：必须已报名、且排位分 > 0
            if uid not in season_joined.get(self.chat_id, set()):
                return False
            wallet = season_points
            if wallet[self.chat_id][uid] <= 0: return False
        else:
            wallet = game_chips
            if wallet[self.chat_id][uid] < MIN_ENTRY_CHIPS: return False
        self.players.append(uid); self.chips[uid] = wallet[self.chat_id][uid]; self.total_bet[uid] = 0
        return True

    def start(self):
        if len(self.players) < 2: return False
        random.shuffle(self.players)
        self.cancel_auto(); self.cancel_wait(); self.folded.clear(); self.all_in.clear(); self.acted.clear(); self.raise_locked.clear(); self.board = []; self.pot = 0; self.settled = False
        wallet = season_points if self.season else game_chips
        for uid in self.players:
            self.chips[uid] = wallet[self.chat_id][uid]; self.initial_chips[uid] = self.chips[uid]
            self.total_bet[uid] = self.round_bets[uid] = 0
            ante = min(ANTE, self.chips[uid]); self.chips[uid] -= ante; self.total_bet[uid] += ante; self.pot += ante
            if not self.chips[uid]: self.all_in.add(uid)
        # 排位赛：单局每人投入上限 = 本局落座玩家带入筹码总和 × 百分比（人少上限低，防串通）
        self.max_total_bet = max(int(sum(self.initial_chips.values()) * SEASON_BET_PERCENT), ANTE) if self.season else None
        self.deck = [Card.new(rank + suit) for rank in "23456789TJQKA" for suit in "shdc"]
        random.shuffle(self.deck); self.hands = {uid: [self.deck.pop(), self.deck.pop()] for uid in self.players}
        self.dealer_idx = len(self.players) - 1; self.active = self.players.copy()
        self._blind(self.players[(self.dealer_idx + 1) % len(self.players)], SMALL_BLIND)
        bb = (self.dealer_idx + 2) % len(self.players); self._blind(self.players[bb], BIG_BLIND)
        self.current_bet, self.phase, self.actor_idx = max(self.round_bets.values()), "preflop", (bb + 1) % len(self.active)
        if self._next(self.actor_idx) is None: self.phase = "showdown"
        return True

    def _blind(self, uid, value):
        paid = min(value, self.chips[uid])
        self.chips[uid] -= paid; self.round_bets[uid] += paid; self.total_bet[uid] += paid; self.pot += paid
        if not self.chips[uid]: self.all_in.add(uid)

    def current(self):
        if not self.active or self.actor_idx >= len(self.active): return None
        uid = self.active[self.actor_idx]
        return uid if uid not in self.folded and uid not in self.all_in and uid not in self.acted else None

    def _next(self, start):
        for offset in range(len(self.active)):
            idx = (start + offset) % len(self.active); uid = self.active[idx]
            if uid not in self.folded and uid not in self.all_in and uid not in self.acted:
                self.actor_idx = idx; return uid
        return None

    def _round_done(self): return all(uid in self.folded or uid in self.all_in or uid in self.acted for uid in self.active)

    def action(self, uid, kind, extra=0):
        if uid != self.current(): return False, "还没轮到你"
        skip_next = False
        if kind == "fold":
            old = self.active.index(uid); self.folded.add(uid); self.active.remove(uid)
            if self.active:
                self.actor_idx = old % len(self.active)
                self._next(self.actor_idx)   # 直接定位下一个行动者，避免末尾 _next(actor_idx+1) 跳过下家
            desc = "弃牌"
            skip_next = True
        elif kind == "check":
            if self.round_bets[uid] != self.current_bet: return False, "必须跟注或加注"
            self.acted.add(uid); desc = "过牌"
        elif kind == "call":
            paid = min(self.current_bet - self.round_bets[uid], self.chips[uid])
            if self.max_total_bet is not None and self.total_bet[uid] + paid > self.max_total_bet:
                return False, f"单局每人投入上限 {self.max_total_bet}，你已投入 {self.total_bet[uid]}"
            self.chips[uid] -= paid; self.round_bets[uid] += paid; self.total_bet[uid] += paid; self.pot += paid
            if not self.chips[uid]: self.all_in.add(uid)
            self.acted.add(uid); desc = f"跟注 {paid}"
        elif kind == "allin":
            paid = self.chips[uid]
            if self.max_total_bet is not None and self.total_bet[uid] + paid > self.max_total_bet:
                return False, f"单局每人投入上限 {self.max_total_bet}，你已投入 {self.total_bet[uid]}，可用加注补齐"
            old_bet = self.current_bet; new_total = self.round_bets[uid] + paid
            self.chips[uid] = 0; self.round_bets[uid] = new_total; self.total_bet[uid] += paid; self.pot += paid; self.all_in.add(uid)
            if new_total > old_bet:
                raise_size = new_total - old_bet
                prior_actors = self.acted.copy()
                self.current_bet = new_total
                # 任意抬高下注额的全下都要求其余玩家重新响应。
                self.acted = {uid}
                if raise_size < FIXED_MIN_RAISE:
                    # 短全下不重新开放加注：之前已经行动的玩家只能跟注或弃牌。
                    self.raise_locked.update(prior_actors - {uid})
                else:
                    self.raise_locked.clear()
            else: self.acted.add(uid)
            desc = f"全下 {paid}"
        elif kind == "raise":
            try: extra = int(extra)
            except (TypeError, ValueError): return False, "无效加注额"
            to_call = self.current_bet - self.round_bets[uid]; paid = to_call + extra; new_total = self.round_bets[uid] + paid
            if extra < FIXED_MIN_RAISE: return False, f"最低加注为 {FIXED_MIN_RAISE}"
            if paid > self.chips[uid]: return False, f"积分不足：本次需要跟注 {to_call} + 加注 {extra}，共 {paid}，你只有 {self.chips[uid]}"
            if self.max_total_bet is not None and self.total_bet[uid] + paid > self.max_total_bet:
                return False, f"单局每人投入上限 {self.max_total_bet}，你已投入 {self.total_bet[uid]}"
            if new_total <= self.current_bet: return False, "加注后总下注必须高于当前下注"
            if uid in self.raise_locked: return False, "短全下后已行动玩家只能跟注或弃牌"
            self.chips[uid] -= paid; self.round_bets[uid] = new_total; self.total_bet[uid] += paid; self.pot += paid; self.current_bet = new_total; self.acted = {uid}; self.raise_locked.clear()
            if not self.chips[uid]: self.all_in.add(uid)
            desc = f"加注 {extra}"
        else: return False, "未知操作"
        alive = [p for p in self.active if p not in self.folded]
        if len(alive) <= 1 or all(p in self.all_in for p in alive): self.phase = "showdown"
        elif self._round_done(): self._end_round()
        elif not skip_next: self._next(self.actor_idx + 1)
        return True, desc

    def _draw(self):
        """安全抽牌：牌堆耗尽时重洗一副新牌，避免抽牌 IndexError。"""
        if not self.deck:
            self.deck = [Card.new(rank + suit) for rank in "23456789TJQKA" for suit in "shdc"]
            random.shuffle(self.deck)
        return self.deck.pop()

    def _end_round(self):
        self.round_bets = {uid: 0 for uid in self.players}; self.current_bet = 0; self.acted.clear(); self.raise_locked.clear()
        if self.phase == "preflop": self._draw(); self.board.extend([self._draw() for _ in range(3)]); self.phase = "flop"
        elif self.phase == "flop": self._draw(); self.board.append(self._draw()); self.phase = "turn"
        elif self.phase == "turn": self._draw(); self.board.append(self._draw()); self.phase = "river"
        else: self.phase = "showdown"; return
        # 基于 dealer 在 active 中的位置计算起始行动者（dealer 可能已弃牌）
        dealer = self.players[self.dealer_idx]
        if dealer in self.active:
            start = (self.active.index(dealer) + 1) % len(self.active)
        else:
            # dealer 已弃牌：从按钮（dealer_idx）下一位开始，找第一个仍为 active 的玩家，以其 active 索引作为起点
            n = len(self.players)
            start = 0
            for i in range(1, n + 1):
                cand = self.players[(self.dealer_idx + i) % n]
                if cand in self.active:
                    start = self.active.index(cand)
                    break
        if self._next(start) is None: self.phase = "showdown"

    async def showdown(self):
        alive = [uid for uid in self.players if uid not in self.folded]
        self.showdown_order = alive.copy()

        # 只剩一名未弃牌玩家：直接获得底池。
        # 不继续发公牌，也不进入摊牌亮牌。
        if len(alive) == 1:
            winner = alive[0]
            self.chips[winner] += self.pot
            wallet = season_points if self.season else game_chips
            for uid in self.players:
                # 增量结算：保留牌局进行中管理员用 /adddz 加的分，避免被开局快照覆盖
                # 赛季已结束的进行中牌局不写回 season_points，避免污染已清空的赛季账本（仍正常派奖，筹码不持久化）
                if not (self.season and not season_active):
                    wallet[self.chat_id][uid] += self.chips[uid] - self.initial_chips.get(uid, wallet[self.chat_id][uid])
            save_data(); await asyncio.to_thread(force_save_now)
            return [(winner, "最后赢家", self.pot, [("全部底池", self.pot)], {})]

        # 至少两人仍在局内，才补齐五张公牌并进行正常摊牌。
        while len(self.board) < 5:
            self._draw()
            if not self.board:
                self.board.extend([self._draw() for _ in range(3)])
            else:
                self.board.append(self._draw())
        scores = {uid: self.evaluator.evaluate(self.hands[uid], self.board) for uid in alive}
        names = {uid: HAND_NAME_CN.get(self.evaluator.class_to_string(self.evaluator.get_rank_class(score)), "未知") for uid, score in scores.items()}
        payouts = distribute_side_pots(self.total_bet, scores)
        for uid, item in payouts.items(): self.chips[uid] += item["amount"]
        wallet = season_points if self.season else game_chips
        for uid in self.players:
            # 增量结算：保留牌局进行中管理员用 /adddz 加的分，避免被开局快照覆盖
            # 赛季已结束的进行中牌局不写回 season_points，避免污染已清空的赛季账本（仍正常派奖，筹码不持久化）
            if not (self.season and not season_active):
                wallet[self.chat_id][uid] += self.chips[uid] - self.initial_chips.get(uid, wallet[self.chat_id][uid])
        save_data(); await asyncio.to_thread(force_save_now); return [(uid, names[uid], item["amount"], item["details"], names) for uid, item in payouts.items()]

    def cancel_timer(self):
        task, self.turn_task = self.turn_task, None
        if task and task is not asyncio.current_task() and not task.done(): task.cancel()

    def cancel_auto(self):
        task, self.auto_task = self.auto_task, None
        if task and task is not asyncio.current_task() and not task.done(): task.cancel()

    def cancel_wait(self):
        task, self.wait_task = self.wait_task, None
        if task and task is not asyncio.current_task() and not task.done(): task.cancel()


# ---------- 德州界面 / 流程 ----------
async def poker_waiting_text(game, app):
    players = [f"{i}. {await get_name(app, uid)}" for i, uid in enumerate(game.players, 1)]
    prefix = "🏆 排位赛｜" if game.season else "🃏 新一局积分德州扑克"
    return f"{prefix}\n发起人：{await get_name(app, game.owner_id)}\n\n已加入：\n" + "\n".join(players) + "\n\n点击加入，发起人可立即开始。\n⏰ 满 2 人后 60 秒自动开局，不足 2 人 60 秒后自动解散。"


async def update_poker_waiting(game, app):
    rows = [[InlineKeyboardButton("📥 加入游戏", callback_data="texas_join")]]
    if len(game.players) >= 2: rows.append([InlineKeyboardButton("🎮 开始游戏", callback_data="texas_start")])
    rows.append([InlineKeyboardButton("❌ 终止房间", callback_data="texas_end")])
    await safe_edit(app.bot, game.chat_id, game.game_msg_id, await poker_waiting_text(game, app), reply_markup=InlineKeyboardMarkup(rows))


async def poker_table_text(game, app):
    phase = {"preflop":"翻牌前", "flop":"翻牌圈", "turn":"转牌圈", "river":"河牌圈"}.get(game.phase, game.phase)
    lines = [
        f"{'🏆 排位赛｜' if game.season else '🃏 积分德州'}｜{phase}",
        "",
        "━━━━━━━━━━━━━━━━━",
        f"🃏 公牌：{'  '.join(card_str(card) for card in game.board) or '未发牌'}",
        "",
        f"💰 奖池：{game.pot}｜当前下注：{game.current_bet}",
        "━━━━━━━━━━━━━━━━━",
    ]
    current = game.current()
    if current:
        lines.append(f"⏳ 当前行动：{await get_name(app, current)}｜需跟：{max(0, game.current_bet - game.round_bets[current])}")
    lines.append("")
    lines.append("👥 玩家状态")
    lines.append("")
    for index, uid in enumerate(game.players, 1):
        status = "❌ 弃牌" if uid in game.folded else "🔥 全下" if uid in game.all_in else "🟢 在局"
        lines.extend([f"{index}. {await get_name(app, uid)}", f"   {status}｜投入 {game.total_bet[uid]}｜余筹 {game.chips[uid]}", ""])
    return "\n".join(lines)


def poker_buttons(game, uid):
    rows = [[InlineKeyboardButton("🃏 查看手牌", callback_data="texas_hand")]]
    if uid != game.current() or uid in game.folded or uid in game.all_in: return InlineKeyboardMarkup(rows)
    to_call = max(0, game.current_bet - game.round_bets[uid])
    rows.append([InlineKeyboardButton("❌ 弃牌", callback_data="texas_fold"), InlineKeyboardButton("✅ 过牌" if not to_call else f"✅ 跟注 {to_call}", callback_data="texas_check" if not to_call else "texas_call")])
    # 半池/全池快捷加注（同栏）：加注金额=底池的 1/2 或 1 倍；不足最小加注时按最小加注兜底，保证池子小时也有加注入口
    if uid not in game.raise_locked:
        half_amt = max(FIXED_MIN_RAISE, game.pot // 2)
        pot_amt = max(FIXED_MIN_RAISE, game.pot)
        pot_row = []
        if half_amt < pot_amt and game.chips[uid] >= to_call + half_amt:
            pot_row.append(InlineKeyboardButton(f"💰 半池 +{half_amt}", callback_data="texas_raise_half"))
        if game.chips[uid] >= to_call + pot_amt:
            pot_row.append(InlineKeyboardButton(f"💰 全池 +{pot_amt}", callback_data="texas_raise_pot"))
        if pot_row: rows.append(pot_row)
        # 固定额加注：加注 100（最低加注额）；筹码不足时隐藏，半池本身就是 100 时不再重复显示
        if game.chips[uid] >= to_call + FIXED_MIN_RAISE and half_amt > FIXED_MIN_RAISE:
            rows.append([InlineKeyboardButton(f"➕ 加注 {FIXED_MIN_RAISE}", callback_data=f"texas_raise_{FIXED_MIN_RAISE}")])
    if game.chips[uid] > 0: rows.append([InlineKeyboardButton(f"🔥 全下 {game.chips[uid]}", callback_data="texas_allin")])
    return InlineKeyboardMarkup(rows)


async def update_poker_table(game, app):
    # 游戏开始后：把等待房消息直接编辑成牌桌（不删除；操作按钮在行动消息里）
    await safe_edit(app.bot, game.chat_id, game.game_msg_id, await poker_table_text(game, app), reply_markup=None)


async def start_turn_timer(game, app):
    game.cancel_timer()
    uid = game.current()
    if uid is None:
        if game.phase == "showdown": await settle_poker(game, app)
        return
    # 行动消息携带完整牌桌 + 行动提示 + 操作按钮（一条消息）
    await safe_delete(app.bot, game.chat_id, game.action_msg_id)
    text = f"{await poker_table_text(game, app)}\n\n⏰ <b>{await get_name(app, uid)}</b> 请在 {TURN_TIMEOUT} 秒内行动。"
    msg = await safe_send(app.bot, game.chat_id, text, reply_markup=poker_buttons(game, uid), parse_mode="HTML")
    game.action_msg_id = msg.message_id if msg else None

    # 真实超时任务：无需跟注自动过牌，否则自动弃牌，防止牌局卡死
    async def timeout_action():
        await asyncio.sleep(TURN_TIMEOUT)
        if game.settled or game.phase == "showdown": return
        if game.current() != uid: return  # 该玩家已行动过
        if game.round_bets[uid] == game.current_bet:
            ok, _ = game.action(uid, "check")
            if not ok: game.action(uid, "fold")
            desc = "超时自动过牌"
        else:
            game.action(uid, "fold")
            desc = "超时自动弃牌"
        await safe_send(app.bot, game.chat_id, f"⏰ {desc}：{await get_name(app, uid)}")
        if game.phase == "showdown":
            await safe_delete(app.bot, game.chat_id, game.action_msg_id)
            await settle_poker(game, app)
        else: await update_poker_table(game, app); await start_turn_timer(game, app)
    game.turn_task = asyncio.create_task(timeout_action())


async def settle_poker(game, app):
    if game.settled: return
    game.settled = True; game.cancel_timer(); game.cancel_auto(); game.cancel_wait()
    try:
        # 获取本局所有真实玩家的钱包锁，再执行 showdown 里的钱包写回，避免与同一用户的其他扣款路径并发
        async with user_wallet_locks([uid for uid in game.players if uid >= 0]):
            result = await game.showdown()
        if not result: raise RuntimeError("德州摊牌未生成结算结果")
        date, hand_types = business_date(), result[0][4]
        name_ids = set(game.players) | set(game.showdown_order)
        names = {uid: await get_name(app, uid) for uid in name_ids}
        board_text = "  ".join(card_str(card) for card in game.board) or "未发牌"
        lines = ["🃏 <b>德州结算</b>", "━━━━━━━━━━━━━━━━━", f"🃏 公牌：{board_text}", ""]

        if len(game.showdown_order) > 1:
            lines.append("亮牌：")
            for uid in game.players:
                if uid in game.folded: lines.extend([f"{names[uid]}：弃牌", ""])
                else: lines.extend([f"{names[uid]}：{'  '.join(card_str(card) for card in game.hands[uid])}｜{hand_types.get(uid, '')}", ""])
        else:
            lines.append("亮牌牌型：")
            for uid in game.players:
                if uid not in game.folded: lines.append(f"{names[uid]}：未亮牌")
                else: lines.append(f"{names[uid]}：弃牌")
            lines.append("")
        
        lines.append("派奖：")
        for uid, hand, amount, details, _ in sorted(result, key=lambda item: item[2], reverse=True):
            lines.extend([f"{names[uid]}：{hand}｜+{amount}（{'，'.join(f'{pool}+{value}' for pool, value in details)}）", ""])
        
        lines.append("投入 / 盈亏：")
        for uid in game.players:
            net = game.chips[uid] - game.initial_chips[uid]
            if game.season:
                pass  # 排位分已在 showdown 写回 season_points，不写当日榜
            elif game.mode == "official":
                poker_profit_by_date[date][game.chat_id][uid] += net
            lines.extend([f"{names[uid]}：投入 {game.total_bet[uid]}｜盈亏 {net:+d}", ""])

        # 排位赛：累计局数 + 破产应急补分（已取消淘汰；赛季已结束的进行中牌局只正常派奖、不计入、不误判破产）
        if game.season and season_active:
            for p in game.players:
                if p < 0: continue
                season_games[game.chat_id][p] += 1
            for p in game.players:
                if p < 0: continue
                if season_points[game.chat_id][p] <= 0:
                    if season_rebuy[game.chat_id][p] < SEASON_REBUY_COUNT:
                        season_rebuy[game.chat_id][p] += 1
                        season_points[game.chat_id][p] = SEASON_REBUY_AMOUNT
                        lines.append(f"⚠️ {names[p]} 破产，启用应急筹码 +{SEASON_REBUY_AMOUNT}（剩 {SEASON_REBUY_COUNT - season_rebuy[game.chat_id][p]} 次）")
            # 排位赛跨午夜补重置：本局横跨业务日结束，错过的午夜刷新在此补记当日盈亏并归位到起始分
            if game.start_date and business_date() != game.start_date:
                for uid in game.players:
                    if uid < 0: continue
                    final = season_points[game.chat_id][uid]
                    day_profit = final - SEASON_START_CHIPS
                    if day_profit:
                        season_profit_by_date[game.start_date][game.chat_id][uid] += day_profit
                    season_points[game.chat_id][uid] = SEASON_START_CHIPS
                    # 已取消淘汰机制：破产玩家当日剩余时间无法下注，次日 0 点重置为 {SEASON_START_CHIPS} 后可继续参赛

        if game.mode == "official" and not game.season:
            rank = sorted(poker_profit_by_date[date][game.chat_id].items(), key=lambda item: item[1], reverse=True)[:50]
            lines.extend(["", "🏆 <b>当日德州累计盈利榜</b>", "━━━━━━━━━━━━━━━━━"])
            lines.extend([f"{rank_marker(index)} {names.get(uid) or await get_name(app, uid)}：{amount:+d}" for index, (uid, amount) in enumerate(rank, 1)])
            
        delivered = await safe_send_long(app.bot, game.chat_id, "\n".join(lines), parse_mode="HTML")
        # 单赢场景（只剩一人未弃牌）：提供可选亮牌按钮，尊重德州 muck 规则，不强制亮牌
        if len(game.showdown_order) <= 1:
            winner = game.showdown_order[0] if game.showdown_order else None
            if winner is not None and game.hands.get(winner):
                btn = await safe_send(app.bot, game.chat_id,
                    "💡 本局单挑收池，赢家可选择亮出底牌：",
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🃏 亮牌", callback_data="texas_reveal")]]))
                # 入队而非覆盖：同一群可同时存在多局未亮牌的单赢
                recent_poker_reveals[game.chat_id].append({
                    "winner": winner,
                    "hand": list(game.hands[winner]),
                    "board": list(game.board),
                    "reveal_msg_id": btn.message_id if btn else None,
                })
                # 仅保留最近 5 条，避免极端情况下无限增长
                if len(recent_poker_reveals[game.chat_id]) > 5:
                    recent_poker_reveals[game.chat_id] = recent_poker_reveals[game.chat_id][-5:]
        if delivered is None:
            await safe_send(app.bot, game.chat_id, "⚠️ 德州已完成结算，但详细结算消息发送失败。")
    except Exception:
        logger.exception("德州结算异常")
    finally:
        if active_poker_games.get(game.chat_id) is game: active_poker_games.pop(game.chat_id, None)
        if game.mode == "official" and not game.season:
            for uid in game.players: await emergency_if_needed(game.chat_id, uid, app, game_chips, game)
        save_data(); await asyncio.to_thread(force_save_now)



async def handle_texas_reveal(cid, uid, q, context):
    """德州单赢后，点击「亮牌」按钮，把赢家两张底牌发到群（可选，不强制）。"""
    infos = recent_poker_reveals.get(cid, [])
    if not infos:
        await q.answer("本局亮牌数据已失效", show_alert=True); return
    # 按点击的亮牌按钮消息 id 精确匹配对应的一局，避免新单赢覆盖旧单赢后无法亮牌
    clicked_id = q.message.message_id if q.message else None
    info = next((it for it in infos if it.get("reveal_msg_id") == clicked_id), None)
    if info is None and len(infos) == 1:
        info = infos[0]  # 兜底：仅剩一条且按钮消息 id 无法匹配时直接取该条
    if info is None:
        await q.answer("本局亮牌数据已失效", show_alert=True); return
    if uid != info["winner"]:
        await q.answer("只有赢家本人能亮牌", show_alert=True); return
    name = await get_name(context.application, info["winner"])
    hand_text = "  ".join(card_str(c) for c in info["hand"])
    board_text = "  ".join(card_str(c) for c in info["board"]) if info["board"] else "（未发公牌）"
    await safe_send(context.bot, cid,
        f"🃏 <b>{name} 亮牌</b>：{hand_text}\n🃏 公牌：{board_text}（收全部底池）",
        parse_mode="HTML")
    rid = info.get("reveal_msg_id")
    if rid:
        await safe_edit(context.bot, cid, rid, "🃏 已亮牌", reply_markup=None)
    # 仅移除本条亮牌记录，其余未亮牌的单赢保留
    recent_poker_reveals[cid] = [it for it in infos if it is not info]
    if not recent_poker_reveals[cid]:
        recent_poker_reveals.pop(cid, None)
    await q.answer("已亮牌")


# ==================== 赛车 ====================
class HorseRace:
    def __init__(self, cid, owner, jackpot, mode=None):
        self.chat_id, self.owner_id, self.jackpot = cid, owner, jackpot
        self.mode = mode or current_game_mode()
        self.bets, self.total_bets, self.pool = defaultdict(dict), [0] * HORSE_COUNT, 0
        self.phase, self.create_time, self.positions, self.arrivals = "betting", time.time(), [0.0] * HORSE_COUNT, []
        self.display_positions = [0] * HORSE_COUNT  # 显示格（=节奏曲线进度的整数部分，严格跟随真实进度）
        self.arrival_times, self.race_start_time = {}, None
        self.notified, self.name_cache = set(), {}
        self.game_msg_id = self.animation_msg_id = None
        self.task, self.settled, self.cancelled, self.lock = None, False, False, asyncio.Lock()
        self.final_odds = None
        self.bet_odds = defaultdict(dict)  # 每注下注瞬间锁定的赔率（uid->horse 金额加权平均）
        rates = [random.uniform(.18, .35) for _ in range(HORSE_COUNT)]
        # 先按显示精度（整数%）四舍五入再归一化，避免"显示胜率相同、真实胜率不同"导致同胜率马赔率不同
        rates = [round(r, 2) for r in rates]
        total = sum(rates)
        self.rates = [value / total for value in rates]
        # 用胜率抽样每匹对象的精确完赛时间：长期获胜概率更接近显示胜率，仍保留随机爆冷。
        self.finish_durations = {}

    def odds(self):
        # 赔率 = 真实胜率的公平赔率(1/rate) × 注额压力因子
        # - 不设上限（用户要求），仅保留 1.05 地板防止「赢了还亏本」
        # - 注额越多 -> 因子越小 -> 赔率越低（热门马赔得少，标准押注池逻辑）
        # - 单调约束：胜率越低赔率必须越高，杜绝「低胜率马赔率反而更低」的怪象
        total = sum(self.total_bets)
        avg = 1.0 / HORSE_COUNT
        raw = []
        for i in range(HORSE_COUNT):
            base = 1.0 / self.rates[i]                       # 自然公平赔率，无封顶
            if total > 0 and self.total_bets[i] > 0:
                share = self.total_bets[i] / total
                factor = (avg / share) ** 0.5                # 押注占比越高 -> 因子越小
                factor = max(0.4, min(factor, 2.5))          # 限制单匹摆动幅度，保证可读
            else:
                factor = 1.0
            raw.append(base * factor)
        # 单调约束：按胜率升序，确保低胜率马的赔率不低于高胜率马
        order = sorted(range(HORSE_COUNT), key=lambda i: self.rates[i])
        for a, b in zip(order, order[1:]):
            if raw[a] < raw[b]:
                raw[b] = raw[a]
        # 同显示胜率（整数%）的馬，赔率必须完全一致，避免"胜率一样赔率却不同"的困惑。
        # 取组内最低赔率统一，不抬高任一匹，保证庄家不被过度赔付。
        groups = {}
        for i in range(HORSE_COUNT):
            groups.setdefault(round(self.rates[i] * 100), []).append(i)
        for grp in groups.values():
            if len(grp) > 1:
                lo = min(raw[i] for i in grp)
                for i in grp:
                    raw[i] = lo
        return [max(1.05, v) for v in raw]

    async def bet(self, uid, horse, amount):
        if self.phase != "betting" or self.cancelled: return False, "当前不是下注阶段"
        wallet = game_chips
        if not 0 <= horse < HORSE_COUNT or amount <= 0: return False, "马号或金额无效"
        async with wallet_locks[uid]:
            # 锁内重校阶段：等锁期间比赛可能已开跑，避免按旧赔率接受下注
            if self.phase != "betting" or self.cancelled: return False, "当前不是下注阶段"
            if amount > wallet[self.chat_id][uid]: return False, "积分不足"
            # 先按「下注前」赔率锁定（即玩家在界面上看到的赔率），确保看到=拿到
            o = self.odds()[horse]
            wallet[self.chat_id][uid] -= amount; self.pool += amount; self.total_bets[horse] += amount
        self.bets[uid][horse] = self.bets[uid].get(horse, 0) + amount
        prev_amt = self.bets[uid][horse] - amount
        prev_odd = self.bet_odds[uid].get(horse)
        self.bet_odds[uid][horse] = o if prev_odd is None else (prev_amt * prev_odd + amount * o) / (prev_amt + amount)

        # 记录退款保护
        curr_pending = pending_game_bets[self.chat_id][uid].get("horse", {}).get("amount", 0)
        pending_game_bets[self.chat_id][uid]["horse"] = {"amount": curr_pending + amount, "mode": self.mode}
        save_data(); return True, "下注成功"

    def buttons(self):
        return InlineKeyboardMarkup([[InlineKeyboardButton(f"{HORSE_EMOJI[i]} {amount}", callback_data=f"horsebet_{i}_{amount}") for i in range(HORSE_COUNT)] for amount in FIXED_BET_AMOUNTS])

    async def view(self, app):
        """保持原版赛车下注界面的赛道、路书、胜率和投注信息结构。"""
        remain = max(0, int(RACE_AUTO_START - (time.time() - self.create_time)))
        minutes, seconds = divmod(remain, 60)
        history = "".join(HORSE_EMOJI[index] for index in race_history[self.chat_id][-10:]) or "暂无"
        stats = race_daily_stats[self.chat_id]
        total_wins = sum(stats)
        odds = self.odds()
        lines = [
            f"🏁 赛车大赛 {race_id(self.create_time)} 🏁 【下注中】",
            "━" * 14,
            *[f"🏁{'━' * 13}{HORSE_EMOJI[i]}" for i in range(HORSE_COUNT)],
            "━" * 14,
            "📊 路书",
            f"近10场: {history}",
            "📜 当日胜率:",
            "  " + " | ".join(f"{HORSE_EMOJI[i]} {stats[i]}胜" for i in range(HORSE_COUNT)),
            "  " + " | ".join(f"{HORSE_EMOJI[i]} {stats[i] / total_wins * 100:.0f}%" if total_wins else f"{HORSE_EMOJI[i]} 0%" for i in range(HORSE_COUNT)),
            "📊 投注情况:",
        ]
        for i, odd in enumerate(odds):
            lines.append(f"{HORSE_EMOJI[i]} {HORSE_NAMES[i]}: 胜率{self.rates[i] * 100:.0f}% | {self.total_bets[i]}积分 | 赔率 {odd:.2f}x")
        lines.append("━" * 14)
        if self.bets:
            lines.append("📋 玩家下注：")
            for uid, bets in self.bets.items():
                name = self.name_cache.get(uid) or await get_name(app, uid)
                self.name_cache[uid] = name
                lines.append(f"{name}: " + " ".join(f"{HORSE_EMOJI[h]}{amount}" for h, amount in bets.items()))
            lines.append("")
        lines.extend([f"⏰ 距离开赛还有 {minutes} 分 {seconds:02d} 秒", "🔒 开赛后无法投注", "💡 赔率随下注实时浮动，下注瞬间锁定"])
        return "\n".join(lines)

    def animation(self):
        lines = ["🏁 赛车进行中", "━" * 14]
        for i, pos in enumerate(self.display_positions):
            track_pos = max(0, min(RACE_TRACK_LENGTH, int(pos)))
            track = "🏁" + (HORSE_EMOJI[i] + "━" * RACE_TRACK_LENGTH if track_pos >= RACE_TRACK_LENGTH else "━" * (RACE_TRACK_LENGTH - track_pos - 1) + HORSE_EMOJI[i] + "━" * track_pos)
            lines.append(track)
        if self.arrivals: lines.append("✅ 到达：" + " ".join(HORSE_EMOJI[i] for i in self.arrivals))
        return "\n".join(lines)

    async def _push_animation_frame(self, app):
        """先删旧帧、再发新帧（每帧以新消息出现在群底部，无双画面堆叠）。
        发送/删除都完整尊重 429 的 retry_after 重试——之前画面冻结的根因是
        safe_send/safe_delete 吞掉限流错误，而不是删发顺序本身。"""
        text = self.animation()
        old_id, self.animation_msg_id = self.animation_msg_id, None
        if old_id:
            for _ in range(3):
                try:
                    await app.bot.delete_message(chat_id=self.chat_id, message_id=old_id)
                    break
                except RetryAfter as exc:
                    await asyncio.sleep(min(exc.retry_after + 0.5, 25))
                except TelegramError:
                    break
        msg = None
        for _ in range(4):  # 发送最多重试 4 次并按 Telegram 要求等待，保证帧必达、不冻结
            try:
                msg = await app.bot.send_message(chat_id=self.chat_id, text=text)
                break
            except RetryAfter as exc:
                await asyncio.sleep(min(exc.retry_after + 0.5, 25))
            except TelegramError:
                logger.exception("赛车动画帧发送失败: %s", self.chat_id)
                break
        self.animation_msg_id = msg.message_id if msg else None

    async def run(self, app):
        try:
            # 统一通知点：60秒, 30秒
            thresholds = [60, 30]
            while self.phase == "betting" and not self.cancelled:
                # 实时计算剩余时间
                remain = max(0, int(RACE_AUTO_START - (time.time() - self.create_time)))
                
                # 只有在整秒点附近才发出推送通知，防止重复发送
                for threshold in thresholds:
                    if remain <= threshold and threshold not in self.notified:
                        self.notified.add(threshold)
                        await safe_send(app.bot, self.chat_id, f"⏰ 赛车还剩 {threshold // 60} 分钟 {threshold % 60} 秒！")
                
                if not remain: break
                
                # 实时刷新主面板
                await safe_edit(app.bot, self.chat_id, self.game_msg_id, await self.view(app), reply_markup=self.buttons())
                
                # 界面刷新与通知检查间隔 30 秒
                await asyncio.sleep(min(30, max(1, remain)))

            if self.cancelled: return
            self.phase = "racing"
            self.final_odds = self.odds()
            self.race_start_time = time.time()
            await safe_edit(app.bot, self.chat_id, self.game_msg_id, "🏁 比赛开始！正在奔跑中……", reply_markup=None)
            msg = await safe_send(app.bot, self.chat_id, "🏁 比赛开始！正在奔跑中……"); self.animation_msg_id = msg.message_id if msg else None
            # 先按胜率加权抽取完整名次，再分配有间隔的完赛时间。
            # 这样长期夺冠率接近显示胜率，同时不会出现开赛第一帧直接到终点。
            remaining = list(range(HORSE_COUNT))
            finish_order = []
            while remaining:
                total_rate = sum(self.rates[index] for index in remaining)
                target = random.uniform(0, total_rate)
                cumulative = 0.0
                for index in remaining:
                    cumulative += self.rates[index]
                    if cumulative >= target:
                        finish_order.append(index)
                        remaining.remove(index)
                        break
            # 赛程总时长 = minimum_duration + 3*finish_gap = 70 秒
            # 配合 RACE_ANIMATION_INTERVAL=5.0 与 RACE_TRACK_LENGTH=14 → 约 15 帧、每帧走 1 格
            minimum_duration = 55.0
            finish_gap = 5.0
            self.finish_durations = {
                horse: minimum_duration + rank * finish_gap + random.uniform(-0.20, 0.20)
                for rank, horse in enumerate(finish_order)
            }
            # 节奏分配（v2.9）：每辆车一条单调节奏曲线 f(p) = p ± a·sin(pπ) —— f(0)=0, f(1)=1,
            # 完赛时刻与名次分毫不差，但中段节奏不同 → 真实反超/守擂戏码。
            # 方向与幅度全随机（冠军不特殊，先慢后快/先快后慢各半，25% 概率接近匀速），每场剧本不重样。
            # a 上限按各车完赛时长收紧，保证最慢段每帧仍 +≥1 格（不钉死）；曲线单调 → 无倒退。
            # 显示 = int(真实节奏进度)，无累积/无强制步长 → 显示与真实严格同步，零失真。
            self.race_tempo = {}
            for rank, horse in enumerate(finish_order):
                T = self.finish_durations[horse]
                a_cap = max(0.0, (1 - T / (RACE_TRACK_LENGTH * RACE_ANIMATION_INTERVAL)) / math.pi)
                if random.random() < 0.25:
                    a = random.uniform(0.05, 0.35) * a_cap    # 四分之一概率接近匀速，增加剧本多样性
                else:
                    a = random.uniform(0.4, 0.95) * a_cap
                sign = random.choice([-1, 1])                  # -1 先慢后快（反超），+1 先快后慢（守擂）
                self.race_tempo[horse] = (sign, a)
            while not self.cancelled and len(self.arrivals) < HORSE_COUNT:
                now = time.time()
                for i in range(HORSE_COUNT):
                    if i in self.arrival_times:
                        continue
                    duration = self.finish_durations[i]
                    progress = min(1.0, max(0.0, (now - self.race_start_time) / duration))
                    sign, amp = self.race_tempo.get(i, (0, 0.0))
                    tempo = progress + sign * amp * math.sin(progress * math.pi)
                    self.positions[i] = max(0.0, min(float(RACE_TRACK_LENGTH),
                                                     RACE_TRACK_LENGTH * tempo))
                    if progress >= 1.0:
                        self.arrival_times[i] = self.race_start_time + duration
                        self.positions[i] = float(RACE_TRACK_LENGTH)
                        self.display_positions[i] = RACE_TRACK_LENGTH
                    else:
                        # 画面格子严格跟随真实节奏进度：既不超前（不会提前压线）也不滞后（不会钉死）
                        self.display_positions[i] = max(0, min(RACE_TRACK_LENGTH, int(self.positions[i])))
                self.arrivals = sorted(self.arrival_times, key=self.arrival_times.get)
                await self._push_animation_frame(app)
                if len(self.arrivals) < HORSE_COUNT: await asyncio.sleep(RACE_ANIMATION_INTERVAL)
            if not self.cancelled: await self.settle(app)
        except asyncio.CancelledError: raise
        except Exception:
            logger.exception("赛车任务异常")
            if not self.settled:
                await self.refund(app, "⚠️ 赛车异常，所有下注已退款。")

    async def settle(self, app):
        async with self.lock:
            if self.settled or self.cancelled: return
            self.settled, self.phase = True, "settling"
            payouts_applied = False
            try:
                if not self.arrivals: raise RuntimeError("赛车未产生到达顺序")
                winner, date = self.arrivals[0], business_date()
                fallback_odd = (self.final_odds or self.odds())[winner]
                if self.mode == "official":
                    race_daily_stats[self.chat_id][winner] += 1
                    race_history[self.chat_id] = (race_history[self.chat_id] + [winner])[-10:]
                standings = ["🥇", "🥈", "🥉", "🏅"]
                lines = [f"🏆 赛车大赛 {race_id(self.create_time)} 结果 🏆", "━━━━━━━━━━━━━━━━━"]
                lines.extend(f"{standings[index]} {HORSE_EMOJI[horse]} {HORSE_NAMES[horse]}" for index, horse in enumerate(self.arrivals))

                # 先获取所有玩家名字：避免派彩后因取名字失败触发异常退款，导致已派彩玩家被双重派彩
                for uid in self.bets:
                    if uid not in self.name_cache: self.name_cache[uid] = await get_name(app, uid)

                # 阶段一：计算派彩并记录盈亏（不动钱包，避免中途异常导致已派彩玩家被双重退款）
                settlements, total_payout = [], 0
                wallet = game_chips
                for uid, bets in self.bets.items():
                    stake = sum(bets.values()); bet_on_winner = bets.get(winner, 0)
                    bet_odd = self.bet_odds[uid].get(winner, fallback_odd)
                    payout = int(bet_on_winner * bet_odd)
                    net = payout - stake
                    if self.mode == "official":
                        race_profit_by_date[date][self.chat_id][uid] += net
                    settlements.append((uid, self.name_cache[uid], stake, bet_on_winner, payout, net, bet_odd))
                # 阶段二：统一改写钱包（此处仅 dict 操作，不会抛异常，payouts_applied 必定置位）
                for uid, _, _, _, payout, _, _ in settlements:
                    wallet[self.chat_id][uid] += payout; total_payout += payout
                payouts_applied = True

                available_pool = self.jackpot + self.pool
                supplement = max(0, total_payout - available_pool)
                if self.mode == "official":
                    race_jackpot[self.chat_id] = max(0, available_pool - total_payout)
                if supplement:
                    lines.extend(["", f"⚠️ 奖池不足，系统补充 {supplement} 积分"])
                elif not total_payout:
                    lines.extend(["", "🔄 无人押中，奖池滚入下一期。"])

                lines.extend(["", "💰 本局结算："])
                for _, name, stake, bet_on_winner, payout, net, bo in settlements:
                    if bet_on_winner > 0:
                        lines.append(f"{name}：总投注 {stake}｜命中 {bet_on_winner}（{bo:.2f}x）｜派彩 {payout}｜净 {net:+d}")
                    else:
                        lines.append(f"{name}：总投注 {stake}｜未命中｜净 {net:+d}")

                if self.mode == "official":
                    day_rank = sorted(total_profit_by_game(race_profit_by_date, self.chat_id).items(), key=lambda item: item[1], reverse=True)[:50]
                    lines.extend(["", "🏆 <b>赛车累计盈利榜（总数）</b>", "━━━━━━━━━━━━━━━━━"])
                    for index, (uid, amount) in enumerate(day_rank, 1):
                        name = self.name_cache.get(uid)
                        if not name:
                            name = await get_name(app, uid)
                            self.name_cache[uid] = name
                        lines.append(f"{rank_marker(index)} {name}：{amount:+d}")
                else:
                    lines.extend(["", "🎮 娱乐局：本局不计入正式盈亏榜。"])
                
                self.phase = "finished"; save_data(); await asyncio.to_thread(force_save_now)
                # 清除退款记录
                for uid in self.bets: pending_game_bets[self.chat_id].get(uid, {}).pop("horse", None)
                delivered = await safe_send_long(app.bot, self.chat_id, "\n".join(lines), parse_mode="HTML")

                if delivered is None:
                    await safe_send(app.bot, self.chat_id, "⚠️ 赛车已完成结算，但详细结果消息发送失败。积分与当日盈亏已保存，可使用 /cx 查看排行榜。")
            except Exception:
                logger.exception("赛车结算异常，群 %s", self.chat_id)
                # 仅在尚未派彩时退款，避免已派彩玩家被双重派彩
                if not payouts_applied:
                    wallet = game_chips
                    for uid, bets in self.bets.items():
                        wallet[self.chat_id][uid] += sum(bets.values())
                    if self.mode == "official": race_jackpot[self.chat_id] = self.jackpot
                    await safe_send(app.bot, self.chat_id, "⚠️ 赛车结算异常，本局已退款以保护玩家积分。")
                else:
                    await safe_send(app.bot, self.chat_id, "⚠️ 赛车结算显示异常，派彩已保存，可使用 /cx 查看排行榜。")
                save_data()
            finally:
                await safe_delete(app.bot, self.chat_id, self.animation_msg_id)
                if active_horse_races.get(self.chat_id) is self: active_horse_races.pop(self.chat_id, None)
                if self.mode == "official":
                    for uid in self.bets: await emergency_if_needed(self.chat_id, uid, app)

    async def refund(self, app, notice):
        async with self.lock:
            if self.cancelled: return
            self.cancelled, self.phase = True, "cancelled"
            wallet = game_chips
            for uid, bets in self.bets.items(): 
                wallet[self.chat_id][uid] += sum(bets.values())
                pending_game_bets[self.chat_id].get(uid, {}).pop("horse", None)
            # 奖池不再在开局时弹出，故取消/退款时无需回写（race_jackpot[cid] 始终保留原始奖池）
            save_data()
            if active_horse_races.get(self.chat_id) is self: active_horse_races.pop(self.chat_id, None)
            await safe_edit(app.bot, self.chat_id, self.game_msg_id, notice, reply_markup=None)


# ---------- 权限与命令 ----------
def is_auth(cid): return cid in AUTHORIZED_GROUPS
def is_bot_admin(uid): return uid in BOT_ADMINS
async def need_auth(update):
    # 授权只针对「群聊」：私聊没有群组概念，不应被「群组未授权」拦截。
    # 私聊里真正受限的游戏/管理命令，各自还有 require_group_chat / is_bot_admin 兜底。
    chat = update.effective_chat
    if chat and chat.type in ("group", "supergroup"):
        if not is_auth(chat.id):
            if update.effective_message: await update.effective_message.reply_text("❌ 此群组未授权，请联系管理员。")
            return False
    return True


def is_group_chat(update):
    """消息是否来自群聊/超级群（多人游戏只能在此发起，私聊开别人看不到）。"""
    chat_type = update.effective_chat.type if update.effective_chat else None
    return chat_type in ("group", "supergroup")


async def require_group_chat(update, game_name, cmd):
    """多人游戏必须在群聊发起；私聊里开只有发起人自己看得到。返回 False 时已回复提示。"""
    if not is_group_chat(update):
        await update.message.reply_text(
            f"⚠️ {game_name}是多人游戏，请在群聊中发起（发送 /{cmd}），别人才能一起玩。私聊里开只有你自己看得到。")
        return False
    return True

async def cmd_start(update, context):
    if not await need_auth(update): return
    text = "🎮 欢迎使用娱乐机器人！\n\n🎲 发起游戏：\n/开始 或 /菜单 - 查看本帮助\n/德州 - 发起德州扑克（统一积分）\n/赛车 - 发起赛车\n/21点 - 发起21点\n/炸金花 - 发起炸金花（闷牌偷鸡）\n\n💰 积分系统：\n/签到 - 每日签到领积分\n/我的积分 - 积分/等级/签到状态\n/积分排行 - 积分排行榜\n/积分商城 - 用积分换好物\n红包 总数 份数 - 发积分红包（如：红包 1000 5）\n转赠 数量 - 把积分转给群里成员（回复消息用）\n充值 数量 - 申请购买积分（管理员确认到账）\n\n📊 数据查询：\n/盈亏 - 当日盈亏榜\n/排行 - 总积分榜\n/结束 - 终止当前游戏\n\n🏪 称号商店：\n/商店 - 查看可兑换称号\n/兑换 称号名 - 用积分换称号"
    if is_bot_admin(update.effective_user.id):
        text += "\n\n🔧 管理命令（仅管理员）：\n/授权 - 授权当前群使用\n取消授权 - 取消群授权\n/授权列表 - 查看已授权群\n/加管理员 /减管理员 /管理员列表\n/加积分(负数即减) /赛季分\n/拍卖 物品 起拍价 - 发起积分拍卖\n/拉黑 /解黑 /黑名单 - 封禁违规玩家\n/列表 - 管理总览(管理员/授权群/黑名单三合一)\n/备份 /恢复\n💡 快捷加减分：在群里回复某玩家的消息，然后发「/add 数量」即可给他加/减分（负数即减），不用输ID"
    await update.message.reply_text(text)

# ---------- 21点 界面与逻辑 ----------
async def start_bj_turn_timer(game, app):
    game.cancel_timer()
    curr_uid = game.players[game.current_player_idx]
    async def timeout():
        await asyncio.sleep(TURN_TIMEOUT)
        if active_blackjack_games.get(game.chat_id) is not game: return  # 游戏已终止或被替换
        if game.phase == "playing" and game.players[game.current_player_idx] == curr_uid:
            game.next_player()
            await safe_send(app.bot, game.chat_id, f"⏰ {await get_name(app, curr_uid)} 超时自动停牌。")
            if game.phase == "dealer_turn": await update_blackjack_ui(game, app)
            else: await update_blackjack_ui(game, app); await start_bj_turn_timer(game, app)
    game.timer_task = asyncio.create_task(timeout())

async def start_bj_wait_timeout(game, app):
    """21点等待房 60 秒倒计时：有人加入则自动开局，无人加入自动解散。"""
    game.cancel_wait()
    async def expire():
        await asyncio.sleep(ROOM_WAIT_TIMEOUT)
        if game.phase != "waiting" or active_blackjack_games.get(game.chat_id) is not game:
            return
        if game.players:
            if game.start():
                await update_blackjack_ui(game, app)
                await start_bj_turn_timer(game, app)
        else:
            active_blackjack_games.pop(game.chat_id, None)
            await safe_edit(app.bot, game.chat_id, game.game_msg_id, "⌛ 21点等待 60 秒无人加入，房间已自动解散。", reply_markup=None)
    game.wait_task = asyncio.create_task(expire())


async def build_blackjack_wait_board(game, app):
    """构建 21点 等待房间阶段的看板（文本+按钮），供首发与重发复用。"""
    history_list = "".join(blackjack_history[game.chat_id][-10:]) or "暂无"
    text = (
        f"🃏 <b>21点 (Blackjack)</b>\n"
        f"━━━━━━━━━━━━━━━━━\n"
        f"📊 <b>庄家路书</b>：{history_list}\n\n"
        f"发起人：{await get_name(app, game.owner_id)}\n\n"
        f"已加入：\n"
    )
    for uid in game.players:
        text += f"- {await get_name(app, uid)} (下注: {game.bets[uid]})\n"
    text += "\n⏰ 有人加入后 60 秒自动开局，无人加入自动解散。\n"
    kb = [[InlineKeyboardButton(f"📥 加入 (下注{b})", callback_data=f"bj_join_{b}") for b in BJ_JOIN_BETS]]
    if game.players: kb.append([InlineKeyboardButton("🎮 开始游戏", callback_data="bj_start")])
    kb.append([InlineKeyboardButton("❌ 终止", callback_data="bj_end")])
    return text, InlineKeyboardMarkup(kb)


async def update_blackjack_ui(game, app):
    if game.phase == "waiting":
        text, kb = await build_blackjack_wait_board(game, app)
        if game.game_msg_id:
            await safe_edit(app.bot, game.chat_id, game.game_msg_id, text, reply_markup=kb, parse_mode="HTML")
        else:
            msg = await safe_send(app.bot, game.chat_id, text, reply_markup=kb, parse_mode="HTML")
            if msg: game.game_msg_id = msg.message_id
    elif game.phase == "playing":
        curr_uid = game.players[game.current_player_idx]
        text = f"🃏 <b>21点 进行中</b>\n\n🏛 <b>庄家</b>：{game.get_card_str(game.dealer_hand, True)}\n\n"
        for uid in game.players:
            mark = " 👈 <b>行动中</b>" if uid == curr_uid else ""
            text += f"👤 <b>玩家</b>：{await get_name(app, uid)} | {game.get_card_str(game.hands[uid])} ({game.get_score(game.hands[uid])}){mark}\n\n"
        
        # 1. 原地更新主面板文字
        await safe_edit(app.bot, game.chat_id, game.game_msg_id, text, reply_markup=None, parse_mode="HTML")
        
        # 2. 动态发送/更新底部的操作按钮
        await safe_delete(app.bot, game.chat_id, game.game_msg_id if game.phase == "waiting" else game.action_msg_id)
        
        dealer_peek = game.get_card_str(game.dealer_hand, True)
        my_hand = game.get_card_str(game.hands[curr_uid])
        my_score = game.get_score(game.hands[curr_uid])
        
        action_text = (
            f"⏰ <b>玩家</b>：{await get_name(app, curr_uid)}\n\n"
            f"🏛 <b>庄家</b>：{dealer_peek}\n\n"
            f"👤 <b>我的</b>：{my_hand} ({my_score}点)"
        )
        
        kb_rows = [[
            InlineKeyboardButton("🃏 要牌 (Hit)", callback_data=f"bj_hit_{curr_uid}"),
            InlineKeyboardButton("✋ 停牌 (Stand)", callback_data=f"bj_stand_{curr_uid}")
        ]]
        
        wallet = game_chips
        if len(game.hands[curr_uid]) == 2 and wallet[game.chat_id][curr_uid] >= game.bets[curr_uid] and not game.is_blackjack(game.hands[curr_uid]):
            kb_rows.append([InlineKeyboardButton("💰 双倍 (Double Down)", callback_data=f"bj_double_{curr_uid}")])
        
        msg = await safe_send(app.bot, game.chat_id, action_text, reply_markup=InlineKeyboardMarkup(kb_rows), parse_mode="HTML")
        if msg: game.action_msg_id = msg.message_id
    elif game.phase == "dealer_turn":
        # 庄家补牌后直接进入结算（消息删除由 finished 分支统一处理，避免重复删除）
        game.dealer_play()
        # 确保跳转到 finished 逻辑
        await update_blackjack_ui(game, app)
    elif game.phase == "finished":
        if getattr(game, "settled", False):
            return
        game.settled = True
        # 增加整体 try-except 保护
        try:
            payments_applied = False
            await safe_delete(app.bot, game.chat_id, game.action_msg_id)
            d_score = game.get_score(game.dealer_hand)
            text = f"🃏 <b>21点 结算</b>\n━━━━━━━━━━━━━━━━━\n🏛 <b>庄家</b>：{game.get_card_str(game.dealer_hand)} ({d_score})\n\n"
            date = business_date()
            wallet = game_chips

            lines = []
            # 预先获取所有名字，提高 HTML 生成速度
            player_names = {}
            for uid in game.players: player_names[uid] = await get_name(app, uid)

            # ===== 阶段一：只计算派彩，绝不动钱包（先算后付，杜绝中途异常双重退款）=====
            payouts_done = False
            payments_applied = False
            payout_plan = []  # (uid, payout, net)
            for uid in game.players:
                p_score = game.get_score(game.hands[uid])
                bet = game.bets[uid]
                result_str = ""
                payout = 0
                
                dealer_bj = game.is_blackjack(game.dealer_hand)
                player_bj = game.is_blackjack(game.hands[uid])
                if p_score > 21:
                    result_str = "💥 爆牌 (负)"; payout = 0
                elif dealer_bj and not player_bj:
                    result_str = "🏛 庄家天生21 (负)"; payout = 0
                elif d_score > 21:
                    if player_bj: result_str = "🃏 Blackjack (胜)"; payout = int(bet * 2.5)
                    else: result_str = "🏛 庄爆 (胜)"; payout = bet * 2
                elif p_score > d_score:
                    if player_bj: result_str = "🃏 Blackjack (胜)"; payout = int(bet * 2.5)
                    else: result_str = "🎉 获胜"; payout = bet * 2
                elif p_score < d_score:
                    result_str = "💸 战败"; payout = 0
                else:
                    if player_bj and dealer_bj: result_str = "🤝 双天生21 平局"; payout = bet
                    else: result_str = "🤝 平局"; payout = bet
                
                net = payout - bet
                hand_text = game.get_card_str(game.hands[uid])
                lines.append(f"👤 <b>玩家</b>：{player_names[uid]} | {hand_text} ({p_score})\n<b>结果</b>：{result_str} | 盈亏 {net:+d}")
                payout_plan.append((uid, payout, net))

            # ===== 阶段二：全部算成功后，统一改钱包 + 写盈亏 + 清退款记录 =====
            async with user_wallet_locks([uid for uid, _, _ in payout_plan]):
                for uid, payout, net in payout_plan:
                    wallet[game.chat_id][uid] += payout
                    if game.mode == "official":
                        blackjack_profit_by_date[date][game.chat_id][uid] += net
                    pending_game_bets[game.chat_id].get(uid, {}).pop("21", None)
            payments_applied = True
            payouts_done = True
            save_data(); await asyncio.to_thread(force_save_now)

            # 记录庄家历史 (仅记录本局主要趋势)
            if game.mode == "official":
                # 计算本局玩家总体输赢，用于生成庄家路书图标
                total_net = sum(net for (uid, payout, net) in payout_plan)
                history_icon = "🏛" if total_net < 0 else ("🤝" if total_net == 0 else "👤")
                blackjack_history[game.chat_id] = (blackjack_history[game.chat_id] + [history_icon])[-10:]

            text += "\n\n".join(lines)
            
            if game.mode == "official":
                bj_rank = sorted(total_profit_by_game(blackjack_profit_by_date, game.chat_id).items(), key=lambda item: item[1], reverse=True)[:30]
                text += "\n\n🏆 <b>21点 累计盈利榜（总数）</b>\n"
                rank_lines = []
                for i, (u, a) in enumerate(bj_rank, 1):
                    name = game.name_cache.get(u) or await get_name(app, u)
                    game.name_cache[u] = name
                    rank_lines.append(f"{rank_marker(i)} {name}：{a:+d}")
                text += "\n".join(rank_lines)
                
            await safe_delete(app.bot, game.chat_id, game.game_msg_id)
            await safe_send_long(app.bot, game.chat_id, text, parse_mode="HTML")
        except Exception:
            logger.exception("21点结算显示失败")
            if not payments_applied:
                # 派彩前出错，退还投注
                wallet = game_chips
                for uid in game.players:
                    wallet[game.chat_id][uid] += game.bets[uid]
                await safe_send(app.bot, game.chat_id, "⚠️ 21点结算异常，本局已退款，积分不受影响。")
            else:
                await safe_send(app.bot, game.chat_id, "⚠️ 21点已结算，但由于 HTML 渲染问题无法显示详细战报。积分已保存。")
        finally:
            active_blackjack_games.pop(game.chat_id, None)
            save_data()







async def cmd_21(update, context):
    if not await need_auth(update): return
    if not await require_group_chat(update, "21点", "21"): return
    cid, uid = update.effective_chat.id, update.effective_user.id
    if cid in active_blackjack_games:
        g = active_blackjack_games[cid]
        if g.phase == "waiting":
            text, kb = await build_blackjack_wait_board(g, context.application)
            msg = await safe_send(context.bot, cid, text, reply_markup=kb, parse_mode="HTML")
            if msg: g.game_msg_id = msg.message_id
        else:
            await update.message.reply_text("当前已有 21点 进行中。")
        return
    mode = current_game_mode()
    game = BlackjackGame(cid, uid, mode)
    active_blackjack_games[cid] = game
    # 发起人自动入座（按最低档加入下注；余额不足则仅建房不占座，与其他游戏对齐）
    bet0 = BJ_JOIN_BETS[0] if BJ_JOIN_BETS else 500
    async with wallet_locks[uid]:
        if game_chips[cid][uid] >= bet0 and game.add_player(uid, bet0):
            game_chips[cid][uid] -= bet0
    await update_blackjack_ui(game, context.application)  # 直接发送等待房界面，无"准备中"占位
    await start_bj_wait_timeout(game, context.application) # 启动等待超时

# ==================== 骰子 ====================



















# ==================== 通用 sendDice 游戏（足球/篮球/飞镖/保龄球） ====================

# 配置：每个游戏一个条目。bets 每项为 (key, 按钮标签, 赢的value集合, 赔率分子, 赔率分母)
























# ==================== 梭哈（Five Card Stud） ====================
# treys suit_int 是位掩码（s=1,h=2,d=4,c=8），映射为梭哈花色优先级 ♠>♥>♦>♣
























# ==================== 炸金花（三张牌，闷牌偷鸡） ====================
JINHUA_ANTE = 200        # 炸金花底注
JINHUA_BASE = 100        # 闷牌单位（看牌者跟注/加注金额为其 2 倍）
JINHUA_HAND_NAMES = {5: "豹子", 4: "同花顺", 3: "金花", 2: "顺子", 1: "对子", 0: "散牌"}


def evaluate_jinhua(cards):
    """炸金花 3 张牌牌型：返回 (等级, 比较键)。等级 5豹子 > 4同花顺 > 3金花 > 2顺子 > 1对子 > 0散牌。
    rank_int: 2=0...A=12；A23 是最小顺子（rank 12,0,1）。"""
    ranks = sorted([Card.get_rank_int(c) for c in cards], reverse=True)
    suits = [Card.get_suit_int(c) for c in cards]
    is_flush = len(set(suits)) == 1
    is_straight = (ranks[0] == ranks[1] + 1 == ranks[2] + 2) or (ranks == [12, 1, 0])
    counts = {}
    for r in ranks:
        counts[r] = counts.get(r, 0) + 1
    if len(counts) == 1:
        return (5, (ranks[0],))
    if is_straight and is_flush:
        return (4, (1 if ranks == [12, 1, 0] else ranks[0],))
    if is_flush:
        return (3, tuple(ranks))
    if is_straight:
        return (2, (1 if ranks == [12, 1, 0] else ranks[0],))
    if len(counts) == 2:
        pair_rank = [r for r, c in counts.items() if c == 2][0]
        kicker = [r for r, c in counts.items() if c == 1][0]
        return (1, (pair_rank, kicker))
    return (0, tuple(ranks))


def is_235(cards):
    """不同花的 2、3、5（散牌最小，但专杀豹子）。rank: 2=0,3=1,5=3"""
    ranks = sorted([Card.get_rank_int(c) for c in cards])
    suits = [Card.get_suit_int(c) for c in cards]
    return ranks == [0, 1, 3] and len(set(suits)) == 3


def jinhua_winners(hands_map):
    """炸金花比牌：返回赢家 uid 列表。235 专杀豹子。"""
    alive = list(hands_map.keys())
    has_235 = [uid for uid in alive if is_235(hands_map[uid])]
    has_triple = [uid for uid in alive if evaluate_jinhua(hands_map[uid])[0] == 5]
    if has_235 and has_triple:
        return sorted(has_235)  # 235 专杀豹子
    best = max(evaluate_jinhua(hands_map[uid]) for uid in alive)
    return sorted(uid for uid in alive if evaluate_jinhua(hands_map[uid]) == best)


def compare_jinhua_pair(challenger, target, hands):
    """炸金花官方比牌（点对点）：返回 'challenger' 或 'target'。
    235 专杀豹子；其余按标准牌型比较。平局（含双方都235/都豹子）→ 先比者(挑战方)输，返回 'target'。"""
    hc, ht = hands[challenger], hands[target]
    c235, t235 = is_235(hc), is_235(ht)
    ctriple = evaluate_jinhua(hc)[0] == 5
    ttriple = evaluate_jinhua(ht)[0] == 5
    if c235 and ttriple: return "challenger"   # 235 杀豹子
    if t235 and ctriple: return "target"        # 豹子被235杀，挑战方胜
    if evaluate_jinhua(hc) > evaluate_jinhua(ht): return "challenger"
    return "target"  # 挑战方牌小或平局 → 先比者输


class JinhuaGame:
    """炸金花：3 张暗牌，闷牌（不看牌下注）与看牌（看牌者 2 倍跟），跟平后可开牌或继续加注。"""

    def __init__(self, cid, owner, mode=None):
        self.chat_id, self.owner_id, self.mode, self.phase = cid, owner, mode or current_game_mode(), "waiting"
        self.players, self.chips, self.initial_chips = [], {}, {}
        self.total_bet, self.round_bets = {}, {}
        self.hands = {}        # uid -> [3张牌]
        self.seen = set()      # 已看牌玩家（看牌者下注翻倍）
        self.folded, self.all_in, self.acted, self.raise_locked = set(), set(), set(), set()
        self.deck = []
        self.pot = self.current_bet = self.actor_idx = 0
        self.game_msg_id = None  # 唯一权威牌桌消息（删旧发新：每次行动重发到群最新位置，全群始终只有这一条）
        self.turn_task = self.wait_task = None
        self.settled = False
        self.showdown_order = []
        self.last_compare = None
        self.penalty_log = []
        self.last_action = None          # 牌桌状态行：展示“上一手”动作，取代浮动提示消息
        self.compare_menu_owner = None   # 比牌选人菜单发起者（锁），仅其可点选对手
        self._render_lock = asyncio.Lock()  # 牌桌渲染锁：删旧发新期间防并发导致出现两条牌桌

    def add(self, uid):
        if self.phase != "waiting" or uid in self.players: return False
        if game_chips[self.chat_id][uid] < MIN_ENTRY_CHIPS: return False
        self.players.append(uid)
        return True

    def start(self):
        if len(self.players) < 2: return False
        random.shuffle(self.players)
        self.cancel_wait(); self.folded.clear(); self.all_in.clear(); self.acted.clear(); self.raise_locked.clear(); self.seen.clear()
        self.pot = self.current_bet = 0; self.settled = False
        self.deck = [Card.new(rank + suit) for rank in "23456789TJQKA" for suit in "shdc"]
        random.shuffle(self.deck)
        for uid in self.players:
            self.chips[uid] = game_chips[self.chat_id][uid]; self.initial_chips[uid] = self.chips[uid]
            self.total_bet[uid] = self.round_bets[uid] = 0
            ante = min(JINHUA_ANTE, self.chips[uid]); self.chips[uid] -= ante; self.total_bet[uid] += ante; self.pot += ante
            if not self.chips[uid]: self.all_in.add(uid)
            self.hands[uid] = [self.deck.pop(), self.deck.pop(), self.deck.pop()]
        self.phase = "betting"
        self.actor_idx = 0
        # 跳过开局即全下(ante 后 0 筹)的玩家，避免首轮无人可行动而卡死
        if self.current() is None:
            self._next()
            if self.current() is None: self.phase = "showdown"
        return True

    def _target(self, uid):
        """该玩家本轮应投入的实际金额 = 闷牌单位 × (看牌 2 倍 / 闷牌 1 倍)。"""
        return self.current_bet * (2 if uid in self.seen else 1)

    def current(self):
        if self.actor_idx >= len(self.players): return None
        uid = self.players[self.actor_idx]
        return uid if uid not in self.folded and uid not in self.all_in and uid not in self.acted else None

    def _next(self):
        n = len(self.players)
        for offset in range(1, n + 1):
            idx = (self.actor_idx + offset) % n
            uid = self.players[idx]
            if uid not in self.folded and uid not in self.all_in and uid not in self.acted:
                self.actor_idx = idx
                return uid
        return None

    def _round_done(self):
        return all(uid in self.folded or uid in self.all_in or uid in self.acted for uid in self.players)

    def _do_raise(self, uid, extra):
        try: extra = int(extra)
        except (TypeError, ValueError): return False, "无效加注额"
        if extra < JINHUA_BASE: return False, f"最低加注为 {JINHUA_BASE}"
        if uid in self.raise_locked: return False, "短全下后已行动玩家只能跟注或弃牌"
        # 先按校验后的值计算目标投入，余额不足直接拒绝，绝不先改 current_bet
        mult = 2 if uid in self.seen else 1
        new_current_bet = self.current_bet + extra
        new_target = new_current_bet * mult
        paid = new_target - self.round_bets[uid]
        if paid > self.chips[uid]:
            return False, f"积分不足：需要 {paid}，你只有 {self.chips[uid]}"
        # 校验通过后才改状态
        self.current_bet = new_current_bet
        self.chips[uid] -= paid; self.round_bets[uid] = new_target; self.total_bet[uid] += paid; self.pot += paid
        if not self.chips[uid]: self.all_in.add(uid)
        self.acted = {uid}; self.phase = "betting"
        return True, f"加注 {extra}"

    def _do_allin(self, uid):
        """炸金花全下：不足跟注或部分高出(不足一个单位加注)按 call 处理；超出足够则全下并加注、重开下注。"""
        if self.chips[uid] <= 0:
            return False, "你没有可下的筹码"
        mult = 2 if uid in self.seen else 1
        to_call = max(0, self._target(uid) - self.round_bets[uid])
        paid = self.chips[uid]
        if paid <= to_call or (paid - to_call) < mult:
            # 部分跟注：不足一个单位加注时按 call 处理（余下零星筹码保留），不重开下注
            shove = min(paid, to_call)
            self.chips[uid] -= shove
            self.round_bets[uid] += shove
            self.total_bet[uid] += shove
            self.pot += shove
            self.acted.add(uid)
            desc = f"全下 {shove}" if shove else "过牌"
        else:
            # 超出跟注足够：全下并加注，重开下注让其余玩家响应
            excess = paid - to_call
            raise_units = excess // mult
            shove = to_call + raise_units * mult
            self.chips[uid] -= shove
            self.round_bets[uid] += shove
            self.total_bet[uid] += shove
            self.pot += shove
            self.current_bet += raise_units
            prior_actors = self.acted.copy()
            if raise_units * mult < JINHUA_BASE:
                # 短全下(加注不足一个单位)：已行动者只能跟注/弃牌，不能再加注
                self.raise_locked.update(prior_actors - {uid})
            else:
                self.raise_locked.clear()
            self.acted = {uid}
            desc = f"全下 {shove}"
        if self.chips[uid] == 0:
            self.all_in.add(uid)
        return True, desc

    def action(self, uid, kind, extra=0):
        if kind == "see":
            if uid in self.seen: return False, "你已看过牌"
            self.seen.add(uid)
            return True, "看牌"
        if kind == "compare":
            if uid in self.folded: return False, "你已弃牌"
            if self.phase == "betting" and uid != self.current():
                return False, "还没轮到你"
            if self.phase not in ("betting", "open_pending"):
                return False, "当前无法比牌"
            if extra in (None, uid) or extra in self.folded or extra not in self.players:
                return False, "无效比牌对象"
            alive = [p for p in self.players if p not in self.folded]
            if len(alive) < 2:
                return False, "人数不足，无法比牌"
            # 比牌者需先跟平当前注（若尚未跟平）；看牌者需按 2 倍匹配
            to_call = max(0, self._target(uid) - self.round_bets[uid])
            if to_call > self.chips[uid]:
                return False, f"需先跟注 {to_call} 才能比牌，但积分不足"
            if to_call > 0:
                self.chips[uid] -= to_call; self.round_bets[uid] += to_call
                self.total_bet[uid] += to_call; self.pot += to_call
                if self.chips[uid] == 0: self.all_in.add(uid)
            winner = compare_jinhua_pair(uid, extra, self.hands)
            loser = extra if winner == "challenger" else uid
            penalty = 0
            # 官方规则：看牌者向闷牌者比牌落败 → 倒赔 2 倍底注
            if loser == uid and uid in self.seen and extra not in self.seen:
                penalty = min(2 * JINHUA_BASE, self.chips[uid])
                self.chips[uid] -= penalty; self.chips[extra] += penalty
                self.penalty_log.append((uid, extra, penalty))
            self.folded.add(loser)
            self.last_compare = (uid, extra, winner, penalty)
            self.acted.add(uid)
            alive = [p for p in self.players if p not in self.folded]
            if len(alive) <= 1:
                self.phase = "showdown"
            elif self._round_done():
                self.phase = "open_pending"
            else:
                self._next()
            return True, f"比牌：{'你胜' if winner == 'challenger' else '你负'}"
        if self.phase == "open_pending":
            if uid in self.folded: return False, "你已弃牌"
            if kind == "open":
                self.phase = "showdown"
                return True, "开牌"
            if kind == "raise":
                return self._do_raise(uid, extra)
            return False, "当前只能开牌或继续加注"
        if uid != self.current(): return False, "还没轮到你"
        if kind == "fold":
            self.folded.add(uid); desc = "弃牌"
        elif kind == "call":
            target = self._target(uid)
            paid = max(0, target - self.round_bets[uid])
            if paid > self.chips[uid]: return False, f"积分不足：需要 {paid}，你只有 {self.chips[uid]}"
            self.chips[uid] -= paid; self.round_bets[uid] += paid; self.total_bet[uid] += paid; self.pot += paid
            if not self.chips[uid]: self.all_in.add(uid)
            self.acted.add(uid)
            desc = f"跟注 {paid}" if paid else "过牌"
        elif kind == "raise":
            ok, desc = self._do_raise(uid, extra)
            if not ok: return False, desc
        elif kind == "allin":
            ok, desc = self._do_allin(uid)
            if not ok: return False, desc
        else: return False, "未知操作"
        alive = [p for p in self.players if p not in self.folded]
        if len(alive) <= 1:
            self.phase = "showdown"
        elif self._round_done():
            self.phase = "open_pending"
        else:
            self._next()
        return True, desc

    def _hand_name(self, uid):
        if is_235(self.hands[uid]): return "235"
        return JINHUA_HAND_NAMES.get(evaluate_jinhua(self.hands[uid])[0], "散牌")

    def jinhua_side_pot_payouts(self):
        """炸金花边池派奖：按总投入分层主池/边池，每层用 jinhua_winners 选赢家(保留 235 专杀)。"""
        payouts = defaultdict(lambda: {"amount": 0, "details": []})
        total_pot = sum(self.total_bet.values())
        for index, (amount, contributors) in enumerate(side_pots(self.total_bet)):
            alive_contributors = [u for u in contributors if u not in self.folded]
            if not alive_contributors:
                # 根因：该层贡献者已全部弃牌，原逻辑直接 skip，余额靠全局兜底掩盖分配。
                # 修正：弃牌者的投入仍属底池，归入仍存活的最佳牌型（炸金花规则）。
                alive = [u for u in self.players if u not in self.folded]
                winners = jinhua_winners({u: self.hands[u] for u in alive})
                share, remainder = divmod(amount, len(winners))
                for pos, uid in enumerate(sorted(winners)):
                    won = share + (1 if pos < remainder else 0)
                    payouts[uid]["amount"] += won
                    payouts[uid]["details"].append(("主池" if index == 0 else f"边池{index}", won))
                continue
            winners = jinhua_winners({u: self.hands[u] for u in alive_contributors})
            share, remainder = divmod(amount, len(winners))
            for pos, uid in enumerate(sorted(winners)):
                won = share + (1 if pos < remainder else 0)
                payouts[uid]["amount"] += won
                payouts[uid]["details"].append(("主池" if index == 0 else f"边池{index}", won))
        # 守恒兜底：未被分配的底池归入最佳牌型存活玩家，禁止积分凭空消失
        allocated = sum(item["amount"] for item in payouts.values())
        unallocated = total_pot - allocated
        if unallocated > 0:
            alive = [u for u in self.players if u not in self.folded]
            winners = jinhua_winners({u: self.hands[u] for u in alive})
            share, remainder = divmod(unallocated, len(winners))
            for pos, uid in enumerate(sorted(winners)):
                won = share + (1 if pos < remainder else 0)
                payouts[uid]["amount"] += won
                payouts[uid]["details"].append(("底池兜底", won))
        return payouts

    async def showdown(self):
        alive = [uid for uid in self.players if uid not in self.folded]
        self.showdown_order = alive.copy()
        if len(alive) == 1:
            winner = alive[0]
            self.chips[winner] += self.pot
            for uid in self.players:
                game_chips[self.chat_id][uid] += self.chips[uid] - self.initial_chips.get(uid, game_chips[self.chat_id][uid])
            save_data(); await asyncio.to_thread(force_save_now)
            return [(winner, "最后赢家", self.pot, [("全部底池", self.pot)], {})]
        names = {uid: self._hand_name(uid) for uid in alive}
        payouts = self.jinhua_side_pot_payouts()
        for uid, item in payouts.items():
            self.chips[uid] += item["amount"]
        for uid in self.players:
            game_chips[self.chat_id][uid] += self.chips[uid] - self.initial_chips.get(uid, game_chips[self.chat_id][uid])
        save_data(); await asyncio.to_thread(force_save_now)
        return [(uid, names[uid], payouts[uid]["amount"], payouts[uid]["details"], names) for uid in alive if payouts[uid]["amount"] > 0]

    def cancel_timer(self):
        task, self.turn_task = self.turn_task, None
        if task and task is not asyncio.current_task() and not task.done(): task.cancel()

    def cancel_wait(self):
        task, self.wait_task = self.wait_task, None
        if task and task is not asyncio.current_task() and not task.done(): task.cancel()


async def jinhua_waiting_text(game, app):
    players = [f"{i}. {await get_name(app, uid)}" for i, uid in enumerate(game.players, 1)]
    return f"🌸 新一局炸金花\n发起人：{await get_name(app, game.owner_id)}\n\n已加入：\n" + "\n".join(players) + "\n\n点击加入，发起人可立即开始。\n⏰ 满 2 人后 60 秒自动开局，不足 2 人 60 秒后自动解散。"


async def update_jinhua_waiting(game, app):
    rows = [[InlineKeyboardButton("📥 加入游戏", callback_data="jh_join")]]
    if len(game.players) >= 2: rows.append([InlineKeyboardButton("🎮 开始游戏", callback_data="jh_start")])
    rows.append([InlineKeyboardButton("❌ 终止房间", callback_data="jh_end")])
    await safe_edit(app.bot, game.chat_id, game.game_msg_id, await jinhua_waiting_text(game, app), reply_markup=InlineKeyboardMarkup(rows))


async def jinhua_table_text(game, app):
    lines = [
        f"🌸 炸金花",
        "",
        "━━━━━━━━━━━━━━━━━",
        f"💰 奖池：{game.pot}｜单注：{game.current_bet}（看牌者×2）",
    ]
    if game.last_action:
        lines.append(f"🔔 上一手：{game.last_action}")
    lines.extend([
        "━━━━━━━━━━━━━━━━━",
        "",
        "👥 玩家状态",
        "",
    ])
    current = game.current() if game.phase == "betting" else None
    if current:
        lines.append(f"⏳ 当前行动：{await get_name(app, current)}｜需补：{max(0, game._target(current) - game.round_bets[current])}")
        lines.append("")
    for index, uid in enumerate(game.players, 1):
        status = "❌ 弃牌" if uid in game.folded else "🔥 全下" if uid in game.all_in else "🟢 在局"
        seen_mark = "👁 已看牌" if uid in game.seen else "🎴 闷牌"
        lines.extend([
            f"{index}. {await get_name(app, uid)}",
            f"   {seen_mark}｜{status}｜投入 {game.total_bet[uid]}｜余筹 {game.chips[uid]}",
            "",
        ])
    return "\n".join(lines)


def jinhua_buttons(game, uid):
    rows = []
    if uid not in game.folded:
        label = "🃏 查看手牌" if uid in game.seen else "👁 看牌"
        rows.append([InlineKeyboardButton(label, callback_data="jh_see")])
    if uid != game.current() or uid in game.folded:
        return InlineKeyboardMarkup(rows)
    to_call = max(0, game._target(uid) - game.round_bets[uid])
    rows.append([InlineKeyboardButton("❌ 弃牌", callback_data="jh_fold"), InlineKeyboardButton("✅ 过牌" if not to_call else f"✅ 跟注 {to_call}", callback_data="jh_call")])
    if uid not in game.raise_locked and game.chips[uid] >= to_call + JINHUA_BASE:
        rows.append([InlineKeyboardButton(f"🔼 加注 {JINHUA_BASE}", callback_data=f"jh_raise_{JINHUA_BASE}")])
    if game.chips[uid] > 0:
        rows.append([InlineKeyboardButton(f"🔥 全下 {game.chips[uid]}", callback_data="jh_allin")])
    alive_cnt = sum(1 for p in game.players if p not in game.folded)
    if alive_cnt >= 2:
        rows.append([InlineKeyboardButton("⚔️ 比牌", callback_data="jh_compare_menu")])
    rows.append([InlineKeyboardButton("🔄 刷新界面", callback_data="jh_refresh")])
    return InlineKeyboardMarkup(rows)


async def _sync_jinhua_msg(game, app, text, kb):
    """渲染唯一权威牌桌消息：删旧发新，让牌桌永远停在群最新位置（不被聊天顶上去），全群始终只有这一条。

    流程：先发新消息（更新 game_msg_id）再删旧消息，避免牌桌短暂消失；发送失败则回退原地编辑兜底。
    加锁避免快速连续操作（连点/超时与点击并发）时出现两条牌桌。
    """
    async with game._render_lock:
        old_id = game.game_msg_id
        msg = await safe_send(app.bot, game.chat_id, text, reply_markup=kb, parse_mode="HTML")
        if msg:
            game.game_msg_id = msg.message_id
            if old_id and old_id != game.game_msg_id:
                await safe_delete(app.bot, game.chat_id, old_id)
            return
        # 发送失败兜底：原地编辑旧的（若还在），让牌桌不消失
        if old_id:
            edited = await safe_edit(app.bot, game.chat_id, old_id, text, reply_markup=kb, parse_mode="HTML")
            if edited is not None:
                return


async def update_jinhua_table(game, app):
    # 收敛为唯一牌桌消息：直接复用 show_jinhua_action（含当前操作者按钮），原地编辑不再删旧发新
    await show_jinhua_action(game, app)


async def show_jinhua_action(game, app):
    """渲染唯一权威牌桌消息（牌桌文本 + 当前操作者按钮），原地编辑 game_msg_id。

    三种视图：比牌选人菜单 / 跟平阶段全员开牌·继续加注 / 下注阶段当前玩家行动。
    """
    if game.compare_menu_owner is not None:
        owner = game.compare_menu_owner
        targets = [p for p in game.players if p not in game.folded and p != owner]
        rows = []
        for t in targets:
            tname = await get_name(app, t)
            tmark = "👁" if t in game.seen else "🎴"
            rows.append([InlineKeyboardButton(f"{tmark} {tname}", callback_data=f"jh_pk_{t}")])
        rows.append([InlineKeyboardButton("❌ 取消", callback_data="jh_cancel_pk")])
        text = f"{await jinhua_table_text(game, app)}\n\n⚔️ {await get_name(app, owner)} 选择比牌对手（仅比牌双方亮牌，其余玩家看不到牌面）："
        await _sync_jinhua_msg(game, app, text, InlineKeyboardMarkup(rows))
        return
    if game.phase == "open_pending":
        text = f"{await jinhua_table_text(game, app)}\n\n💡 已跟平，可 <b>开牌</b> 比大小，或 <b>继续加注</b> 偷鸡。"
        kb = InlineKeyboardMarkup([
            [InlineKeyboardButton("⚔️ 比牌", callback_data="jh_compare_menu"), InlineKeyboardButton("🃏 开牌比大小", callback_data="jh_open")],
            [InlineKeyboardButton(f"🔼 继续加注 {JINHUA_BASE}", callback_data=f"jh_raise_{JINHUA_BASE}")],
            [InlineKeyboardButton("🔄 刷新界面", callback_data="jh_refresh")],
        ])
        await _sync_jinhua_msg(game, app, text, kb)
        return
    uid = game.current()
    if uid is None:
        if game.phase == "showdown": await settle_jinhua(game, app)
        return
    text = f"{await jinhua_table_text(game, app)}\n\n⏰ <b>{await get_name(app, uid)}</b> 请在 {TURN_TIMEOUT} 秒内行动。"
    await _sync_jinhua_msg(game, app, text, jinhua_buttons(game, uid))


async def start_jinhua_turn_timer(game, app):
    game.cancel_timer()
    await show_jinhua_action(game, app)
    if game.phase in ("open_pending", "showdown"):
        return
    uid = game.current()

    async def timeout_action():
        await asyncio.sleep(TURN_TIMEOUT)
        if game.settled or game.phase == "showdown": return
        if game.phase == "open_pending": return
        if game.current() != uid: return
        game.action(uid, "fold")
        game.last_action = f"{await get_name(app, uid)} 超时弃牌"
        if game.phase == "showdown":
            await settle_jinhua(game, app)
        else:
            await start_jinhua_turn_timer(game, app)
    game.turn_task = asyncio.create_task(timeout_action())


async def _refresh_jinhua_table(game, app):
    """炸金花刷新界面：原地重编辑唯一牌桌消息（无副作用，仅恢复当前 phase 的视图与 timer）。

    供 on_text 的「刷新」分支与 on_button 的 jh_refresh 复用。
    """
    game.cancel_timer()
    await start_jinhua_turn_timer(game, app)
    return None


async def settle_jinhua(game, app):
    if game.settled: return
    game.settled = True; game.cancel_timer(); game.cancel_wait()
    try:
        async with user_wallet_locks([uid for uid in game.players if uid >= 0]):
            result = await game.showdown()
        if not result: raise RuntimeError("炸金花开牌未生成结算结果")
        date, hand_types = business_date(), result[0][4]
        name_ids = set(game.players) | set(game.showdown_order)
        names = {uid: await get_name(app, uid) for uid in name_ids}
        lines = ["🌸 <b>炸金花结算</b>", "━━━━━━━━━━━━━━━━━", ""]
        lines.append("亮牌：")
        for uid in game.players:
            if uid in game.folded:
                lines.extend([f"{names[uid]}：弃牌", ""])
            else:
                cards = "  ".join(card_str(c) for c in game.hands[uid])
                lines.extend([f"{names[uid]}：{cards}｜{hand_types.get(uid, '')}", ""])
        lines.append("派奖：")
        for uid, hand, amount, details, _ in sorted(result, key=lambda item: item[2], reverse=True):
            if amount > 0:
                lines.extend([f"{names[uid]}：{hand}｜+{amount}（{'，'.join(f'{pool}+{value}' for pool, value in details)}）", ""])
        lines.append("投入 / 盈亏：")
        for uid in game.players:
            net = game.chips[uid] - game.initial_chips[uid]
            if game.mode == "official":
                jinhua_profit_by_date[date][game.chat_id][uid] += net
            lines.extend([f"{names[uid]}：投入 {game.total_bet[uid]}｜盈亏 {net:+d}", ""])
        if getattr(game, "penalty_log", []):
            lines.extend(["", "比牌惩罚："])
            for payer, payee, amount in game.penalty_log:
                lines.extend([f"{names.get(payer, str(payer))} 倒赔 {amount} 给 {names.get(payee, str(payee))}", ""])
        if game.mode == "official":
            rank = sorted(jinhua_profit_by_date[date][game.chat_id].items(), key=lambda item: item[1], reverse=True)[:50]
            lines.extend(["", "🏆 <b>当日炸金花累计盈利榜</b>", "━━━━━━━━━━━━━━━━━"])
            lines.extend([f"{rank_marker(index)} {names.get(uid) or await get_name(app, uid)}：{amount:+d}" for index, (uid, amount) in enumerate(rank, 1)])
        await safe_delete(app.bot, game.chat_id, game.game_msg_id)
        delivered = await safe_send_long(app.bot, game.chat_id, "\n".join(lines), parse_mode="HTML")
        if delivered is None:
            await safe_send(app.bot, game.chat_id, "⚠️ 炸金花已完成结算，但详细结算消息发送失败。")
    except Exception:
        logger.exception("炸金花结算异常")
    finally:
        if active_jinhua_games.get(game.chat_id) is game: active_jinhua_games.pop(game.chat_id, None)
        if game.mode == "official":
            for uid in game.players: await emergency_if_needed(game.chat_id, uid, app)
        save_data(); await asyncio.to_thread(force_save_now)


async def start_jinhua_wait_timeout(game, app):
    game.cancel_wait()
    async def countdown():
        await asyncio.sleep(ROOM_WAIT_TIMEOUT)
        if game.phase != "waiting" or active_jinhua_games.get(game.chat_id) is not game:
            return
        if len(game.players) >= 2:
            if game.start():
                await update_jinhua_table(game, app)
                await start_jinhua_turn_timer(game, app)
        else:
            await refund_jinhua(game, app, "⌛ 炸金花等待 60 秒不足 2 人，房间已自动解散。")
    game.wait_task = asyncio.create_task(countdown())


async def refund_jinhua(game, app, notice):
    game.cancel_timer(); game.cancel_wait()
    game.phase = "cancelled"
    if active_jinhua_games.get(game.chat_id) is game:
        active_jinhua_games.pop(game.chat_id, None)
    await safe_delete(app.bot, game.chat_id, game.game_msg_id)
    await safe_send(app.bot, game.chat_id, notice)
    save_data()


async def cmd_jinhua(update, context):
    if not await need_auth(update): return
    if not await require_group_chat(update, "炸金花", "jinhua"): return
    cid, uid = update.effective_chat.id, update.effective_user.id
    game = active_jinhua_games.get(cid)
    room_name, _ = poker_room_of(cid, uid, exclude_game=game)
    if room_name:
        await update.message.reply_text(f"⚠️ 你已在 {room_name} 房间，请先结束再开新的扑克游戏。"); return
    mode = game.mode if game and game.phase == "waiting" else current_game_mode()
    if game_chips[cid][uid] < MIN_ENTRY_CHIPS:
        await update.message.reply_text(f"❌ 进入炸金花至少需要 {MIN_ENTRY_CHIPS} 积分。"); return
    if game:
        if game.phase != "waiting": await update.message.reply_text("当前已有进行中的炸金花。"); return
        if game.add(uid):
            await update_jinhua_waiting(game, context.application); await update.message.reply_text("已加入当前等待房间。")
        else: await update.message.reply_text("你已在等待房间中。")
        return
    game = JinhuaGame(cid, uid, mode); game.add(uid); active_jinhua_games[cid] = game
    msg = await safe_send(context.bot, cid, await jinhua_waiting_text(game, context.application), reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("📥 加入游戏", callback_data="jh_join")], [InlineKeyboardButton("❌ 终止房间", callback_data="jh_end")]]))
    if msg:
        game.game_msg_id = msg.message_id
        await start_jinhua_wait_timeout(game, context.application)


# ==================== 牛牛 PVP ====================



























async def start_wait_timeout(game, app):
    """德州等待房 60 秒倒计时：满 2 人自动开局，不足 2 人自动解散。"""
    game.cancel_wait()
    async def countdown():
        await asyncio.sleep(ROOM_WAIT_TIMEOUT)
        if game.phase != "waiting" or active_poker_games.get(game.chat_id) is not game:
            return
        if len(game.players) >= 2:
            if game.start():
                await update_poker_table(game, app)
                await start_turn_timer(game, app)
        else:
            await refund_poker(game, app, "⌛ 德州等待 60 秒不足 2 人，房间已自动解散。")
    game.wait_task = asyncio.create_task(countdown())


async def cmd_dz(update, context):
    if not await need_auth(update): return
    if not await require_group_chat(update, "德州扑克", "dz"): return
    cid, uid = update.effective_chat.id, update.effective_user.id; game = active_poker_games.get(cid)
    room_name, _ = poker_room_of(cid, uid, exclude_game=game)
    if room_name:
        await update.message.reply_text(f"⚠️ 你已在 {room_name} 房间，请先结束再开新的扑克游戏。"); return
    mode = game.mode if game and game.phase == "waiting" else current_game_mode()
    wallet = game_chips
    if wallet[cid][uid] < MIN_ENTRY_CHIPS:
        label = "积分"
        await update.message.reply_text(f"❌ 进入德州至少需要 {MIN_ENTRY_CHIPS} {label}。"); return
    if game:
        if game.season:
            await update.message.reply_text("当前有排位赛房间，请用 /排位 加入或开局。"); return
        if game.phase != "waiting": await update.message.reply_text("当前已有进行中的德州扑克。"); return
        if game.add(uid):
            await update_poker_waiting(game, context.application); await update.message.reply_text("已加入当前等待房间。")
        else: await update.message.reply_text("你已在等待房间中。")
        return
    # 注意：不再在此清空亮牌队列，保留上一局（已结束）单赢未亮牌的数据，供玩家随时补亮牌
    game = PokerGame(cid, uid, mode); game.add(uid); active_poker_games[cid] = game
    msg = await safe_send(context.bot, cid, await poker_waiting_text(game, context.application), reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("📥 加入游戏", callback_data="texas_join")], [InlineKeyboardButton("❌ 终止房间", callback_data="texas_end")]]))
    if msg:
        game.game_msg_id = msg.message_id
        await start_wait_timeout(game, context.application)

# ---------- 德州排位赛命令 ----------
async def start_season(cid, name="", forced=False):
    """开启新赛季：给所有已报名者发放起始分。返回 (ok, msg)。"""
    global season_active, season_id, season_name, season_start_ts, season_end_ts
    if season_active:
        return True, "already_active"  # 幂等：已在赛季中，不重复初始化（防自动开赛竞态双击）
    joined = season_joined.get(cid, set())
    if not forced and len(joined) < SEASON_MIN_PLAYERS:
        return False, f"需满 {SEASON_MIN_PLAYERS} 人报名才能开赛（当前 {len(joined)} 人）"
    if forced and not joined:
        return False, "尚无任何人报名，无法强制开赛"
    season_active = True
    season_id = now_bj().strftime("%Y%m%d")
    season_name = name or f"第{season_id}赛季"
    season_start_ts = int(now_bj().timestamp())
    season_end_ts = season_start_ts + SEASON_DAYS * 86400
    season_points[cid] = defaultdict(int)
    season_games[cid] = defaultdict(int)
    season_rebuy[cid] = defaultdict(int)
    for uid in joined:
        season_points[cid][uid] = SEASON_START_CHIPS
        season_games[cid][uid] = 0
        season_rebuy[cid][uid] = 0
    season_profit_by_date.pop(cid, None)
    save_data()
    return True, None


async def season_settle(app, manual=False):
    """赛季结算：按当前排位分排名（过滤未达最少局数者），推榜后重置。"""
    global season_active, season_id, season_name, season_start_ts, season_end_ts
    if not season_active:
        return
    # 提前置位：结算一旦开始立即标记赛季结束，防止并发重入（如 daily_reset 的每日重置在结算中途误触发）
    season_active = False
    # 快照（外层+内层均拷贝）：防止结算过程中并发的 showdown 修改 season_points 导致 RuntimeError
    season_snapshot = {cid: dict(users) for cid, users in season_points.items()}
    for cid, users in season_snapshot.items():
        standings = sorted(users.items(), key=lambda x: (-season_total_profit(cid, x[0]), x[0]))
        eligible = [(uid, val) for uid, val in standings if uid >= 0 and season_games[cid].get(uid, 0) >= SEASON_MIN_GAMES]
        lines = [f"🏆 第{season_id}赛季最终榜（{season_name or '排位赛'}）", "━" * 18]
        if not eligible:
            lines.append("本赛季无达标玩家，赌神称号保留在任者。")
        for i, (uid, val) in enumerate(eligible[:50], 1):
            g = season_games[cid].get(uid, 0)
            marker = "👑" if (i == 1 and uid in user_titles and TITLE_GAMBLING_GOD in user_titles[uid]) else rank_marker(i)
            lines.append(f"{marker} {await get_name(app, uid, cid=cid, with_title=False)}：总{season_total_profit(cid, uid):+d}｜{g}局")
        lines.extend(["", "⚠️ 结算时刻进行中的牌局不计入本赛季。", "🎁 奖励由管理员另行发放。"])
        await safe_send_long(app.bot, cid, "\n".join(lines))
        # 自动加冕本赛季赌神（全局唯一，覆盖上任）
        if eligible:
            champ_uid = eligible[0][0]
            champ_name = await get_name(app, champ_uid, cid=cid, with_title=False)
            streak = 1
            if champions_history and champions_history[-1]["uid"] == champ_uid:
                streak = champions_history[-1].get("streak", 1) + 1
            # 移除旧赌神称号（赌神全局唯一），保留其余称号；再给新冠军加冕
            for _u in list(user_titles.keys()):
                user_titles[_u].discard(TITLE_GAMBLING_GOD)
                if not user_titles[_u]:
                    del user_titles[_u]
            user_titles.setdefault(champ_uid, set()).add(TITLE_GAMBLING_GOD)
            champions_history.append({"season_id": season_id, "uid": champ_uid, "name": champ_name, "score": season_total_profit(cid, champ_uid), "streak": streak})
            crown = f"👑 恭喜 {await get_name(app, champ_uid, cid=cid, with_title=False)} 加冕本赛季 🎰赌神" + (f"（{streak}连冠！）" if streak > 1 else "！")
            try:
                await safe_send(app.bot, cid, crown)
            except Exception:
                pass
    # 进行中的排位牌局：本手结算不计入排名，提前告知玩家（赛季已结束后其 settle_poker 仅派奖不写回）
    for g in list(active_poker_games.values()):
        if getattr(g, "season", False) and getattr(g, "phase", "waiting") != "waiting" and g.chat_id in season_points:
            try:
                await safe_send(app.bot, g.chat_id, "⏰ 赛季已结束，本手牌结算不计入排位排名（仍正常派奖）。")
            except Exception:
                pass
    season_active = False
    season_id = None
    season_name = ""
    season_start_ts = 0
    season_end_ts = 0
    season_points.clear(); season_games.clear(); season_joined.clear(); season_rebuy.clear(); season_profit_by_date.clear()
    season_lobby_msg.clear()  # 大厅看板为 UI 态，结算后清空，下赛季重新发
    save_data()


def season_total_profit(cid, uid):
    """赛季总盈亏 = 各日已结算盈亏之和 + 当前未结算当日盈亏（当前分 - 起始分）。
    仅对已报名玩家有意义；未报名 uid 不参与当日盈亏计算，避免凭空 -起始分。"""
    total = 0
    for d in season_profit_by_date:
        total += season_profit_by_date[d].get(cid, {}).get(uid, 0)
    pts = season_points.get(cid, {}).get(uid)
    if pts is not None:
        total += pts - SEASON_START_CHIPS
    return total


async def season_standings_lines(app, cid, uid=None):
    users = season_points.get(cid, {})
    standings = sorted(users.items(), key=lambda x: (-season_total_profit(cid, x[0]), x[0]))
    remain = max(0, int((season_end_ts - now_bj().timestamp()) / 86400))
    lines = [f"🏆 第{season_id}赛季排位榜（{season_name or '排位赛'}）",
             f"⏳ 剩余约 {remain} 天｜上榜需≥{SEASON_MIN_GAMES}局", "━" * 18]
    if not standings:
        lines.append("暂无数据")
    for i, (u, val) in enumerate(standings[:50], 1):
        g = season_games[cid].get(u, 0)
        tag = "" if g >= SEASON_MIN_GAMES else f"（{g}局·未达标）"
        marker = "👑" if (i == 1 and u in user_titles and TITLE_GAMBLING_GOD in user_titles[u]) else rank_marker(i)
        lines.append(f"{marker} {await get_name(app, u, cid=cid, with_title=False)}：总{season_total_profit(cid, u):+d}｜当日{val}｜{g}局{tag}")
    # 个人排名行：请求者不在前 50 时，单独补一行真实名次，避免大群看不到自己
    if uid is not None and uid in users:
        full_rank = next((i for i, (u, _) in enumerate(standings, 1) if u == uid), None)
        if full_rank is not None and full_rank > 50:
            g = season_games[cid].get(uid, 0)
            tag = "" if g >= SEASON_MIN_GAMES else f"（{g}局·未达标）"
            lines.append(f"…（仅显示前 50，你当前第 {full_rank} 名：总{season_total_profit(cid, uid):+d}分{tag}）")
    return lines


async def season_signup(app, cid, uid):
    """报名 / 赛中补报名。处理自动开赛。返回 (ok, key)。key∈joining/started/joined_active。"""
    if season_active:
        season_joined.setdefault(cid, set()).add(uid)
        if uid not in season_points.get(cid, {}):
            season_points[cid][uid] = SEASON_START_CHIPS
            season_games[cid][uid] = 0
            season_rebuy[cid][uid] = 0
        save_data()
        return True, "joined_active"
    season_joined.setdefault(cid, set()).add(uid)
    save_data()
    n = len(season_joined[cid])
    if n >= SEASON_MIN_PLAYERS:
        ok, msg = await start_season(cid)
        # 只有真正“首次开赛”的那次才回 started；并发点按钮导致的二次进入回 joined_active
        return True, "started" if (ok and msg != "already_active") else "joined_active"
    return True, "joining"


async def season_lobby_content(app, cid):
    """返回 (text, reply_markup) 排位大厅看板，按赛季状态切换。"""
    if not season_active:
        joined = list(season_joined.get(cid, set()))
        n = len(joined)
        # 列出已报名昵称（最多 15 个，避免刷屏 + 控制 get_chat API 调用量）
        names = [await get_name(app, u) for u in joined[:15]]
        names_text = ("、".join(names) + (f" 等 {n} 人" if n > 15 else "")) if n else "（暂无）"
        text = (f"🏆 <b>排位赛报名大厅</b>\n\n"
                f"当前报名：<b>{n}/{SEASON_MIN_PLAYERS}</b> 人\n"
                f"满 {SEASON_MIN_PLAYERS} 人自动开赛，每人 {SEASON_START_CHIPS} 分，周期 {SEASON_DAYS} 天。\n"
                f"已报名：{names_text}\n"
                f"点下面按钮报名，或用 /排位报名 也能一键报名。")
        markup = InlineKeyboardMarkup([
            [InlineKeyboardButton(f"📝 报名参赛（{n}/{SEASON_MIN_PLAYERS}）", callback_data="season_signup")],
            [InlineKeyboardButton("❌ 关闭看板", callback_data="season_lobby_close")],
        ])
    else:
        remain = max(0, int((season_end_ts - now_bj().timestamp()) / 86400))
        sn = html.escape(season_name or '排位赛')  # 防止管理员自定义赛季名含 < 或 & 触发 BadRequest
        text = (f"🏆 <b>第{season_id}赛季「{sn}」进行中</b>\n\n"
                f"⏳ 剩余约 {remain} 天｜上榜需≥{SEASON_MIN_GAMES}局\n"
                f"用 /排位 开局入座；中途想加入点下面按钮。")
        markup = InlineKeyboardMarkup([
            [InlineKeyboardButton("📝 中途报名加入", callback_data="season_signup")],
            [InlineKeyboardButton("📊 看排位榜", callback_data="season_rank_btn")],
            [InlineKeyboardButton("❌ 关闭看板", callback_data="season_lobby_close")],
        ])
    return text, markup


async def render_season_lobby(app, cid):
    """编辑已有大厅看板，没有则新发。"""
    text, markup = await season_lobby_content(app, cid)
    mid = season_lobby_msg.get(cid)
    if mid:
        try:
            await safe_edit(app.bot, cid, mid, text, reply_markup=markup, parse_mode="HTML")
            return
        except Exception:
            pass
    msg = await safe_send(app.bot, cid, text, reply_markup=markup, parse_mode="HTML")
    if msg:
        season_lobby_msg[cid] = msg.message_id


async def cmd_season_join(update, context):
    if not await need_auth(update): return
    if not await require_group_chat(update, "德州排位赛", "排位"): return
    cid, uid = update.effective_chat.id, update.effective_user.id
    ok, key = await season_signup(context.application, cid, uid)
    await render_season_lobby(context.application, cid)
    if key == "started":
        await update.message.reply_text(f"🏆 报名满 {SEASON_MIN_PLAYERS} 人，第{season_id}赛季「{season_name or '排位赛'}」开始！每人 {SEASON_START_CHIPS} 分，周期 {SEASON_DAYS} 天。用 /排位 开局。")
    elif key == "joined_active":
        await update.message.reply_text(f"✅ 已加入进行中的赛季（需满 {SEASON_MIN_GAMES} 局才上榜）。当前分 {season_points[cid][uid]}。用 /排位 开局。")
    else:
        n = len(season_joined[cid])
        await update.message.reply_text(f"✅ 已报名本赛季排位赛（{n}/{SEASON_MIN_PLAYERS}）。满 {SEASON_MIN_PLAYERS} 人自动开赛；也可点群里的大厅看板报名。")


async def cmd_season_start(update, context):
    if not is_bot_admin(update.effective_user.id):
        await update.message.reply_text("❌ 仅 Bot 管理员可强制开赛"); return
    if not await require_group_chat(update, "德州排位赛", "排位"): return
    cid = update.effective_chat.id
    if season_active:
        await update.message.reply_text("⚠️ 本赛季已在进行中。"); return
    name = " ".join(context.args) if context.args else ""
    ok, msg = await start_season(cid, name, forced=True)
    if ok:
        await update.message.reply_text(f"🏆 第{season_id}赛季「{season_name or '排位赛'}」由管理员强制开启！每人 {SEASON_START_CHIPS} 分，周期 {SEASON_DAYS} 天。用 /排位 开局。")
    else:
        await update.message.reply_text(msg)


async def cmd_season_end(update, context):
    if not is_bot_admin(update.effective_user.id):
        await update.message.reply_text("❌ 仅 Bot 管理员可操作"); return
    cid = update.effective_chat.id
    if not season_active:
        await update.message.reply_text("⚠️ 当前无进行中的赛季。"); return
    await season_settle(context.application, manual=True)
    await update.message.reply_text("🏁 赛季已手动结算并重置。")


async def cmd_season_rank(update, context):
    if not await need_auth(update): return
    cid, uid = update.effective_chat.id, update.effective_user.id
    if not season_active:
        await update.message.reply_text("⚠️ 当前无进行中的赛季排位赛。"); return
    lines = await season_standings_lines(context.application, cid, uid=uid)
    await safe_send_long(context.bot, cid, "\n".join(lines))


async def cmd_god(update, context):
    """查看当前赌神与历届荣誉墙。"""
    if not await need_auth(update): return
    app = context.application
    cid = update.effective_chat.id
    lines = ["👑 <b>🎰赌神 荣誉殿堂</b>", "━" * 16]
    champ_uid = next((u for u, ts in user_titles.items() if TITLE_GAMBLING_GOD in ts), None)
    if champ_uid is None:
        lines.append("当前暂无 🎰赌神。拿下排位赛冠军即可加冕！")
    else:
        lines.append(f"🏅 现任赌神：{await get_name(app, champ_uid, cid=cid, with_title=False)}")
    if champions_history:
        lines.append("")
        lines.append("📜 <b>历届荣誉墙</b>")
        for rec in champions_history[-12:][::-1]:
            streak = rec.get("streak", 1)
            sfx = f" · {streak}连冠" if streak > 1 else ""
            name = html.escape(str(rec.get("name", "?")))
            lines.append(f"第{rec['season_id']}赛季：{name}（{rec.get('score', 0)}分）{sfx}")
    else:
        lines.append("")
        lines.append("📜 历届荣誉墙：暂无记录")
    text = "\n".join(lines)
    try:
        await safe_send_long(context.bot, update.effective_chat.id, text, parse_mode="HTML")
    except Exception:
        # 历史称号含 < & 等特殊字符导致 HTML 渲染失败时，降级为纯文本发送，避免命令“失效无响应”
        await safe_send_long(context.bot, update.effective_chat.id, text)


async def cmd_god_grant(update, context):
    """管理员封赌神（全局唯一，覆盖上任）。"""
    if not is_bot_admin(update.effective_user.id):
        await update.message.reply_text("❌ 仅 Bot 管理员可操作"); return
    if not context.args:
        await update.message.reply_text("用法：/封赌神 <用户ID>"); return
    try:
        uid = int(context.args[0])
    except ValueError:
        await update.message.reply_text("❌ 用户 ID 必须是数字。"); return
    for _u in list(user_titles.keys()):
        user_titles[_u].discard(TITLE_GAMBLING_GOD)
        if not user_titles[_u]:
            del user_titles[_u]
    user_titles.setdefault(uid, set()).add(TITLE_GAMBLING_GOD)
    save_data()
    await update.message.reply_text(f"👑 已将 {uid} 封为 🎰赌神（覆盖上任）。")


async def cmd_god_revoke(update, context):
    """管理员撤赌神。"""
    if not is_bot_admin(update.effective_user.id):
        await update.message.reply_text("❌ 仅 Bot 管理员可操作"); return
    if not context.args:
        await update.message.reply_text("用法：/撤赌神 <用户ID>"); return
    try:
        uid = int(context.args[0])
    except ValueError:
        await update.message.reply_text("❌ 用户 ID 必须是数字。"); return
    if uid in user_titles and TITLE_GAMBLING_GOD in user_titles[uid]:
        user_titles[uid].discard(TITLE_GAMBLING_GOD)
        if title_equipped.get(uid) == TITLE_GAMBLING_GOD:
            title_equipped.pop(uid, None)
        if not user_titles[uid]:
            del user_titles[uid]
        save_data()
        await update.message.reply_text(f"🔻 已撤销 {uid} 的 🎰赌神 称号。")
    else:
        await update.message.reply_text("ℹ️ 该用户当前没有 🎰赌神 称号。")


async def cmd_shop(update, context):
    """积分商店：列出可兑换的称号。"""
    if not await need_auth(update): return
    if not is_group_chat(update):
        await update.message.reply_text("🏪 积分商店请在群聊中使用（发 /商店）。"); return
    lines = ["🏪 <b>积分商店 · 称号兑换</b>", "━" * 16]
    for t, cfg in SHOP_TITLES.items():
        cur = "积分"
        dur = "永久" if cfg["duration"] is None else f"{cfg['duration'] // 86400}天"
        lines.append(f"• {title_icon(t)}<b>{html.escape(t)}</b>：{cfg['price']} {cur}｜{dur}")
    lines.append("")
    lines.append("💡 用 /兑换 称号名 购买；/我的称号 查看，/佩戴 切换亮出的称号。")
    await safe_send_long(context.bot, update.effective_chat.id, "\n".join(lines), parse_mode="HTML")


async def cmd_redeem(update, context):
    """兑换称号：扣统一积分 + 挂称号（永久或限时）。"""
    if not await need_auth(update): return
    if not is_group_chat(update):
        await update.message.reply_text("🏪 积分商店请在群聊中使用（发 /商店）。"); return
    if not context.args:
        await update.message.reply_text("用法：/兑换 称号名（用 /商店 查看可兑换称号）"); return
    # 容错：用户经常顺手多打「购买/一个/来一个」之类，按空格 join 后找不到。
    # 优先取第一个参数（称号意图词），join 作为兜底（SHOP_TITLES 实际全无空格）。
    title = context.args[0].strip()
    cfg = SHOP_TITLES.get(title) or SHOP_TITLES.get("".join(context.args).strip())
    if not cfg:
        await update.message.reply_text("❌ 该称号不存在，用 /商店 查看可兑换称号。"); return
    uid = update.effective_user.id
    cid = update.effective_chat.id
    # 已持有且未过期则拒绝重复兑换
    held = user_titles.get(uid, set())
    if title in held:
        exp = title_expiry.get(uid, {}).get(title)
        if exp is None or exp > int(now_bj().timestamp()):
            await update.message.reply_text("ℹ️ 你已持有该称号，无需重复兑换。"); return
    if player_is_busy(cid, uid):
        await update.message.reply_text("⚠️ 你正在游戏中，请先结束当前游戏再兑换。"); return
    wallet = game_chips
    cur = "积分"
    async with wallet_locks[uid]:
        if wallet[cid][uid] < cfg["price"]:
            await update.message.reply_text(f"❌ 你的{cur}不足：需要 {cfg['price']}，当前 {wallet[cid][uid]}。"); return
        wallet[cid][uid] -= cfg["price"]
        user_titles.setdefault(uid, set()).add(title)
        if cfg["duration"] is not None:
            title_expiry.setdefault(uid, {})[title] = int(now_bj().timestamp()) + cfg["duration"]
        else:
            title_expiry.setdefault(uid, {}).pop(title, None)
        save_data()
    dur = "永久" if cfg["duration"] is None else f"{cfg['duration'] // 86400}天"
    await update.message.reply_text(f"🎉 兑换成功！获得称号 {title_icon(title)}<b>{html.escape(title)}</b>（{dur}），花费 {cfg['price']} {cur}，剩余 {wallet[cid][uid]}。", parse_mode="HTML")


async def cmd_my_titles(update, context):
    """查看我持有的所有称号。"""
    if not await need_auth(update): return
    uid = update.effective_user.id
    ts = user_titles.get(uid, set())
    if not ts:
        await update.message.reply_text("你还没有任何称号，用 /商店 查看可兑换称号。")
        return
    lines = ["🎖 <b>我的称号</b>", "━" * 16]
    equipped = title_equipped.get(uid)
    now = int(now_bj().timestamp())
    for t in sorted(ts, key=lambda x: (-SHOP_TITLES.get(x, {}).get("price", 0), x)):
        mark = " 👈佩戴中" if t == equipped else ""
        if t == TITLE_GAMBLING_GOD:
            lines.append(f"👑 {html.escape(t)}（赛季冠军专属）{mark}")
        else:
            cfg = SHOP_TITLES.get(t, {})
            if cfg.get("duration") is not None:
                exp = title_expiry.get(uid, {}).get(t, 0)
                if exp <= now:
                    lines.append(f"• {title_icon(t)}{html.escape(t)}（已过期，待清理）{mark}")
                else:
                    remain = max(1, (exp - now + 86399) // 86400)
                    lines.append(f"• {title_icon(t)}{html.escape(t)}（剩余约 {remain} 天）{mark}")
            else:
                lines.append(f"• {title_icon(t)}{html.escape(t)}（永久）{mark}")
    lines.append("")
    lines.append("💡 用 /佩戴 称号名 切换亮出的称号；不佩戴则默认显示最贵的。")
    await safe_send_long(context.bot, update.effective_chat.id, "\n".join(lines), parse_mode="HTML")


async def cmd_equip(update, context):
    """佩戴某个已持有的称号（切换昵称前缀，可覆盖默认）。"""
    if not await need_auth(update): return
    if not context.args:
        await update.message.reply_text("用法：/佩戴 称号名（用 /我的称号 查看你持有的称号）")
        return
    title = "".join(context.args)
    uid = update.effective_user.id
    ts = user_titles.get(uid, set())
    if title not in ts:
        await update.message.reply_text("❌ 你尚未持有该称号，用 /我的称号 查看。")
        return
    title_equipped[uid] = title
    save_data()
    await update.message.reply_text(f"✅ 已佩戴 <b>{html.escape(title)}</b>，将显示在昵称前。", parse_mode="HTML")


async def cmd_season_points(update, context):
    """管理员加减排位分（正为加，负为减）。"""
    if not is_bot_admin(update.effective_user.id):
        await update.message.reply_text("❌ 仅 Bot 管理员可操作"); return
    if not await need_auth(update): return
    try:
        uid, amount = await _parse_target_amount(update, context)
        if amount == 0: raise ValueError
    except (ValueError, IndexError):
        await update.message.reply_text("用法：/赛季分 用户ID 数量（正加负减），或回复玩家消息后使用 /赛季分 数量"); return
    cid = update.effective_chat.id
    if not season_active and uid not in season_points.get(cid, {}):
        await update.message.reply_text("⚠️ 该玩家不在当前赛季，且赛季未激活。"); return
    if amount < 0 and season_points.get(cid, {}).get(uid, 0) < -amount:
        await update.message.reply_text("❌ 该玩家排位分不足。"); return
    season_points.setdefault(cid, defaultdict(int))[uid] += amount
    season_joined.setdefault(cid, set()).add(uid)
    save_data()
    verb = "增加" if amount > 0 else "扣除"
    await update.message.reply_text(f"✅ 已为 {await get_name(context.application, uid)} {verb} {abs(amount)} 排位分，当前 {season_points[cid][uid]}。")


async def cmd_season_help(update, context):
    if not await need_auth(update): return
    cid = update.effective_chat.id
    text = (
        "🏆 <b>德州排位赛使用说明</b>\n\n"
        "<b>报名 / 开局</b>\n"
        "• /排位 — 一键报名（静默）并可在开赛后开/入牌桌；未报名会自动补报\n"
        "• /排位报名 — 报名并弹出群里「报名大厅」看板（满 20 自动开赛）\n"
        "• 大厅看板按钮：📝 报名参赛 / 📝 中途报名加入\n\n"
        "<b>查询</b>\n"
        "• /排位榜 — 看当前排名（榜尾显示你的名次）\n"
        "• /赌神 — 查看 🎰赌神 称号与历届荣誉墙\n"
        "• 大厅看板按钮：📊 看排位榜\n\n"
        "<b>管理员专属</b>\n"
        "• /排位开赛 [赛季名] — 强制开赛（可自定义名，如 /排位开赛 赌神大战秋季赛）\n"
        "• /排位结束 — 提前结算并推最终榜\n\n"
        "<b>自动机制</b>\n"
        "• 每日 23:50 自动推一次排位榜\n"
        "• 开赛后第 7 天（到点后的首个午夜）自动结算，可能晚最多约 24 小时\n\n"
        "📌 满 20 人开赛；起始 20000 分；输光可应急补分 3×2000；满 5 局才上榜；次日 0 点重置为 20000 分可继续打。\n"
        "💡 以上「排位」命令均可换「赛季」前缀，含义完全相同，如 /赛季榜 /赛季报名 /赛季开赛 /赛季结束。\n"
        "⚠️ 群里若中文命令无反应，多为 BotFather 隐私模式拦截，发 /setprivacy → Disable 即可。"
    )
    await safe_send_long(context.bot, cid, text, parse_mode="HTML")


async def cmd_season_play(update, context):
    if not await need_auth(update): return
    if not await require_group_chat(update, "德州排位赛", "排位"): return
    cid, uid = update.effective_chat.id, update.effective_user.id
    if not season_active:
        ok, key = await season_signup(context.application, cid, uid)
        if key == "started":
            await render_season_lobby(context.application, cid)  # 满 20 自动开赛：翻转看板为进行中，继续往下开房
        else:
            # UX2：/排位 静默报名不弹看板（看板仅在 /排位报名 或按钮点击时出现，减少刷屏）
            n = len(season_joined[cid])
            await update.message.reply_text(f"✅ 已报名本赛季排位赛（{n}/{SEASON_MIN_PLAYERS}）。满 {SEASON_MIN_PLAYERS} 人自动开赛；发 /排位报名 可看报名大厅。")
            return
    # 赛季进行中：开 / 入房间（赛中未报名者自动补报名）
    if uid not in season_joined.get(cid, set()):
        season_joined.setdefault(cid, set()).add(uid)
        if uid not in season_points.get(cid, {}):
            season_points[cid][uid] = SEASON_START_CHIPS
            season_games[cid][uid] = 0
            season_rebuy[cid][uid] = 0
        save_data()
    if season_points[cid][uid] <= 0:
        await update.message.reply_text("❌ 你的排位分已用完，等待应急补分或下局。"); return
    game = active_poker_games.get(cid)
    if game:
        if game.season:
            if game.phase != "waiting": await update.message.reply_text("当前已有进行中的排位赛。"); return
            if game.add(uid):
                await update_poker_waiting(game, context.application); await update.message.reply_text("已加入当前等待房间。")
            else: await update.message.reply_text("你已在等待房间中。")
            return
        else:
            await update.message.reply_text("当前有日常德州房间，请先 /结束 后再开排位赛。"); return
    game = PokerGame(cid, uid, current_game_mode(), season=True); game.add(uid); active_poker_games[cid] = game
    msg = await safe_send(context.bot, cid, await poker_waiting_text(game, context.application), reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("📥 加入游戏", callback_data="texas_join")], [InlineKeyboardButton("❌ 终止房间", callback_data="texas_end")]]))
    if msg:
        game.game_msg_id = msg.message_id
        await start_wait_timeout(game, context.application)

async def cmd_sm(update, context):
    if not await need_auth(update): return
    if not await require_group_chat(update, "赛车", "sc"): return
    cid = update.effective_chat.id
    if cid in active_horse_races:
        race = active_horse_races[cid]
        # 已有赛车：直接把当前带按钮的看板重发出来，让后发的人也能立刻看到/参与，而不是只回一句文字
        if getattr(race, "phase", "") == "betting":
            msg = await safe_send(context.bot, cid, await race.view(context.application), reply_markup=race.buttons())
            if msg: race.game_msg_id = msg.message_id
        else:
            await update.message.reply_text("当前已有赛车进行中。")
        return
    mode = current_game_mode()
    jackpot = race_jackpot.get(cid, 0) if mode == "official" else 0
    race = HorseRace(cid, update.effective_user.id, jackpot, mode); active_horse_races[cid] = race
    msg = await safe_send(context.bot, cid, await race.view(context.application), reply_markup=race.buttons())
    if msg: race.game_msg_id = msg.message_id
    race.task = asyncio.create_task(race.run(context.application)); save_data()

async def refund_poker(game, app, notice):
    """终止未结算牌局时退款。

    德州下注只在局对象 self.chips 中暂扣，wallet 在牌局期间不会被扣减
    （仅在开局快照 + 管理员 /adddz 加分时变动），因此直接保留 wallet 现状即可
    正确退还，同时不丢失牌局进行中管理员的加分。
    """
    game.cancel_timer(); game.cancel_auto(); game.cancel_wait()
    game.phase = "cancelled"
    if active_poker_games.get(game.chat_id) is game:
        active_poker_games.pop(game.chat_id, None)
    await safe_delete(app.bot, game.chat_id, game.action_msg_id)
    await safe_edit(app.bot, game.chat_id, game.game_msg_id, notice, reply_markup=None)
    save_data()


async def cmd_end(update, context):
    if not await need_auth(update): return
    cid, uid = update.effective_chat.id, update.effective_user.id
    arg = context.args[0].lower() if context.args else ""
    
    poker = active_poker_games.get(cid)
    race = active_horse_races.get(cid)
    bj = active_blackjack_games.get(cid)
    jinhua = active_jinhua_games.get(cid)

    if not any([poker, race, bj, jinhua]):
        await update.message.reply_text("当前没有进行中的游戏。"); return

    notices = []
    # 如果带了参数，只针对性关闭
    target_all = (arg == "")
    

    if poker and (target_all or arg in ["dz", "dzpk", "texas", "德州"]):
        if is_bot_admin(uid) or uid in poker.players:
            await refund_poker(poker, context.application, "🛑 德州扑克已终止，积分已退回。")
            notices.append("德州已退款")

    if jinhua and (target_all or arg in ["jinhua", "zjh", "炸金花", "金花"]):
        if is_bot_admin(uid) or uid in jinhua.players:
            await refund_jinhua(jinhua, context.application, "🛑 炸金花已终止，积分已退回。")
            notices.append("炸金花已退款")

    if race and (target_all or arg in ["sc", "sm", "race", "赛车"]):
        if is_bot_admin(uid) or uid in race.bets:
            if race.phase == "betting":
                if race.task and not race.task.done(): race.task.cancel()
                await race.refund(context.application, "🛑 赛车已终止，积分已退回。")
                notices.append("赛车已退款")
            else: notices.append("赛车进行中无法终止")

    if bj and (target_all or arg in ["21", "bj", "21点"]):
        if is_bot_admin(uid) or uid in bj.players:
            bj.cancel_timer(); bj.cancel_wait()
            wallet = game_chips
            for p_uid, b in bj.bets.items():
                wallet[cid][p_uid] += b
                pending_game_bets[cid].get(p_uid, {}).pop("21", None)
            active_blackjack_games.pop(cid, None)
            await safe_edit(context.bot, cid, bj.game_msg_id, "🛑 21点已终止，积分已退回。", reply_markup=None)
            notices.append("21点已退款")

    if not notices:
        await update.message.reply_text("❌ 权限不足或未找到匹配的游戏指令。用法示例：/end dz")
    else:
        save_data()
        await update.message.reply_text("；".join(notices))
def player_is_busy(cid, uid):
    poker = active_poker_games.get(cid)
    if poker and poker.phase != "waiting" and uid in poker.players:
        return True
    race = active_horse_races.get(cid)
    if race and race.phase in {"betting", "racing", "settling"} and uid in race.bets:
        return True
    bj = active_blackjack_games.get(cid)
    if bj and bj.phase != "waiting" and uid in bj.players:
        return True
    jinhua = active_jinhua_games.get(cid)
    if jinhua and jinhua.phase != "waiting" and uid in jinhua.players:
        return True
    return False


def poker_room_of(cid, uid, exclude_game=None):
    """玩家所在的扑克游戏房间（德州/炸金花，含等待房）。exclude_game 用于排除当前房间。
    返回 (游戏名, 游戏对象)，不在任何房间则返回 (None, None)。"""
    for name, g in (("德州", active_poker_games.get(cid)),
                    ("炸金花", active_jinhua_games.get(cid))):
        if g and g is not exclude_game and uid in g.players:
            return name, g
    return None, None


async def _parse_target_amount(update, context):
    if len(context.args) >= 2:
        return int(context.args[0]), int(context.args[1])
    if len(context.args) == 1 and update.message.reply_to_message:
        return update.message.reply_to_message.from_user.id, int(context.args[0])
    raise ValueError


async def cmd_add(update, context):
    if not is_bot_admin(update.effective_user.id):
        await update.message.reply_text("❌ 仅 Bot 管理员可操作"); return
    if not ADMIN_ADJUST_ENABLED:
        await update.message.reply_text("❌ 管理员加减分功能已关闭（网页「积分系统 → 积分设置」可开启）。"); return
    if not await need_auth(update): return
    try:
        uid, amount = await _parse_target_amount(update, context)
        if amount == 0: raise ValueError
    except (ValueError, IndexError):
        await update.message.reply_text("用法：/add 用户ID 数量（正为加，负为减），或回复玩家消息后使用 /add 数量"); return
    cid = update.effective_chat.id
    if player_is_busy(cid, uid):
        await update.message.reply_text("该玩家正在游戏中，无法修改积分。"); return
    async with wallet_locks[uid]:
        if amount < 0 and game_chips[cid][uid] < -amount:
            await update.message.reply_text("❌ 玩家积分不足。"); return
        game_chips[cid][uid] += amount; save_data()
    verb = "添加" if amount > 0 else "扣除"
    msg = _fmt_tpl("add_msg_tpl", target=await get_name(context.application, uid),
                   verb=verb, amount=abs(amount), balance=game_chips[cid][uid])
    await update.message.reply_text(msg)



async def cmd_cx(update, context):
    if not await need_auth(update): return
    cid = update.effective_chat.id
    date = business_date()
    texas = poker_profit_by_date[date].get(cid, {})
    combined = {}
    for g in (blackjack_profit_by_date, race_profit_by_date, jinhua_profit_by_date):
        for uid, v in total_profit_by_game(g, cid).items():
            combined[uid] = combined.get(uid, 0) + v
    if not texas and not combined:
        await update.message.reply_text("当前业务日暂无盈亏记录。"); return
    lines = ["🃏 德州当日盈亏", "━"*14]
    if texas:
        for i, (uid, value) in enumerate(sorted(texas.items(), key=lambda x:x[1], reverse=True)[:50], 1):
            lines.append(f"{rank_marker(i)} {await get_name(context.application, uid, cid=cid)}：{value:+d}")
    else:
        lines.append("暂无记录")
    lines.extend(["", "🎮 其他游戏累计盈亏", "━"*14])
    if combined:
        for i, (uid, value) in enumerate(sorted(combined.items(), key=lambda x:x[1], reverse=True)[:50], 1):
            lines.append(f"{rank_marker(i)} {await get_name(context.application, uid, cid=cid)}：{value:+d}")
    else:
        lines.append("暂无记录")
    await safe_send_long(context.bot, cid, "\n".join(lines))

async def cmd_ph(update, context):
    if not await need_auth(update): return
    cid = update.effective_chat.id
    lines = ["💰 积分榜", "━"*14]
    for i, (uid, value) in enumerate(sorted(game_chips[cid].items(), key=lambda x:x[1], reverse=True)[:50], 1):
        lines.append(f"{rank_marker(i)} {await get_name(context.application, uid, cid=cid)}：{value}")
    # 累计盈利榜（含老虎机），方便随时核对战绩，不再只能从抽奖结果里看滞后的榜单
    combined = {}
    for g in (blackjack_profit_by_date, race_profit_by_date, jinhua_profit_by_date):
        for u, v in total_profit_by_game(g, cid).items():
            combined[u] = combined.get(u, 0) + v
    if combined:
        lines.extend(["", "🏆 累计盈利榜（总数）", "━"*14])
        for i, (u, v) in enumerate(sorted(combined.items(), key=lambda x:x[1], reverse=True)[:50], 1):
            lines.append(f"{rank_marker(i)} {await get_name(context.application, u, cid=cid)}：{v:+d}")
    await safe_send_long(context.bot, cid, "\n".join(lines))

async def cmd_sq(update, context):
    if not is_bot_admin(update.effective_user.id):
        await update.message.reply_text("❌ 仅 Bot 管理员可操作"); return
    if not is_group_chat(update):
        await update.message.reply_text("⚠️ 授权需在群聊中进行：请在目标群里发送 /授权，机器人会把该群加入授权名单。私聊里授权无意义，且会导致游戏开在私聊、别人看不到。")
        return
    cid = update.effective_chat.id
    AUTHORIZED_GROUPS.add(cid); save_data()
    await update.message.reply_text(f"✅ 当前群已授权：{cid}")

async def cmd_qxshouquan(update, context):
    if not is_bot_admin(update.effective_user.id): return
    try: cid = int(context.args[0])
    except (IndexError, ValueError): await update.message.reply_text("用法：取消授权 群ID（或 /qxsh 群ID）"); return
    AUTHORIZED_GROUPS.discard(cid); save_data(); await update.message.reply_text(f"✅ 已取消授权 {cid}")

async def cmd_auth_list(update, context):
    """管理员查看所有已授权群组（列出群 ID，尽量附带群名）。"""
    if not is_bot_admin(update.effective_user.id):
        await update.message.reply_text("❌ 仅 Bot 管理员可操作"); return
    if not AUTHORIZED_GROUPS:
        await update.message.reply_text("📋 当前没有任何已授权群组。"); return
    lines = ["📋 <b>已授权群组列表</b>", f"共 {len(AUTHORIZED_GROUPS)} 个：", "━"*14]
    for cid in sorted(AUTHORIZED_GROUPS):
        title = chat_name_cache.get(cid)
        if not title:
            try:
                chat = await context.bot.get_chat(cid)
                if getattr(chat, "title", None):
                    title = chat.title
                    chat_name_cache[cid] = title
            except Exception as e:
                logger.warning("授权列表取群名失败 cid=%s: %s", cid, e)
        lines.append(f"• {title}（{cid}）" if title else f"• {cid}（群名未知，bot 可能已不在该群）")
    await safe_send_long(context.bot, update.effective_chat.id, "\n".join(lines))

async def cmd_ban(update, context):
    """管理员拉黑玩家（禁止使用机器人）。支持 /拉黑 用户ID 或 回复玩家消息 /拉黑"""
    if not is_bot_admin(update.effective_user.id):
        await update.message.reply_text("❌ 仅 Bot 管理员可操作"); return
    target = None
    replied = update.message.reply_to_message
    if replied:
        target = replied.from_user.id
        # 顺带缓存被回复者的真名，黑名单列表不再显示"玩家{ID}"
        ru = replied.from_user
        if not ru.is_bot:
            nm = ru.full_name or (f"@{ru.username}" if ru.username else None)
            if nm: user_names[target] = nm
    else:
        try: target = int(context.args[0])
        except (IndexError, ValueError): pass
    if not target:
        await update.message.reply_text("用法：/拉黑 用户ID，或回复玩家消息后使用 /拉黑"); return
    if is_bot_admin(target):
        await update.message.reply_text("⚠️ 不能拉黑管理员。"); return
    if target in BLACKLISTED_USERS:
        await update.message.reply_text("ℹ️ 该用户已在黑名单中。"); return
    # 用 ID 拉黑且尚无缓存名字时，主动 get_chat 取名缓存（失败则回退"玩家{ID}"）
    if target not in user_names:
        try:
            chat = await context.bot.get_chat(target)
            nm = getattr(chat, "first_name", None) or getattr(chat, "title", None) or (f"@{chat.username}" if getattr(chat, "username", None) else None)
            if nm: user_names[target] = nm
        except Exception:
            pass
    BLACKLISTED_USERS.add(target); save_data()
    await update.message.reply_text(f"🚫 已拉黑 {await get_name(context.application, target)}（{target}），该用户已被禁止使用机器人。")

async def cmd_unban(update, context):
    """管理员解封玩家。"""
    if not is_bot_admin(update.effective_user.id):
        await update.message.reply_text("❌ 仅 Bot 管理员可操作"); return
    target = None
    if update.message.reply_to_message:
        target = update.message.reply_to_message.from_user.id
    else:
        try: target = int(context.args[0])
        except (IndexError, ValueError): pass
    if not target:
        await update.message.reply_text("用法：/解黑 用户ID，或回复玩家消息后使用 /解黑"); return
    if target not in BLACKLISTED_USERS:
        await update.message.reply_text("ℹ️ 该用户不在黑名单中。"); return
    BLACKLISTED_USERS.discard(target); save_data()
    await update.message.reply_text(f"✅ 已解封 {await get_name(context.application, target)}（{target}）。")

async def cmd_banlist(update, context):
    """管理员查看黑名单。"""
    if not is_bot_admin(update.effective_user.id):
        await update.message.reply_text("❌ 仅 Bot 管理员可操作"); return
    if not BLACKLISTED_USERS:
        await update.message.reply_text("📋 当前黑名单为空。"); return
    lines = [f"📋 <b>黑名单（共 {len(BLACKLISTED_USERS)} 人）</b>", "━"*14]
    for uid in sorted(BLACKLISTED_USERS):
        lines.append(f"• {await get_name(context.application, uid)}（{uid}）")
    await safe_send_long(context.bot, update.effective_chat.id, "\n".join(lines), parse_mode="HTML")

async def cmd_list_all(update, context):
    """管理员一键查看：管理员 / 授权群 / 黑名单 三合一总览。"""
    if not is_bot_admin(update.effective_user.id):
        await update.message.reply_text("❌ 仅 Bot 管理员可操作"); return
    app = context.application
    lines = ["📋 <b>管理总览</b>", "━"*18]

    # 管理员
    seeds = set(ADMIN_USER_IDS)
    dynamic = BOT_ADMINS - seeds
    lines.append(f"👑 <b>管理员（{len(BOT_ADMINS)}）</b>")
    for uid in sorted(seeds):
        lines.append(f"  🔒 {await get_name(app, uid)}（{uid}）")
    for uid in sorted(dynamic):
        lines.append(f"  ➕ {await get_name(app, uid)}（{uid}）")
    if not dynamic:
        lines.append("  （无动态管理员）")
    lines.append("")

    # 授权群
    lines.append(f"✅ <b>已授权群（{len(AUTHORIZED_GROUPS)}）</b>")
    if not AUTHORIZED_GROUPS:
        lines.append("  （无）")
    else:
        for cid in sorted(AUTHORIZED_GROUPS):
            title = chat_name_cache.get(cid)
            if not title:
                try:
                    chat = await context.bot.get_chat(cid)
                    if getattr(chat, "title", None):
                        title = chat.title; chat_name_cache[cid] = title
                except Exception as e:
                    logger.warning("取群名失败 %s: %s", cid, e)
            lines.append(f"  • {title}（{cid}）" if title else f"  • {cid}（群名未知）")
    lines.append("")

    # 黑名单
    lines.append(f"🚫 <b>黑名单（{len(BLACKLISTED_USERS)}）</b>")
    if not BLACKLISTED_USERS:
        lines.append("  （无）")
    else:
        for uid in sorted(BLACKLISTED_USERS):
            lines.append(f"  • {await get_name(app, uid)}（{uid}）")

    await safe_send_long(context.bot, update.effective_chat.id, "\n".join(lines), parse_mode="HTML")

async def cmd_addadmin(update, context):
    if not is_bot_admin(update.effective_user.id):
        await update.message.reply_text("❌ 仅 Bot 管理员可操作"); return
    try: uid = int(context.args[0])
    except (IndexError, ValueError):
        await update.message.reply_text("用法：/addadmin 用户ID，例如 /addadmin 123456789"); return
    if uid in BOT_ADMINS:
        await update.message.reply_text(f"ℹ️ {uid} 已经是管理员了"); return
    BOT_ADMINS.add(uid); save_data()
    await update.message.reply_text(f"✅ 已添加机器人管理员：{uid}")

async def cmd_deladmin(update, context):
    if not is_bot_admin(update.effective_user.id):
        await update.message.reply_text("❌ 仅 Bot 管理员可操作"); return
    try: uid = int(context.args[0])
    except (IndexError, ValueError):
        await update.message.reply_text("用法：/deladmin 用户ID，例如 /deladmin 123456789"); return
    if uid in ADMIN_USER_IDS:
        await update.message.reply_text(f"⚠️ {uid} 是种子管理员，重启后自动恢复，无法移除（如需移除请改代码 ADMIN_USER_IDS）"); return
    if uid not in BOT_ADMINS:
        await update.message.reply_text(f"ℹ️ {uid} 不是管理员"); return
    BOT_ADMINS.discard(uid); save_data()
    await update.message.reply_text(f"✅ 已移除机器人管理员：{uid}")

async def cmd_admin_list(update, context):
    if not is_bot_admin(update.effective_user.id):
        await update.message.reply_text("❌ 仅 Bot 管理员可操作"); return
    seeds = set(ADMIN_USER_IDS)
    dynamic = BOT_ADMINS - seeds
    lines = ["👑 <b>当前机器人管理员</b>",
             f"共 <b>{len(BOT_ADMINS)}</b> 人（种子 {len(seeds)} + 动态 {len(dynamic)}）", ""]
    lines.append("🔒 种子管理员（重启保留，不可被 /deladmin 移除）：")
    for uid in sorted(seeds):
        lines.append(f"  • {await get_name(context.application, uid)}（{uid}）")
    lines.append("")
    if dynamic:
        lines.append("➕ 动态添加（可被 /deladmin 移除）：")
        for uid in sorted(dynamic):
            lines.append(f"  • {await get_name(context.application, uid)}（{uid}）")
    else:
        lines.append("（暂无动态添加的管理员）")
    await safe_send_long(context.bot, update.effective_chat.id, "\n".join(lines), parse_mode="HTML")

async def cmd_autosm(update, context):
    if not await need_auth(update): return
    if not is_bot_admin(update.effective_user.id): await update.message.reply_text("❌ 仅 Bot 管理员可操作"); return
    cid = update.effective_chat.id; hourly_race_enabled[cid] = not hourly_race_enabled[cid]; save_data()
    await update.message.reply_text(f"整点自动赛车：{'✅ 已开启' if hourly_race_enabled[cid] else '❌ 已关闭'}")

async def on_button(update, context):
    try:
        q = update.callback_query
        if not q or not q.message:
            if q: await q.answer("该操作已过期", show_alert=True)
            return
        cid, uid, data = q.message.chat.id, q.from_user.id, q.data or ""
        _remember_name(update)
        if not is_auth(cid): await q.answer("未授权", show_alert=True); return
        if uid in BLACKLISTED_USERS and not is_bot_admin(uid): await q.answer("🚫 你已被禁止使用本机器人", show_alert=True); return
        
        # --- 21点 回调 ---
        if data.startswith("bj_"):
            game = active_blackjack_games.get(cid)
            if not game: await q.answer("游戏已结束", show_alert=True); return
            if data.startswith("bj_join_"):
                bet = int(data.split("_")[2])
                wallet = game_chips
                async with wallet_locks[uid]:
                    if wallet[cid][uid] < bet: await q.answer("积分不足", show_alert=True); return
                    if game.add_player(uid, bet):
                        wallet[cid][uid] -= bet
                    else:
                        await q.answer("你已在局中或无法加入", show_alert=True); return
                await q.answer("已加入"); await update_blackjack_ui(game, context.application)
            elif data == "bj_start":
                if uid != game.owner_id: await q.answer("仅发起人可开始", show_alert=True); return
                if game.start(): 
                    game.cancel_wait() # 开始后取消等待计时
                    await update_blackjack_ui(game, context.application); await start_bj_turn_timer(game, context.application)
                else: await q.answer("人数不足", show_alert=True)
            elif data.startswith("bj_hit_"):
                if uid not in game.players:
                    await q.answer("❌ 你未参与本局游戏。", show_alert=True); return
                if str(uid) != data.split("_")[2]: await q.answer("不是你的回合", show_alert=True); return
                card = game.hit(uid); await q.answer(f"你抽到了 {game.get_card_str([card])}")
                if game.phase == "finished" or game.phase == "dealer_turn": await update_blackjack_ui(game, context.application)
                else: await update_blackjack_ui(game, context.application); await start_bj_turn_timer(game, context.application)
            elif data.startswith("bj_stand_"):
                if uid not in game.players:
                    await q.answer("❌ 你未参与本局游戏。", show_alert=True); return
                if str(uid) != data.split("_")[2]: await q.answer("不是你的回合", show_alert=True); return
                # 额外校验：必须当前确为该玩家回合，防止旧按钮双击跳过下一位玩家
                if game.players[game.current_player_idx] != uid: await q.answer("不是你的回合", show_alert=True); return
                game.next_player(); await q.answer("停牌")
                if game.phase == "finished" or game.phase == "dealer_turn": await update_blackjack_ui(game, context.application)
                else: await update_blackjack_ui(game, context.application); await start_bj_turn_timer(game, context.application)
            elif data.startswith("bj_double_"):
                if uid not in game.players:
                    await q.answer("❌ 你未参与本局游戏。", show_alert=True); return
                if str(uid) != data.split("_")[2]: await q.answer("不是你的回合", show_alert=True); return
                wallet = game_chips

                # 用户级锁包裹检查余额→扣款，防止并发超扣
                async with wallet_locks[uid]:
                    if wallet[cid][uid] < game.bets[uid]: await q.answer("积分不足，无法双倍", show_alert=True); return
                    # 原子化：先让 game 校验回合并翻倍（内部翻倍 bets + 更新退款保护），
                    # 仅成功才扣钱；避免超时/重复点击导致静默丢分
                    prev_bet = game.bets[uid]
                    if not game.double_down(uid):
                        await q.answer("操作失败：已不是你的回合", show_alert=True); return
                    wallet[cid][uid] -= prev_bet
                await q.answer("双倍下注！摸牌并停牌")
                await action_notice(cid, context.application, uid, "选择了双倍下注！")
                
                if game.phase == "finished" or game.phase == "dealer_turn": await update_blackjack_ui(game, context.application)
                else: await update_blackjack_ui(game, context.application); await start_bj_turn_timer(game, context.application)
            elif data == "bj_end":
                if not is_bot_admin(uid) and uid != game.owner_id: await q.answer("权限不足", show_alert=True); return
                game.cancel_timer(); game.cancel_wait()
                # 退还本局下注
                wallet = game_chips
                for p_uid, bet in game.bets.items():
                    wallet[cid][p_uid] += bet
                    pending_game_bets[cid].get(p_uid, {}).pop("21", None)
                active_blackjack_games.pop(cid, None)
                await safe_edit(context.bot, cid, game.game_msg_id, "🛑 21点已手动终止，积分已退回。", reply_markup=None)
            return

        if data.startswith("season_"):
            if data == "season_signup":
                ok, key = await season_signup(context.application, cid, uid)
                await render_season_lobby(context.application, cid)
                if key == "started":
                    await q.answer("🏆 报名已满，赛季自动开始！用 /排位 开局", show_alert=True)
                elif key == "joined_active":
                    await q.answer("✅ 已加入进行中的赛季")
                else:
                    await q.answer("✅ 已报名")
                return
            if data == "season_lobby_close":
                mid = season_lobby_msg.pop(cid, None)
                if mid: await safe_delete(context.bot, cid, mid)
                await q.answer("已关闭看板"); return
            if data == "season_rank_btn":
                if not season_active:
                    await q.answer("当前无进行中的赛季", show_alert=True); return
                lines = await season_standings_lines(context.application, cid, uid=uid)
                await safe_send_long(context.bot, cid, "\n".join(lines))
                await q.answer("已发送排位榜"); return
            await q.answer("未知操作", show_alert=True); return
        if data.startswith("texas_"):
            game = active_poker_games.get(cid)
            if data == "texas_reveal":
                await handle_texas_reveal(cid, uid, q, context); return
            if not game: await q.answer("德州游戏已结束", show_alert=True); return
            if data == "texas_hand":
                hand = game.hands.get(uid); await q.answer(f"你的手牌：{card_str(hand[0])}  {card_str(hand[1])}" if hand and uid not in game.folded else "当前无法查看手牌", show_alert=True); return
            if data == "texas_end":
                if not is_bot_admin(uid) and uid not in game.players:
                    await q.answer("权限不足", show_alert=True); return
                await refund_poker(game, context.application, "🛑 德州已终止，积分已退回。")
                await q.answer("本局已终止")
                return
            if game.phase == "waiting":
                if data == "texas_join":
                    room_name, _ = poker_room_of(cid, uid, exclude_game=game)
                    if room_name:
                        await q.answer(f"你已在 {room_name} 房间，请先结束再加入", show_alert=True); return
                    if game.season:
                        if uid not in season_joined.get(cid, set()):
                            season_joined.setdefault(cid, set()).add(uid)
                            if uid not in season_points.get(cid, {}):
                                season_points[cid][uid] = SEASON_START_CHIPS
                                season_games[cid][uid] = 0
                                season_rebuy[cid][uid] = 0
                            save_data()
                        if season_points[cid][uid] <= 0:
                            await q.answer("排位分不足，无法加入", show_alert=True); return
                    else:
                        wallet = game_chips
                        if wallet[cid][uid] < MIN_ENTRY_CHIPS:
                            await q.answer(f"进入德州至少需要 {MIN_ENTRY_CHIPS} 积分", show_alert=True); return
                    if game.add(uid):
                        await q.answer("已加入"); await update_poker_waiting(game, context.application)
                    else: await q.answer("你已在等待房间中。", show_alert=True)
                elif data == "texas_start" and uid == game.owner_id and game.start():
                    game.cancel_wait()
                    await q.answer("游戏开始"); await update_poker_table(game, context.application); await start_turn_timer(game, context.application)
                else: await q.answer("无法执行此操作", show_alert=True)
                return
            if uid != game.current(): await q.answer("还没轮到你", show_alert=True); return
            action = {"texas_fold":"fold", "texas_check":"check", "texas_call":"call", "texas_allin":"allin"}.get(data); extra = 0
            if data == "texas_raise_half": action, extra = "raise", max(FIXED_MIN_RAISE, game.pot // 2)
            elif data == "texas_raise_pot": action, extra = "raise", max(FIXED_MIN_RAISE, game.pot)
            elif data.startswith("texas_raise_"):
                try: action, extra = "raise", int(data.rsplit("_", 1)[1])
                except ValueError: await q.answer("无效加注额", show_alert=True); return
            if not action: await q.answer("未知操作", show_alert=True); return
            ok, desc = game.action(uid, action, extra)
            if not ok: await q.answer(desc, show_alert=True); return
            await q.answer(desc); await safe_delete(context.bot, cid, game.action_msg_id); await action_notice(cid, context.application, uid, desc)
            if game.phase == "showdown": await settle_poker(game, context.application)
            else: await update_poker_table(game, context.application); await start_turn_timer(game, context.application)
            return
        if data.startswith("jh_"):
            game = active_jinhua_games.get(cid)
            if not game: await q.answer("炸金花游戏已结束", show_alert=True); return
            if data == "jh_refresh":
                await _refresh_jinhua_table(game, context.application)
                await q.answer("已刷新界面")
                return
            if data == "jh_see":
                if uid not in game.hands or uid in game.folded:
                    await q.answer("当前无法看牌", show_alert=True); return
                first = uid not in game.seen
                if first:
                    game.seen.add(uid)  # 首次看牌：标记 seen，之后下注翻倍
                cards = "  ".join(card_str(c) for c in game.hands[uid])
                await q.answer(f"你的手牌：{cards}｜{game._hand_name(uid)}", show_alert=True)
                if first:
                    # 看牌是公开信息（闷牌→已看牌），写入状态行并原地重编辑同一牌桌消息
                    game.last_action = f"{await get_name(context.application, uid)} 看了牌"
                    await show_jinhua_action(game, context.application)
                return
            if data == "jh_compare_menu":
                if uid in game.folded:
                    await q.answer("你已弃牌", show_alert=True); return
                if game.phase == "betting" and uid != game.current():
                    await q.answer("还没轮到你", show_alert=True); return
                if game.phase not in ("betting", "open_pending"):
                    await q.answer("当前无法比牌", show_alert=True); return
                targets = [p for p in game.players if p not in game.folded and p != uid]
                if not targets:
                    await q.answer("没有可比对的对象", show_alert=True); return
                game.cancel_timer()  # 选人期间暂停超时，避免被自动弃牌
                game.compare_menu_owner = uid  # 锁：仅发起者能点选对手
                await show_jinhua_action(game, context.application)  # 同一条消息切换为选人菜单
                await q.answer("选择比牌对手"); return
            if data == "jh_cancel_pk":
                game.compare_menu_owner = None
                if game.phase == "open_pending":
                    await show_jinhua_action(game, context.application)
                else:
                    await start_jinhua_turn_timer(game, context.application)
                await q.answer("已取消比牌"); return
            if data.startswith("jh_pk_"):
                if game.compare_menu_owner is None or uid != game.compare_menu_owner:
                    await q.answer("不是你发起的比牌", show_alert=True); return
                try: target = int(data.rsplit("_", 1)[1])
                except ValueError:
                    await q.answer("无效比牌对象", show_alert=True); return
                game.compare_menu_owner = None
                ok, desc = game.action(uid, "compare", target)
                if not ok:
                    await q.answer(desc, show_alert=True)
                    await start_jinhua_turn_timer(game, context.application)
                    return
                cmp = game.last_compare
                challenger, target, winner, penalty = cmp
                cname = await get_name(context.application, challenger)
                tname = await get_name(context.application, target)
                challenger_win = (winner == "challenger")
                lname = tname if challenger_win else cname
                ann = f"⚔️ {cname} 比牌 {tname}：{cname if challenger_win else tname} 胜，{lname} 出局"
                if penalty:
                    ann += f"（看牌者向闷牌者比牌落败，倒赔 {penalty}）"
                await safe_send(context.bot, cid, ann)
                # 仅比牌双方私聊亮牌，旁观者看不到牌面
                ccards = "  ".join(card_str(c) for c in game.hands[challenger])
                tcards = "  ".join(card_str(c) for c in game.hands[target])
                pm = (f"⚔️ 比牌结果\n你：{ccards}（{game._hand_name(challenger)}）\n"
                      f"对方：{tcards}（{game._hand_name(target)}）\n"
                      f"结果：{'你胜' if challenger_win else '你负'}")
                await safe_send(context.bot, challenger, pm)
                await safe_send(context.bot, target, pm)
                await q.answer(desc)
                if game.phase == "showdown":
                    await settle_jinhua(game, context.application)
                else:
                    await start_jinhua_turn_timer(game, context.application)
                return
            if data == "jh_end":
                if not is_bot_admin(uid) and uid not in game.players:
                    await q.answer("权限不足", show_alert=True); return
                await refund_jinhua(game, context.application, "🛑 炸金花已终止，积分已退回。")
                await q.answer("本局已终止")
                return
            if game.phase == "waiting":
                if data == "jh_join":
                    room_name, _ = poker_room_of(cid, uid, exclude_game=game)
                    if room_name:
                        await q.answer(f"你已在 {room_name} 房间，请先结束再加入", show_alert=True); return
                    if game_chips[cid][uid] < MIN_ENTRY_CHIPS:
                        await q.answer(f"进入炸金花至少需要 {MIN_ENTRY_CHIPS} 积分", show_alert=True); return
                    if game.add(uid):
                        await q.answer("已加入"); await update_jinhua_waiting(game, context.application)
                    else: await q.answer("你已在等待房间中。", show_alert=True)
                elif data == "jh_start" and uid == game.owner_id and game.start():
                    game.cancel_wait()
                    await q.answer("游戏开始"); await update_jinhua_table(game, context.application); await start_jinhua_turn_timer(game, context.application)
                else: await q.answer("无法执行此操作", show_alert=True)
                return
            # 跟平阶段：开牌 / 继续加注（所有存活玩家可操作）
            if game.phase == "open_pending":
                if uid in game.folded:
                    await q.answer("你已弃牌", show_alert=True); return
                if data == "jh_open":
                    ok, desc = game.action(uid, "open")
                    await q.answer(desc); await settle_jinhua(game, context.application)
                elif data.startswith("jh_raise_"):
                    try: extra = int(data.rsplit("_", 1)[1])
                    except ValueError: await q.answer("无效加注额", show_alert=True); return
                    ok, desc = game.action(uid, "raise", extra)
                    if not ok: await q.answer(desc, show_alert=True); return
                    await q.answer(desc)
                    game.last_action = f"{await get_name(context.application, uid)} {desc}"
                    await show_jinhua_action(game, context.application)
                else:
                    await q.answer("未知操作", show_alert=True)
                return
            # 下注阶段：当前玩家操作
            if uid != game.current(): await q.answer("还没轮到你", show_alert=True); return
            action = {"jh_fold": "fold", "jh_call": "call", "jh_allin": "allin"}.get(data); extra = 0
            if data.startswith("jh_raise_"):
                try: action, extra = "raise", int(data.rsplit("_", 1)[1])
                except ValueError: await q.answer("无效加注额", show_alert=True); return
            if not action: await q.answer("未知操作", show_alert=True); return
            ok, desc = game.action(uid, action, extra)
            if not ok: await q.answer(desc, show_alert=True); return
            await q.answer(desc)
            game.last_action = f"{await get_name(context.application, uid)} {desc}"
            if game.phase == "showdown": await settle_jinhua(game, context.application)
            elif game.phase == "open_pending": await show_jinhua_action(game, context.application)
            else: await start_jinhua_turn_timer(game, context.application)
            return
        if data.startswith("rp_grab_"):
            p = rp_packets.get(data[8:])
            if not p:
                await q.answer("红包已结束或过期", show_alert=True); return
            await _rp_grab(p, data[8:], uid, context, q)
            return
        if data.startswith("auc_bid_"):
            try: auc_cid = int(data[8:])
            except ValueError:
                await q.answer("无效数据", show_alert=True); return
            await _auction_bid(auc_cid, uid, context, q)
            return
        if data.startswith("buyok_") or data.startswith("buyno_"):
            if not is_bot_admin(uid):
                await q.answer("仅 Bot 管理员可操作", show_alert=True); return
            await _buy_settle(context, data[6:], data.startswith("buyok_"), q)
            return
        if data.startswith("horsebet_"):
            race = active_horse_races.get(cid)
            try: _, horse, amount = data.split("_"); horse, amount = int(horse), int(amount)
            except ValueError: await q.answer("无效下注数据", show_alert=True); return
            if not race: await q.answer("赛车已结束", show_alert=True); return
            ok, desc = await race.bet(uid, horse, amount)
            if not ok: await q.answer(desc, show_alert=True); return
            race.name_cache[uid] = await get_name(context.application, uid); await q.answer(desc); await action_notice(cid, context.application, uid, f"下注 {amount} 于 {HORSE_EMOJI[horse]}")
            await safe_edit(context.bot, cid, race.game_msg_id, await race.view(context.application), reply_markup=race.buttons())
            return

    except Exception:
        logger.exception("按钮处理异常")


async def on_text(update, context):
    # 外层 try 包命令分发；开头校验单独内层 try（消息结构异常属噪音，静默忽略）
    try:
        # 开头校验：无效消息静默跳过，不打扰用户
        try:
            message, user = update.effective_message, update.effective_user
            if not message or not message.text or not user or user.is_bot: return
            if message.date and (datetime.now(timezone.utc) - message.date).total_seconds() > STALE_TEXT_COMMAND_SECONDS:
                return
            cid, text = update.effective_chat.id, message.text.strip()
            _remember_name(update)
        except Exception:
            return

        # 拉黑拦截：被封禁用户（非管理员）禁止使用全部功能，连帮助都看不到
        if update.effective_user.id in BLACKLISTED_USERS and not is_bot_admin(update.effective_user.id):
            await message.reply_text("🚫 你已被禁止使用本机器人，如有疑问请联系管理员。"); return

        # 不带 / 的命令直达：若首词是已知命令别名，按命令处理（全部命令均可不带 / 触发）
        _words = text.split()
        if _words and _words[0] in CMD_ALIASES:
            await _dispatch_alias(_words[0], _words[1:], update, context)
            return
        
        # 深度防御：非命令的游戏交互（下注/落子/加注）仅在授权群内处理，
        # 与 on_button 对齐；命令分发仍在上面由各自 cmd_* 自行校验权限
        if not is_auth(cid):
            return

        # 聊天积分：静默计分，不影响下方游戏文本处理
        try:
            _award_chat_points(cid, user.id, text)
        except Exception:
            logger.exception("聊天积分记账异常（已吞并）")
        # 成员档案：发言即记录（首次见/最后见/消息数）
        try:
            prof = member_profiles[cid][user.id]
            if not prof:
                prof.update({"name": user_names.get(user.id, f"用户{user.id}"), "first": now_bj().strftime("%Y-%m-%d %H:%M"), "msgs": 0})
            prof["last"] = now_bj().strftime("%Y-%m-%d %H:%M")
            prof["msgs"] = prof.get("msgs", 0) + 1
        except Exception:
            logger.exception("成员档案记录异常（已吞并）")
        
        # 统一刷新逻辑
        if text in ["棋盘", "刷新", "看棋", "board", "qp"]:
            found = False
            # 1. 21点
            bj = active_blackjack_games.get(cid)
            if bj: found = True; await update_blackjack_ui(bj, context.application)
            # 3. 德州
            poker = active_poker_games.get(cid)
            if poker:
                found = True
                await safe_delete(context.bot, cid, poker.game_msg_id)
                if poker.phase == "waiting":
                    msg = await safe_send(context.bot, cid, await poker_waiting_text(poker, context.application), reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("📥 加入游戏", callback_data="texas_join")], [InlineKeyboardButton("❌ 终止房间", callback_data="texas_end")]]))
                    if msg: poker.game_msg_id = msg.message_id
                else:
                    msg = await safe_send(context.bot, cid, await poker_table_text(poker, context.application))
                    if msg:
                        poker.game_msg_id = msg.message_id
                        # 恢复当前行动玩家的操作按钮，防止刷新后游戏卡死
                        await start_turn_timer(poker, context.application)
            # 3.5 炸金花：刷新发新界面（仿德州，避免长消息越拉越长）
            jh = active_jinhua_games.get(cid)
            if jh and jh.phase != "waiting":
                found = True
                await _refresh_jinhua_table(jh, context.application)
            # 4. 赛车
            race = active_horse_races.get(cid)
            if race and race.phase == "betting":
                found = True
                await safe_delete(context.bot, cid, race.game_msg_id)
                msg = await safe_send(context.bot, cid, await race.view(context.application), reply_markup=race.buttons())
                if msg: race.game_msg_id = msg.message_id
            if not found: await message.reply_text("💡 当前没有任何正在进行的游戏。")
            return

        # 21点文字加入
        blackjack = active_blackjack_games.get(cid)
        bj_match = re.fullmatch(r"(?:下注|下|押|买)?(?:21点|21)\s*(\d+)", text)
        if bj_match and blackjack:
            if blackjack.phase != "waiting":
                await message.reply_text("❌ 21点已经开始，请等待下一局。"); return
            amount = int(bj_match.group(1))
            if amount < BJ_MIN_BET:
                await message.reply_text(f"❌ 21点最低下注 {BJ_MIN_BET} 积分。"); return
            wallet = game_chips
            async with wallet_locks[user.id]:
                if wallet[cid][user.id] < amount:
                    await message.reply_text(f"❌ 积分不足，你只有 {wallet[cid][user.id]}。"); return
                if blackjack.add_player(user.id, amount):
                    wallet[cid][user.id] -= amount
                else:
                    await message.reply_text("❌ 你已在局中或无法加入。"); return
            await action_notice(cid, context.application, user.id, f"加入了 21点，下注 {amount}")
            await update_blackjack_ui(blackjack, context.application)
            return

        # 赛车与德州传统匹配
        match = re.fullmatch(r"下注\s+(\d+)\s+(\d+)", text); race = active_horse_races.get(cid)
        if match and race:
            horse, amount = int(match.group(1))-1, int(match.group(2))
            ok, desc = await race.bet(user.id, horse, amount)
            if not ok: await message.reply_text(f"❌ {desc}"); return
            race.name_cache[user.id] = await get_name(context.application, user.id)
            await action_notice(cid, context.application, user.id, f"下注 {amount} 于 {HORSE_EMOJI[horse]}")
            await safe_edit(context.bot, cid, race.game_msg_id, await race.view(context.application), reply_markup=race.buttons())
            return


        # 扑克类游戏文字加注（自动路由到玩家当前轮到的游戏：德州→炸金花）
        bet_match = re.fullmatch(r"(?:继续)?(?:下注|加注)\s*[:：]?\s*(\d+)\s*(?:积分)?", text)
        if bet_match:
            amount = int(bet_match.group(1))
            for game, settle, update, start_timer in [
                (active_poker_games.get(cid), settle_poker, update_poker_table, start_turn_timer),
                (active_jinhua_games.get(cid), settle_jinhua, update_jinhua_table, start_jinhua_turn_timer),
            ]:
                if not game:
                    continue
                # 炸金花跟平阶段(open_pending)：所有存活玩家(未弃)均可加注，此时 current() 返回 None
                if game is active_jinhua_games.get(cid) and game.phase == "open_pending":
                    if user.id not in game.players or user.id in game.folded:
                        continue
                elif not (game.phase != "waiting" and user.id == game.current()):
                    continue
                ok, desc = game.action(user.id, "raise", amount)
                if not ok: await message.reply_text(f"❌ {desc}"); return
                await action_notice(cid, context.application, user.id, desc)
                if game.phase == "showdown": await settle(game, context.application)
                else: await update(game, context.application); await start_timer(game, context.application)
                return

        # 扑克类游戏文字全下（自动路由到玩家当前轮到的游戏：德州→炸金花）
        if re.fullmatch(r"全下|all\s*in", text.strip(), re.IGNORECASE):
            for game, settle, update, start_timer in [
                (active_poker_games.get(cid), settle_poker, update_poker_table, start_turn_timer),
                (active_jinhua_games.get(cid), settle_jinhua, update_jinhua_table, start_jinhua_turn_timer),
            ]:
                if not (game and game.phase != "waiting" and user.id == game.current()):
                    continue
                ok, desc = game.action(user.id, "allin")
                if not ok: await message.reply_text(f"❌ {desc}"); return
                await action_notice(cid, context.application, user.id, desc)
                if game.phase == "showdown": await settle(game, context.application)
                else: await update(game, context.application); await start_timer(game, context.application)
                return
    except Exception:
        logger.exception("文本指令处理异常")
        # 命令分发异常不再静默：给用户明确反馈，便于排查而非毫无反应
        try:
            await message.reply_text("⚠️ 指令处理出错，请联系管理员。")
        except Exception:
            pass


# ---------- 积分系统（统一钱包） ----------
def _get_level(balance):
    """按积分等级表返回当前等级名，表为空返回空串。"""
    lv = ""
    for item in POINT_LEVELS:
        if balance >= item["value"]:
            lv = item["name"]
    return lv

def _award_chat_points(cid, uid, text):
    """聊天积分：静默计分，满 N 字符记 X 分，受每日上限约束（零头不计）。"""
    if not CHAT_ENABLED or CHAT_REWARD <= 0 or CHAT_CHARS_PER <= 0:
        return
    n = len(text.strip())
    if n < CHAT_CHARS_PER:
        return
    gain = (n // CHAT_CHARS_PER) * CHAT_REWARD
    if gain <= 0:
        return
    date = now_bj().strftime("%Y-%m-%d")
    today = chat_today[date][cid]
    earned = today.get(uid, 0)
    if CHAT_DAILY_CAP > 0:
        gain = min(gain, CHAT_DAILY_CAP - earned)
        if gain <= 0:
            return
    today[uid] = earned + gain
    game_chips[cid][uid] += gain

async def cmd_sign(update, context):
    if not await need_auth(update): return
    if not SIGN_ENABLED:
        await update.message.reply_text("ℹ️ 签到功能未开启。"); return
    if not is_group_chat(update):
        await update.message.reply_text("⚠️ 签到请在群聊中进行。"); return
    cid, uid = update.effective_chat.id, update.effective_user.id
    today = now_bj().strftime("%Y-%m-%d")
    yesterday = (now_bj() - timedelta(days=1)).strftime("%Y-%m-%d")
    info = sign_data[cid][uid]
    if info.get("last") == today:
        await update.message.reply_text(f"✅ 今天已经签过啦（连续 {info.get('streak', 0)} 天）。"); return
    streak = info.get("streak", 0) + 1 if info.get("last") == yesterday else 1
    reward = SIGN_BASE_REWARD + (SIGN_STREAK_BONUS if streak % 7 == 0 else 0)
    async with wallet_locks[uid]:
        game_chips[cid][uid] += reward
        sign_data[cid][uid] = {"last": today, "streak": streak}
        save_data()
    bonus = "（含连续7天额外奖励）" if streak % 7 == 0 else ""
    msg = _fmt_tpl("sign_msg_tpl", name=await get_name(context.application, uid),
                   streak=streak, reward=reward, bonus=bonus, balance=game_chips[cid][uid])
    await update.message.reply_text(msg)

async def cmd_sign_rank(update, context):
    if not await need_auth(update): return
    cid = update.effective_chat.id
    users = [(uid, v.get("streak", 0)) for uid, v in sign_data.get(cid, {}).items() if v.get("streak", 0) > 0]
    if not users:
        await update.message.reply_text("本群还没有签到记录，发「签到」抢头名！"); return
    lines = ["📅 连续签到排行", "━" * 14]
    for i, (uid, s) in enumerate(sorted(users, key=lambda x: (-x[1], x[0]))[:20], 1):
        lines.append(f"{rank_marker(i)} {await get_name(context.application, uid, cid=cid)}：连续 {s} 天")
    await safe_send_long(context.bot, cid, "\n".join(lines))

async def cmd_my_points(update, context):
    if not await need_auth(update): return
    cid, uid = update.effective_chat.id, update.effective_user.id
    balance = game_chips[cid][uid]
    date = now_bj().strftime("%Y-%m-%d")
    today_chat = chat_today.get(date, {}).get(cid, {}).get(uid, 0)
    streak = sign_data.get(cid, {}).get(uid, {}).get("streak", 0)
    signed = "✅ 已签" if sign_data.get(cid, {}).get(uid, {}).get("last") == date else "❌ 未签"
    lv = _get_level(balance)
    lv_line = f"🎖 等级：{lv}\n" if lv else ""
    msg = _fmt_tpl("query_msg_tpl", name=await get_name(context.application, uid),
                   balance=balance, level_line=lv_line, signed=signed, streak=streak, today_chat=today_chat)
    await update.message.reply_text(msg)
    if POINTS_DELETE_SECONDS > 0 and is_group_chat(update):
        async def _del():
            await asyncio.sleep(POINTS_DELETE_SECONDS)
            await safe_delete(context.bot, cid, update.message.message_id)
        asyncio.create_task(_del())

async def cmd_points_rank(update, context):
    if not await need_auth(update): return
    cid = update.effective_chat.id
    lines = ["💰 积分排行榜", "━" * 14]
    for i, (uid, value) in enumerate(sorted(game_chips[cid].items(), key=lambda x: x[1], reverse=True)[:20], 1):
        lv = _get_level(value)
        tag = f"｜{lv}" if lv else ""
        lines.append(f"{rank_marker(i)} {await get_name(context.application, uid, cid=cid)}：{value}{tag}")
    await safe_send_long(context.bot, cid, "\n".join(lines))

async def cmd_mall(update, context):
    if not await need_auth(update): return
    if not MALL_ITEMS:
        await update.message.reply_text("🛒 商城暂无商品，管理员可在后台「积分系统 → 商城商品表」上架。"); return
    lines = ["🛒 积分商城", "━" * 14]
    for i, item in enumerate(MALL_ITEMS, 1):
        lines.append(f"{i}. {item['name']}　—　{item['value']} 积分")
    lines.append("")
    lines.append("💡 发「购买 编号」（如：购买 1）即可用积分兑换，管理员会尽快发货。")
    await safe_send_long(context.bot, update.effective_chat.id, "\n".join(lines))

async def cmd_mall_buy(update, context):
    if not await need_auth(update): return
    if not is_group_chat(update):
        await update.message.reply_text("⚠️ 购买请在群聊中进行。"); return
    if not MALL_ITEMS:
        await update.message.reply_text("🛒 商城暂无商品。"); return
    if not context.args:
        await update.message.reply_text(f"用法：购买 编号（1~{len(MALL_ITEMS)}），用「积分商城」查看列表。"); return
    arg = context.args[0].strip()
    item = None
    if arg.isdigit() and 1 <= int(arg) <= len(MALL_ITEMS):
        item = MALL_ITEMS[int(arg) - 1]
    else:
        name = arg.lstrip("0123456789.、 ").strip()
        item = next((x for x in MALL_ITEMS if x["name"] == name), None)
    if not item:
        await update.message.reply_text("❌ 没有这个商品，用「积分商城」查看列表。"); return
    cid, uid = update.effective_chat.id, update.effective_user.id
    price = item["value"]
    async with wallet_locks[uid]:
        if game_chips[cid][uid] < price:
            await update.message.reply_text(f"❌ 积分不足：需要 {price}，当前 {game_chips[cid][uid]}。"); return
        game_chips[cid][uid] -= price
        mall_orders.append({"ts": now_bj().strftime("%Y-%m-%d %H:%M"), "cid": cid, "uid": uid,
                            "name": await get_name(context.application, uid), "item": item["name"], "price": price})
        save_data()
    await update.message.reply_text(
        f"🛍 购买成功：{item['name']}（-{price} 积分）\n💰 余额 {game_chips[cid][uid]}\n管理员会尽快处理发货。")
    try:
        await context.bot.send_message(ADMIN_USER_ID,
            f"🛒 积分商城订单\n群：{chat_name_cache.get(cid, cid)}\n"
            f"玩家：{await get_name(context.application, uid)}（{uid}）\n商品：{item['name']}（{price} 积分）")
    except Exception:
        logger.exception("商城订单通知管理员失败")

async def cmd_redpacket(update, context):
    if not await need_auth(update): return
    if not REDPACKET_ENABLED:
        await update.message.reply_text("ℹ️ 红包功能未开启。"); return
    if not is_group_chat(update):
        await update.message.reply_text("⚠️ 红包请在群聊中发。"); return
    args = context.args
    if len(args) < 2 or not args[0].isdigit() or not args[1].isdigit():
        await update.message.reply_text("用法：红包 总积分 份数（如：红包 1000 5）"); return
    total, count = int(args[0]), int(args[1])
    if not (1 <= total <= 1000000 and 1 <= count <= 100 and count <= total):
        await update.message.reply_text("❌ 总积分 1~100 万，份数 1~100 且不超过总积分。"); return
    cid, uid = update.effective_chat.id, update.effective_user.id
    async with wallet_locks[uid]:
        if game_chips[cid][uid] < total:
            await update.message.reply_text(f"❌ 积分不足：需要 {total}，当前 {game_chips[cid][uid]}。"); return
        game_chips[cid][uid] -= total
        pid = secrets.token_urlsafe(8)
        rp_packets[pid] = {"cid": cid, "from": uid, "left_amt": total, "left_n": count,
                           "grabbed": {}, "ts": now_bj().timestamp(), "msg_id": None}
        save_data()
    await action_notice(cid, context.application, uid, f"发出了 {total} 积分 / {count} 份红包")
    msg = await safe_send(context.bot, cid,
        f"🧧 {await get_name(context.application, uid)} 的积分红包\n💰 {total} 积分 × {count} 份\n点击下方按钮抢！",
        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🧧 抢红包", callback_data=f"rp_grab_{pid}")]]))
    if msg:
        rp_packets[pid]["msg_id"] = msg.message_id

async def _rp_grab(p, pid, uid, context, q):
    """红包抢夺核心：检查过期/重复 → 随机拆分 → 入账 → 更新看板。"""
    cid = p["cid"]
    now = now_bj().timestamp()
    if now - p["ts"] > 86400:  # 过期：剩余整体退回发包人
        refund = p["left_amt"]
        async with wallet_locks[p["from"]]:
            game_chips[cid][p["from"]] += refund
        rp_packets.pop(pid, None); save_data()
        await q.answer("红包已过期，剩余已退回", show_alert=True)
        await safe_edit(context.bot, cid, p["msg_id"], "🧧 红包已过期，未领完的积分已退回。", reply_markup=None)
        return
    if uid in p["grabbed"]:
        await q.answer(f"你已经抢过 {p['grabbed'][uid]} 积分啦", show_alert=True); return
    if p["left_n"] <= 0:
        await q.answer("手慢了，红包已被抢完", show_alert=True); return
    if p["left_n"] == 1:
        amt = p["left_amt"]
    else:
        amt = random.randint(1, max(1, p["left_amt"] - p["left_n"] + 1))
    async with wallet_locks[uid]:
        p["grabbed"][uid] = amt
        p["left_amt"] -= amt; p["left_n"] -= 1
        game_chips[cid][uid] += amt
        save_data()
    await q.answer(f"🧧 抢到 {amt} 积分！")
    total, count = sum(p["grabbed"].values()), len(p["grabbed"])
    if p["left_n"] <= 0:
        detail_lines = []
        for u, a in p["grabbed"].items():
            detail_lines.append(f"{await get_name(context.application, u, cid=cid)}：{a}")
        detail = "\n".join(detail_lines)
        await safe_edit(context.bot, cid, p["msg_id"],
                        f"🧧 红包已被抢完（{count} 份 / {total} 积分）\n{detail}", reply_markup=None)
    else:
        await safe_edit(context.bot, cid, p["msg_id"],
                        f"🧧 红包进行中\n💰 已领 {count}/{p['left_n'] + count} 份｜剩 {p['left_amt']} 积分",
                        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🧧 抢红包", callback_data=f"rp_grab_{pid}")]]))


# ---------- 积分转赠 / 积分拍卖 / 购买积分（统一钱包） ----------
async def cmd_inherit(update, context):
    """积分转赠（继承）：把积分转给同群其他成员，可收手续费。"""
    if not await need_auth(update): return
    if not is_group_chat(update):
        await update.message.reply_text("⚠️ 转赠请在群聊中使用。"); return
    if not INHERIT_ENABLED:
        await update.message.reply_text("❌ 转赠功能未开启（网页「积分系统 → 积分继承」可开启）。"); return
    cid, uid = update.effective_chat.id, update.effective_user.id
    args = context.args or []
    reply = update.message.reply_to_message
    if reply and args and args[0].isdigit():
        target, amount = reply.from_user.id, int(args[0])
    elif len(args) >= 2 and args[0].isdigit() and args[1].isdigit():
        target, amount = int(args[0]), int(args[1])
    else:
        await update.message.reply_text("用法：回复成员消息发「转赠 数量」，或「转赠 用户ID 数量」"); return
    if amount <= 0:
        await update.message.reply_text("❌ 转赠数量必须为正数。"); return
    if target == uid:
        await update.message.reply_text("❌ 不能转给自己。"); return
    if player_is_busy(cid, uid) or player_is_busy(cid, target):
        await update.message.reply_text("⚠️ 转赠双方有正在进行的游戏，请先结束。"); return
    fee = amount * INHERIT_FEE_PERCENT // 100
    recv = amount - fee
    async with wallet_locks[uid]:
        if game_chips[cid][uid] < amount:
            await update.message.reply_text(f"❌ 你的积分不足：需要 {amount}，当前 {game_chips[cid][uid]}。"); return
        game_chips[cid][uid] -= amount
        game_chips[cid][target] += recv
        save_data()
    fee_txt = f"（手续费 {fee}）" if fee else ""
    await update.message.reply_text(
        f"✅ {await get_name(context.application, uid)} → {await get_name(context.application, target, cid=cid)}：{amount} 积分{fee_txt}\n"
        f"💰 对方到账 {recv}｜你当前 {game_chips[cid][uid]}")


def _auction_text(cid):
    a = auctions[cid]
    remain = max(0, int(a["end_ts"] - now_bj().timestamp()))
    top = user_names.get(a["top_uid"], str(a["top_uid"])) if a["top_uid"] else "（暂无人出价）"
    return (f"🔨 积分拍卖｜{a['item']}\n"
            f"💰 当前最高价：{a['price']}（{top}）\n"
            f"⏱ 剩余 {remain} 秒｜每次加价 {a['step']}\n点击按钮出价，出价即托管，价高者得！")

async def _auction_settle(cid, app):
    """拍卖倒计时结算：有主则成交（出价时已托管支付），无主流拍。"""
    a = auctions.get(cid)
    if not a: return
    remain = a["end_ts"] - now_bj().timestamp()
    if remain > 0:
        await asyncio.sleep(remain)
        a = auctions.get(cid)
        if not a: return
    auctions.pop(cid, None); save_data()
    try:
        if a["top_uid"]:
            await safe_send(app.bot, cid, f"🔨 拍卖成交｜{a['item']}\n🎉 {await get_name(app, a['top_uid'], cid=cid)} 以 {a['price']} 积分竞得！（出价时已托管支付）")
        else:
            await safe_send(app.bot, cid, f"🔨 拍卖流拍｜{a['item']}（无人出价）")
    except Exception:
        logger.exception("拍卖结算播报异常（已吞并）")


async def cmd_auction(update, context):
    """管理员发起积分拍卖：/拍卖 物品名 起拍价，按钮加价，价高者得。"""
    if not await need_auth(update): return
    if not is_group_chat(update):
        await update.message.reply_text("⚠️ 拍卖请在群聊中使用。"); return
    if not is_bot_admin(update.effective_user.id):
        await update.message.reply_text("❌ 仅 Bot 管理员可发起拍卖。"); return
    if not AUCTION_ENABLED:
        await update.message.reply_text("❌ 拍卖功能未开启（网页「积分系统 → 积分拍卖」可开启）。"); return
    cid = update.effective_chat.id
    args = context.args or []
    if len(args) < 2 or not args[-1].isdigit():
        await update.message.reply_text("用法：/拍卖 物品名 起拍价"); return
    if cid in auctions:
        await update.message.reply_text("⚠️ 本群已有拍卖进行中，结标后再开。"); return
    item, price = " ".join(args[:-1]), int(args[-1])
    if price < 0:
        await update.message.reply_text("❌ 起拍价不能为负。"); return
    auctions[cid] = {"item": item, "price": price, "top_uid": None, "step": AUCTION_STEP,
                     "end_ts": now_bj().timestamp() + AUCTION_DURATION, "msg_id": None, "task": None}
    msg = await safe_send(context.bot, cid, _auction_text(cid),
                          reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton(f"🔨 加价 {AUCTION_STEP}", callback_data=f"auc_bid_{cid}")]]))
    if msg: auctions[cid]["msg_id"] = msg.message_id
    auctions[cid]["task"] = asyncio.create_task(_auction_settle(cid, context.application))
    save_data()


async def _auction_bid(cid, uid, context, q):
    """出价：扣新出价者（托管），退前最高价者，刷新看板。"""
    a = auctions.get(cid)
    if not a:
        await q.answer("拍卖已结束", show_alert=True); return
    if now_bj().timestamp() > a["end_ts"]:
        await q.answer("拍卖已结束，结算中…", show_alert=True); return
    if a["top_uid"] == uid:
        await q.answer("你已经是当前最高价了"); return
    new_price = a["price"] + (a["step"] if a["top_uid"] is not None else 0)
    async with wallet_locks[uid]:
        if game_chips[cid][uid] < new_price:
            await q.answer(f"积分不足：需 {new_price}，你当前 {game_chips[cid][uid]}", show_alert=True); return
        game_chips[cid][uid] -= new_price
        if a["top_uid"]:
            game_chips[cid][a["top_uid"]] += a["price"]
        a["price"], a["top_uid"] = new_price, uid
        save_data()
    await q.answer(f"✅ 出价成功：{new_price}")
    await safe_edit(context.bot, cid, a["msg_id"], _auction_text(cid),
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton(f"🔨 加价 {a['step']}", callback_data=f"auc_bid_{cid}")]]))


async def cmd_buy_points(update, context):
    """购买积分（人工确认制，无需支付通道）：玩家申请 → 私聊通知管理员 → 管理员一键确认到账。"""
    if not await need_auth(update): return
    if not is_group_chat(update):
        await update.message.reply_text("⚠️ 请在群聊中申请购买积分。"); return
    if not BUY_ENABLED:
        await update.message.reply_text("❌ 购买积分功能未开启（网页「积分系统 → 购买积分」可开启）。"); return
    args = context.args or []
    if not args or not args[0].isdigit():
        await update.message.reply_text(f"用法：充值 数量（{BUY_MIN} ~ {BUY_MAX}）\n提交申请后联系管理员转账，管理员确认后积分自动到账。"); return
    amount = int(args[0])
    if not (BUY_MIN <= amount <= BUY_MAX):
        await update.message.reply_text(f"❌ 单次购买需在 {BUY_MIN} ~ {BUY_MAX} 之间。"); return
    cid, uid = update.effective_chat.id, update.effective_user.id
    oid = secrets.token_hex(4)
    buy_orders[oid] = {"cid": cid, "uid": uid, "amount": amount, "ts": now_bj().strftime("%Y-%m-%d %H:%M")}
    save_data()
    await update.message.reply_text(f"📝 购买申请已提交：{amount} 积分（单号 {oid}）\n请联系管理员完成转账，确认后积分自动到账。")
    try:
        kb = InlineKeyboardMarkup([[InlineKeyboardButton("✅ 确认到账", callback_data=f"buyok_{oid}"),
                                    InlineKeyboardButton("❌ 取消", callback_data=f"buyno_{oid}")]])
        await context.bot.send_message(ADMIN_USER_ID,
            f"💳 购买积分申请｜单号 {oid}\n用户：{await get_name(context.application, uid, cid=cid)}（{uid}）\n群：{cid}\n数量：{amount} 积分", reply_markup=kb)
    except Exception:
        logger.exception("购买积分申请通知管理员失败（已吞并）")


async def _buy_settle(context, oid, ok, q):
    o = buy_orders.pop(oid, None)
    if not o:
        await q.answer("该申请已处理过", show_alert=True); return
    if ok:
        game_chips[o["cid"]][o["uid"]] += o["amount"]
        try:
            await context.bot.send_message(o["cid"], f"✅ 你的购买申请（{o['amount']} 积分）已确认到账，当前积分 {game_chips[o['cid']][o['uid']]}。")
        except Exception:
            pass
    save_data()
    await q.answer("已确认到账" if ok else "已取消")


# ---------- 群组管理（禁言/封禁/白名单/退群记录/操作记录） ----------
async def _is_group_admin(context, cid, uid):
    """判断是否群管理员（创建者/管理员），失败时仅认 Bot 管理员体系。"""
    if is_bot_admin(uid):
        return True
    try:
        member = await context.bot.get_chat_member(cid, uid)
        return member.status in ("administrator", "creator")
    except Exception:
        return False

def _admin_log(cid, admin_uid, action, target):
    admin_logs.append({"ts": now_bj().strftime("%Y-%m-%d %H:%M"), "cid": cid,
                       "admin": user_names.get(admin_uid, str(admin_uid)), "action": action, "target": target})

async def cmd_mute(update, context):
    """禁言：回复消息发「禁言 分钟」或「禁言 用户ID 分钟」。白名单免疫。"""
    if not await need_auth(update): return
    cid, admin = update.effective_chat.id, update.effective_user.id
    if not is_group_chat(update):
        await update.message.reply_text("⚠️ 禁言请在群聊中使用。"); return
    if not await _is_group_admin(context, cid, admin):
        await update.message.reply_text("❌ 仅管理员可操作"); return
    args = context.args or []
    reply = update.message.reply_to_message
    if reply and args and args[0].isdigit():
        target, minutes = reply.from_user.id, max(1, min(int(args[0]), 43200))
    elif len(args) >= 2 and args[0].lstrip("-").isdigit() and args[1].isdigit():
        target, minutes = int(args[0]), max(1, min(int(args[1]), 43200))
    else:
        await update.message.reply_text("用法：回复消息发「禁言 分钟」，或「禁言 用户ID 分钟」"); return
    if target in whitelist[cid]:
        await update.message.reply_text("✅ 该用户在白名单中，已跳过禁言。"); return
    if target == admin:
        await update.message.reply_text("❌ 不能禁言自己。"); return
    try:
        await context.bot.restrict_chat_member(cid, target, permissions=ChatPermissions(can_send_messages=False),
                                               until_date=int(now_bj().timestamp()) + minutes * 60)
    except Exception as e:
        await update.message.reply_text(f"❌ 禁言失败（需 bot 为群管理员且有禁言权限）：{e}"); return
    tname = user_names.get(target, str(target))
    _admin_log(cid, admin, f"禁言 {minutes} 分钟", tname); save_data()
    await update.message.reply_text(f"🔇 已禁言 {tname} {minutes} 分钟。")

async def cmd_unmute(update, context):
    if not await need_auth(update): return
    cid, admin = update.effective_chat.id, update.effective_user.id
    if not await _is_group_admin(context, cid, admin):
        await update.message.reply_text("❌ 仅管理员可操作"); return
    reply = update.message.reply_to_message
    args = context.args or []
    if reply:
        target = reply.from_user.id
    elif args and args[0].lstrip("-").isdigit():
        target = int(args[0])
    else:
        await update.message.reply_text("用法：回复消息发「解禁」，或「解禁 用户ID」"); return
    try:
        await context.bot.restrict_chat_member(cid, target, permissions=ChatPermissions(
            can_send_messages=True, can_send_other_messages=True, can_add_web_page_previews=True,
            can_send_polls=True, can_invite_users=True))
    except Exception as e:
        await update.message.reply_text(f"❌ 解禁失败：{e}"); return
    _admin_log(cid, admin, "解除禁言", user_names.get(target, str(target))); save_data()
    await update.message.reply_text(f"🔊 已解除 {user_names.get(target, target)} 的禁言。")

async def cmd_groupban(update, context):
    """Telegram 级封禁：踢出并禁止再入群（区别于 /拉黑 的 bot 层黑名单）。"""
    if not await need_auth(update): return
    cid, admin = update.effective_chat.id, update.effective_user.id
    if not is_group_chat(update):
        await update.message.reply_text("⚠️ 请在群聊中使用。"); return
    if not await _is_group_admin(context, cid, admin):
        await update.message.reply_text("❌ 仅管理员可操作"); return
    reply = update.message.reply_to_message
    args = context.args or []
    if reply:
        target = reply.from_user.id
    elif args and args[0].lstrip("-").isdigit():
        target = int(args[0])
    else:
        await update.message.reply_text("用法：回复消息发「群封」，或「群封 用户ID」"); return
    if target in whitelist[cid]:
        await update.message.reply_text("✅ 该用户在白名单中，已跳过。"); return
    try:
        await context.bot.ban_chat_member(cid, target)
    except Exception as e:
        await update.message.reply_text(f"❌ 封禁失败（需 bot 为群管理员）：{e}"); return
    tname = user_names.get(target, str(target))
    _admin_log(cid, admin, "Telegram级封禁", tname); save_data()
    await update.message.reply_text(f"🔨 已将 {tname} 封禁并移出群组（可用「群解封」撤销）。")

async def cmd_groupunban(update, context):
    if not await need_auth(update): return
    cid, admin = update.effective_chat.id, update.effective_user.id
    if not await _is_group_admin(context, cid, admin):
        await update.message.reply_text("❌ 仅管理员可操作"); return
    args = context.args or []
    if not args or not args[0].lstrip("-").isdigit():
        await update.message.reply_text("用法：群解封 用户ID"); return
    target = int(args[0])
    try:
        await context.bot.unban_chat_member(cid, target, only_if_banned=True)
    except Exception as e:
        await update.message.reply_text(f"❌ 解封失败：{e}"); return
    _admin_log(cid, admin, "Telegram级解封", str(target)); save_data()
    await update.message.reply_text(f"✅ 已解封 {target}，可重新拉入群。")

async def cmd_whitelist(update, context):
    if not await need_auth(update): return
    cid = update.effective_chat.id
    users = whitelist.get(cid, set())
    if not users:
        await update.message.reply_text("白名单为空。回复成员消息发「加白」可加入。"); return
    lines = ["📋 白名单成员", "━" * 14]
    for i, u in enumerate(sorted(users), 1):
        lines.append(f"{i}. {user_names.get(u, u)}（{u}）")
    lines.append("💡 白名单成员免疫禁言/群封；「加白」「删白」管理。")
    await safe_send_long(context.bot, cid, "\n".join(lines))

async def cmd_whitelist_add(update, context):
    if not await need_auth(update): return
    cid, admin = update.effective_chat.id, update.effective_user.id
    if not await _is_group_admin(context, cid, admin):
        await update.message.reply_text("❌ 仅管理员可操作"); return
    reply = update.message.reply_to_message
    args = context.args or []
    if reply:
        target = reply.from_user.id
    elif args and args[0].lstrip("-").isdigit():
        target = int(args[0])
    else:
        await update.message.reply_text("用法：回复成员消息发「加白」，或「加白 用户ID」"); return
    whitelist[cid].add(target); save_data()
    _admin_log(cid, admin, "加白名单", user_names.get(target, str(target)))
    await update.message.reply_text(f"✅ 已把 {user_names.get(target, target)} 加入白名单。")

async def cmd_whitelist_del(update, context):
    if not await need_auth(update): return
    cid, admin = update.effective_chat.id, update.effective_user.id
    if not await _is_group_admin(context, cid, admin):
        await update.message.reply_text("❌ 仅管理员可操作"); return
    reply = update.message.reply_to_message
    args = context.args or []
    if reply:
        target = reply.from_user.id
    elif args and args[0].lstrip("-").isdigit():
        target = int(args[0])
    else:
        await update.message.reply_text("用法：回复成员消息发「删白」，或「删白 用户ID」"); return
    whitelist[cid].discard(target); save_data()
    _admin_log(cid, admin, "移出白名单", user_names.get(target, str(target)))
    await update.message.reply_text(f"✅ 已把 {user_names.get(target, target)} 移出白名单。")

async def cmd_adminlist_tg(update, context):
    """列出本群 Telegram 管理员（实时接口）。"""
    if not await need_auth(update): return
    cid = update.effective_chat.id
    try:
        admins = await context.bot.get_chat_administrators(cid)
    except Exception as e:
        await update.message.reply_text(f"❌ 获取失败：{e}"); return
    lines = ["👥 本群管理员", "━" * 14]
    for a in sorted(admins, key=lambda x: (x.status != "creator", x.user.id)):
        mark = "👑" if a.status == "creator" else "⚙️"
        lines.append(f"{mark} {a.user.first_name or ''}（{a.user.id}）")
    await safe_send_long(context.bot, cid, "\n".join(lines))

async def on_member_event(update, context):
    """成员进出事件：退群/入群记录（bot 需为群管理员才能收到）。"""
    try:
        cmu = update.chat_member
        if not cmu:
            return
        cid = cmu.chat.id
        new, old = cmu.new_chat_member, cmu.old_chat_member
        uid, name = new.user.id, new.user.first_name or f"用户{new.user.id}"
        ts = now_bj().strftime("%Y-%m-%d %H:%M")
        if new.status == "left" and old.status != "left":
            leave_records[cid].append({"ts": ts, "uid": uid, "name": name})
            leave_records[cid] = leave_records[cid][-100:]
        elif new.status in ("member", "administrator") and old.status in ("left", "kicked"):
            leave_records[cid].append({"ts": ts, "uid": uid, "name": name, "join": True})
            leave_records[cid] = leave_records[cid][-100:]
        _remember_name(update)
        save_data()
    except Exception:
        logger.exception("成员事件处理异常（已吞并）")

async def on_join_request(update, context):
    """入群申请记录（群需开启「申请加入」；批准在 Telegram 客户端原生操作）。"""
    try:
        req = update.chat_join_request
        if not req:
            return
        cid = req.chat.id
        uid, name = req.from_user.id, req.from_user.first_name or f"用户{req.from_user.id}"
        join_requests[cid].append({"ts": now_bj().strftime("%Y-%m-%d %H:%M"), "uid": uid, "name": name})
        join_requests[cid] = join_requests[cid][-100:]
        save_data()
    except Exception:
        logger.exception("入群申请处理异常（已吞并）")



async def season_settle_scheduler(app):
    """独立赛季结算调度：每 60 秒检查一次到点，精确到分钟结算（不再依赖每日 0 点循环，避免最多延迟 ~24h）。"""
    while True:
        try:
            if season_active and now_bj().timestamp() >= season_end_ts:
                await season_settle(app)
        except Exception:
            logger.exception("season_settle_scheduler 本轮异常（已吞并继续，下个周期重试）")
        await asyncio.sleep(60)


async def daily_reset_scheduler(app):
    global last_business_date
    today = now_bj().strftime("%Y-%m-%d")
    # 第一次启动只记录业务日，避免因部署重启立刻重置玩家积分。
    if not last_business_date:
        last_business_date = today; save_data()
    while True:
        now = now_bj(); target = (now + timedelta(days=1)).replace(hour=0, minute=0, second=1, microsecond=0)
        await asyncio.sleep((target-now).total_seconds())
        try:
            today = now_bj().strftime("%Y-%m-%d")
            # 排位赛到点自动结算已移至独立的 season_settle_scheduler（精确到分钟），此处不再处理
            # 午夜仅清理「刚结束的那一天」德州当日榜；保留 _archive 与其他日期历史，避免清空全部历史盈亏
            finished_day = (now_bj() - timedelta(days=1)).strftime("%Y-%m-%d")
            poker_profit_by_date.pop(finished_day, None)
            # 统一积分永久不清零，无需每日重置。
            # 排位赛仍每日重置为起始分；进行中的排位局跳过本次重置，待其结算时在 settle_poker 内补重置（跨午夜补重置）。
            if season_active:
                season_protected = set()
                for poker in active_poker_games.values():
                    if poker.season and poker.phase != "waiting":
                        season_protected.update((poker.chat_id, uid) for uid in poker.players)
                day_key = (now_bj() - timedelta(days=1)).strftime("%Y-%m-%d")
                for cid, users in season_points.items():
                    for uid in list(users.keys()):
                        if (cid, uid) in season_protected:
                            continue  # 进行中排位局跳过，等结算补重置
                        day_profit = users[uid] - SEASON_START_CHIPS
                        if day_profit:
                            season_profit_by_date[day_key][cid][uid] += day_profit
                        users[uid] = SEASON_START_CHIPS
                save_data()
            for cid in race_daily_stats: race_daily_stats[cid] = [0] * HORSE_COUNT
            archive_old_profit_data()
            # 积分系统：清掉前天的聊天积分（保留当天用于跨午夜），过期红包退余款
            chat_today.pop((now_bj() - timedelta(days=2)).strftime("%Y-%m-%d"), None)
            for pid in list(rp_packets.keys()):
                p = rp_packets[pid]
                if now_bj().timestamp() - p["ts"] > 86400:
                    if p["left_amt"] > 0:
                        game_chips[p["cid"]][p["from"]] += p["left_amt"]
                    rp_packets.pop(pid, None)
            save_data()
            # 清理已到期的限时商店称号
            _now_ts = int(now_bj().timestamp())
            for _u in list(title_expiry.keys()):
                for _t in list(title_expiry[_u].keys()):
                    if title_expiry[_u][_t] <= _now_ts:
                        title_expiry[_u].pop(_t, None)
                        user_titles.get(_u, set()).discard(_t)
                        if title_equipped.get(_u) == _t:
                            title_equipped.pop(_u, None)
                if not title_expiry[_u]:
                    del title_expiry[_u]
                if _u in user_titles and not user_titles[_u]:
                    del user_titles[_u]
            daily_emergency_used.clear(); last_business_date = today; save_data()
        except Exception:
            logger.exception("daily_reset_scheduler 本轮异常（已吞并继续，下个周期重试）")

async def leaderboard_scheduler(app):
    while True:
        now = now_bj(); target = now.replace(hour=23, minute=50, second=0, microsecond=0)
        if target <= now: target += timedelta(days=1)
        await asyncio.sleep((target-now).total_seconds())
        try:
            # 只推送并清空德州当日榜；其他游戏榜保留累计（总数）
            date = now_bj().strftime("%Y-%m-%d"); texas_snapshot = poker_profit_by_date.pop(date, {})
            # 兜底：业务日在 23:50 翻日，23:50-23:59 的下注记录在下一日业务日键下，一并并入当日榜避免丢失
            date_next = business_date()
            if date_next != date:
                for c, ud in poker_profit_by_date.pop(date_next, {}).items():
                    texas_snapshot.setdefault(c, {})
                    for u, a in ud.items():
                        texas_snapshot[c][u] = texas_snapshot.get(c, {}).get(u, 0) + a
            for cid, data in texas_snapshot.items():
                if not data: continue
                lines = [f"🏆 德州当日排行榜（{date}）", "━"*14]
                for i, (uid, amount) in enumerate(sorted(data.items(), key=lambda x:x[1], reverse=True)[:50], 1): lines.append(f"{rank_marker(i)} {await get_name(app, uid)}：{amount:+d}")
                await safe_send_long(app.bot, cid, "\n".join(lines))
            # 排位赛每日 23:50 推送「当日分数」（每人每天从 2W 起始，当日分即当前分）
            if season_active:
                for cid in list(season_points.keys()):
                    users = season_points.get(cid, {})
                    if not users: continue
                    day_standings = sorted(users.items(), key=lambda x: (-x[1], x[0]))
                    lines = [f"🏆 第{season_id}赛季 当日分数（每人起始 {SEASON_START_CHIPS}）", "━" * 18]
                    for i, (u, val) in enumerate(day_standings[:50], 1):
                        g = season_games[cid].get(u, 0)
                        tag = "" if g >= SEASON_MIN_GAMES else f"（{g}局·未达标）"
                        lines.append(f"{rank_marker(i)} {await get_name(app, u, cid=cid, with_title=False)}：{val}｜{g}局{tag}")
                    await safe_send_long(app.bot, cid, "\n".join(lines))
            save_data()
        except Exception:
            logger.exception("leaderboard_scheduler 本轮异常（已吞并继续，下个周期重试）")

async def hourly_race_scheduler(app):
    last_key = None
    while True:
        try:
            now = now_bj(); key = now.strftime("%Y%m%d%H")
            if now.minute == 0 and key != last_key:
                last_key = key
                for cid, enabled in list(hourly_race_enabled.items()):
                    if not enabled or cid in active_horse_races: continue
                    mode = current_game_mode()
                    jackpot = race_jackpot.get(cid, 0) if mode == "official" else 0
                    race = HorseRace(cid, ADMIN_USER_ID, jackpot, mode); active_horse_races[cid] = race
                    msg = await safe_send(app.bot, cid, await race.view(app), reply_markup=race.buttons())
                    if msg: race.game_msg_id = msg.message_id
                    race.task = asyncio.create_task(race.run(app)); save_data()
            next_minute = (now + timedelta(minutes=1)).replace(second=0, microsecond=0)
            await asyncio.sleep(max(1, (next_minute-now).total_seconds()))
        except Exception:
            logger.exception("hourly_race_scheduler 本轮异常（已吞并继续）")
            await asyncio.sleep(60)


# ---------- 数据备份/恢复 ----------
async def cmd_backup(update, context):
    """管理员备份：把数据文件发送到管理员私聊。"""
    uid = update.effective_user.id
    if not is_bot_admin(uid):
        await update.message.reply_text("⛔ 仅管理员可用")
        return
    # 强制写盘，确保文件是最新的
    ok = await asyncio.to_thread(force_save_now)
    if not ok:
        await update.message.reply_text("⚠️ 写盘失败，请稍后再试")
        return
    if not os.path.exists(DATA_FILE):
        await update.message.reply_text("⚠️ 数据文件不存在")
        return
    try:
        with open(DATA_FILE, "rb") as f:
            await context.bot.send_document(
                chat_id=uid,
                document=f,
                filename=f"bot_backup_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json",
                caption="📦 数据备份完成",
            )
        # 在群里发的命令时，提示一下文件已发到私聊
        if update.effective_chat.id != uid:
            await update.message.reply_text("✅ 备份文件已发送到你的私聊")
    except Exception:
        logger.exception("备份失败")
        await update.message.reply_text("⚠️ 备份失败，请先私聊我发 /start 后再试")


async def cmd_restore(update, context):
    """管理员恢复：回复一个 JSON 备份文件来恢复数据，直接载入内存立即生效（不依赖平台重启）。"""
    global data_dirty
    uid = update.effective_user.id
    if not is_bot_admin(uid):
        await update.message.reply_text("⛔ 仅管理员可用")
        return
    replied = update.message.reply_to_message
    if not replied or not replied.document:
        await update.message.reply_text("⚠️ 请回复一个 JSON 备份文件，再发送 /restore\n\n用法：点开备份文件 → 回复 → 发送 /restore")
        return
    tmp_path = f"{DATA_FILE}.restore_tmp"
    try:
        # 下载并验证备份文件
        tg_file = await context.bot.get_file(replied.document.file_id)
        await tg_file.download_to_drive(tmp_path)
        with open(tmp_path, "r", encoding="utf-8") as f:
            data = json.load(f)
        if not isinstance(data, dict):
            raise ValueError("备份文件格式错误：不是字典")
        # 验证通过：先阻止后台保存线程用旧数据覆盖新文件
        data_dirty = False
        if save_event is not None:
            save_event.clear()
        # 把当前数据另存一份，再写入新数据
        if os.path.exists(DATA_FILE):
            shutil.copy2(DATA_FILE, f"{DATA_FILE}.restore_bak")
        os.replace(tmp_path, DATA_FILE)
        # 关键修复：直接把新文件读进内存 + 落盘，不依赖平台重启。
        # 原实现 os._exit(1) 等平台重启后重新加载，但重启若重建容器，刚写入的文件会被清空 → 恢复失效。
        load_data()
        data_dirty = False
        # 恢复摘要：一眼确认恢复成没成功，不用再翻 /列表
        try:
            all_players = {u for users in list(game_chips.values()) for u in users}
            game_total = sum(sum(users.values()) for users in list(game_chips.values()))
            await update.message.reply_text("\n".join([
                "✅ 数据恢复成功，已立即生效（无需重启）",
                "━━━━━━━━━━━━━━━",
                f"👥 玩家总数：{len(all_players)}",
                f"💰 积分总量：{game_total}",
                f"📋 授权群：{len(AUTHORIZED_GROUPS)}",
                f"🏆 赛季：{'进行中 · ' + (season_name or '未命名') if season_active else '未开启'}",
                "",
                "⚠️ 如有正在进行的牌局，请重新开局。",
            ]))
        except Exception:
            logger.exception("生成恢复摘要失败")
            await update.message.reply_text("✅ 数据恢复成功，已立即生效（无需重启）")
        logger.warning("管理员 %s 执行了数据恢复，已直接载入内存", uid)
    except json.JSONDecodeError:
        await update.message.reply_text("⚠️ 文件不是有效的 JSON 格式，恢复已取消")
        if os.path.exists(tmp_path):
            os.remove(tmp_path)
    except Exception as e:
        logger.exception("恢复失败")
        await update.message.reply_text(f"⚠️ 恢复失败：{e}")
        if os.path.exists(tmp_path):
            os.remove(tmp_path)


async def post_init(app):
    background_tasks.update({
        asyncio.create_task(daily_reset_scheduler(app)), 
        asyncio.create_task(leaderboard_scheduler(app)), 
        asyncio.create_task(season_settle_scheduler(app)), 
        asyncio.create_task(hourly_race_scheduler(app)),
        asyncio.create_task(data_save_worker())
    })
    # 重启恢复：进行中的拍卖继续倒计时结算（托管分在存档里，不丢）
    for _cid, _a in list(auctions.items()):
        if not _a.get("task"):
            try: _a["task"] = asyncio.create_task(_auction_settle(_cid, app))
            except Exception: pass
    # 注册 Telegram 原生命令菜单（仅支持拉丁字符命令，中文命令走自定义路由）。
    # 作用：群里打 / 能看到、能点；命令以 bot_command 实体发送，不受隐私模式影响，必定送达。
    try:
        menu = [
            BotCommand("start", "开始 / 菜单 / 帮助"),
            BotCommand("dz", "德州扑克"),
            BotCommand("sc", "赛车"),
            BotCommand("21", "21点"),
            BotCommand("jinhua", "炸金花"),
            BotCommand("sign", "每日签到"),
            BotCommand("mypoints", "我的积分"),
            BotCommand("mall", "积分商城"),
            BotCommand("end", "结束当前游戏"),
            BotCommand("add", "加/减积分(正加负减)"),
            BotCommand("cx", "盈亏查询"),
            BotCommand("ph", "排行榜"),
            BotCommand("sq", "授权群组"),
            BotCommand("qxsh", "取消授权"),
            BotCommand("addadmin", "添加机器人管理员"),            BotCommand("deladmin", "移除机器人管理员"),
            BotCommand("adminlist", "查看管理员列表"),
            BotCommand("authlist", "查看已授权群"),
            BotCommand("autosm", "切换整点自动赛车"),
            BotCommand("backup", "备份数据"),
            BotCommand("restore", "恢复数据"),
            BotCommand("season", "德州排位赛"),
            BotCommand("seasonjoin", "排位报名"),
            BotCommand("seasonrank", "排位榜"),
            BotCommand("seasonhelp", "排位赛帮助"),
            BotCommand("seasonstart", "排位强制开赛(管理员)"),
            BotCommand("seasonend", "排位提前结算(管理员)"),
            BotCommand("god", "赌神称号/荣誉墙"),
            BotCommand("godgrant", "封赌神(管理员)"),
            BotCommand("godrevoke", "撤赌神(管理员)"),
            BotCommand("shop", "积分商店-称号兑换"),
            BotCommand("redeem", "兑换称号"),
            BotCommand("mytitles", "查看我的称号"),
            BotCommand("equip", "佩戴称号"),
            BotCommand("seasonpoints", "加减排位分(管理员)"),
            BotCommand("ban", "拉黑玩家(管理员)"),
            BotCommand("unban", "解封玩家(管理员)"),
            BotCommand("banlist", "查看黑名单(管理员)"),
            BotCommand("list", "管理总览(管理员/群/黑名单)"),
        ]
        await app.bot.set_my_commands(menu)
    except Exception:
        logger.warning("注册命令菜单失败（不影响主功能）")


async def post_shutdown(app):
    force_save_now()


# 命令路由：支持中文命令（Telegram 命令菜单只认拉丁字符，故用 MessageHandler 解析 /中文）
CMD_ALIASES = {
    # 中文命令
    "开始": cmd_start, "菜单": cmd_start, "帮助": cmd_start,
    "德州": cmd_dz, "德州扑克": cmd_dz,
    "赛车": cmd_sm, "sc": cmd_sm,
    "21点": cmd_21, "二十一点": cmd_21,
    "结束": cmd_end,
    "加积分": cmd_add, "加分": cmd_add,
    "盈亏": cmd_cx, "查询": cmd_cx,
    "排行": cmd_ph, "排行榜": cmd_ph, "积分榜": cmd_ph, "积分": cmd_ph,
    "授权": cmd_sq,
    "取消授权": cmd_qxshouquan,
    "授权列表": cmd_auth_list, "authlist": cmd_auth_list,
    "拉黑": cmd_ban, "ban": cmd_ban,
    "解黑": cmd_unban, "解封": cmd_unban, "取消拉黑": cmd_unban, "unban": cmd_unban,
    "黑名单": cmd_banlist, "黑名单列表": cmd_banlist, "banlist": cmd_banlist,
    "列表": cmd_list_all, "list": cmd_list_all, "总览": cmd_list_all,
    "加管理员": cmd_addadmin,
    "减管理员": cmd_deladmin,
    "管理员列表": cmd_admin_list, "管理员": cmd_admin_list,
    "adminlist": cmd_admin_list, "admins": cmd_admin_list,
    "备份": cmd_backup,
    "恢复": cmd_restore,
    "炸金花": cmd_jinhua, "jinhua": cmd_jinhua, "zjh": cmd_jinhua, "金花": cmd_jinhua,
    "签到": cmd_sign, "每日签到": cmd_sign, "签到排行": cmd_sign_rank,
    "我的积分": cmd_my_points, "积分排行": cmd_points_rank,
    "积分商城": cmd_mall, "商城": cmd_mall, "购买": cmd_mall_buy,
    "红包": cmd_redpacket, "发红包": cmd_redpacket,
    "排位": cmd_season_play, "排位赛": cmd_season_play, "赛季": cmd_season_play, "赛季赛": cmd_season_play,
    "排位报名": cmd_season_join, "报名排位": cmd_season_join, "赛季报名": cmd_season_join,
    "排位榜": cmd_season_rank, "赛季榜": cmd_season_rank, "赛季排名": cmd_season_rank,
    "排位帮助": cmd_season_help, "排位说明": cmd_season_help, "排位赛帮助": cmd_season_help, "赛季帮助": cmd_season_help, "赛季说明": cmd_season_help, "赛季赛帮助": cmd_season_help,
    "排位开赛": cmd_season_start, "排位结束": cmd_season_end, "赛季开赛": cmd_season_start, "赛季结束": cmd_season_end,
    "赌神": cmd_god, "荣誉墙": cmd_god,
    "封赌神": cmd_god_grant, "撤赌神": cmd_god_revoke,
    "商店": cmd_shop, "积分商店": cmd_shop, "称号商店": cmd_shop, "shop": cmd_shop,
    "兑换": cmd_redeem, "兑换称号": cmd_redeem, "redeem": cmd_redeem,
    "我的称号": cmd_my_titles, "我的头衔": cmd_my_titles, "mytitles": cmd_my_titles,
    "佩戴": cmd_equip, "佩戴称号": cmd_equip, "equip": cmd_equip,
    "赛季分": cmd_season_points, "加赛季分": cmd_season_points, "减赛季分": cmd_season_points, "seasonpoints": cmd_season_points,
    # 旧英文/数字别名（保留兼容，仍可用）
    "start": cmd_start, "dz": cmd_dz, "sm": cmd_sm,
    "21": cmd_21, "end": cmd_end,
    "END": cmd_end, "add": cmd_add, "adddz": cmd_add,
    "cx": cmd_cx, "ph": cmd_ph, "sq": cmd_sq, "qxsh": cmd_qxshouquan,
    "addadmin": cmd_addadmin, "deladmin": cmd_deladmin,
    "autosm": cmd_autosm, "backup": cmd_backup, "restore": cmd_restore,
    "season": cmd_season_play, "seasonplay": cmd_season_play,
    "seasonjoin": cmd_season_join, "seasonrank": cmd_season_rank,
    "seasonstart": cmd_season_start, "seasonend": cmd_season_end,
    "god": cmd_god, "godgrant": cmd_god_grant, "godrevoke": cmd_god_revoke,
    "sign": cmd_sign, "signrank": cmd_sign_rank, "mypoints": cmd_my_points,
    "pointsrank": cmd_points_rank, "mall": cmd_mall, "buy": cmd_mall_buy,
    "禁言": cmd_mute, "mute": cmd_mute, "解禁": cmd_unmute, "unmute": cmd_unmute,
    "群封": cmd_groupban, "groupban": cmd_groupban, "群解封": cmd_groupunban, "groupunban": cmd_groupunban,
    "白名单": cmd_whitelist, "加白": cmd_whitelist_add, "删白": cmd_whitelist_del,
    "群管理员": cmd_adminlist_tg, "admins": cmd_adminlist_tg,
    "转赠": cmd_inherit, "继承": cmd_inherit, "转让": cmd_inherit, "transfer": cmd_inherit,
    "拍卖": cmd_auction, "auction": cmd_auction,
    "充值": cmd_buy_points, "购买积分": cmd_buy_points, "topup": cmd_buy_points,
}
# 动态指令接管默认名：网页改指令后，旧默认名同步失效
_DYN_CMD_OWNED.update({"QUERY_CMD": "我的积分", "SIGN_CMD": "签到", "RANK_CMD": "积分排行"})

async def _dispatch_alias(cmd, args, update, context):
    """根据命令别名（无论带不带 /）分发到对应处理函数，并填充 context.args。"""
    handler = CMD_ALIASES.get(cmd)
    if not handler:
        await update.message.reply_text("❓ 未知命令，发送 /开始 查看可用命令")
        return
    context.args = args
    await handler(update, context)


async def route_command(update, context):
    """把 /中文 或 /英文 命令路由到对应处理函数。"""
    if not update.message or not update.message.text:
        return
    _remember_name(update)
    # 拉黑拦截：被封禁用户（非管理员）禁止使用全部命令
    if update.effective_user.id in BLACKLISTED_USERS and not is_bot_admin(update.effective_user.id):
        await update.message.reply_text("🚫 你已被禁止使用本机器人，如有疑问请联系管理员。"); return
    parts = update.message.text.strip().split()
    if not parts or not parts[0].startswith("/"):
        return
    cmd = parts[0][1:]
    if "@" in cmd:
        cmd = cmd.split("@", 1)[0]
    await _dispatch_alias(cmd, parts[1:], update, context)


# ---------- 云平台保活 + 云端持久化（Render / Zeabur 等无持久磁盘的平台用）----------
def start_health_server():
    """网页后台：密码登录 + 在线调设置。

    端口从环境变量 PORT 读取（平台注入），本地没有时默认 8080。
    - GET /health            → 200 ok（给 UptimeRobot ping，不需要登录）
    - GET /                  → 未登录显示登录页；已登录显示群体总览（关键数值卡片）
    - GET /page/<分组>       → 各游戏/分类设置页（左侧菜单栏导航）
    - POST /login            → 校验密码，发 Cookie 会话（7 天有效）
    - POST /save             → 分组保存：立即套用内存全局常量 + 合并写 bot_settings.json
    全部跑在独立守护线程，任何异常都不影响 bot 主逻辑。
    """
    try:
        port = int(os.environ.get("PORT", 8080))
        sessions = {}  # token -> 过期时间戳
        sess_lock = threading.Lock()

        def _check_session(cookie_header):
            if not cookie_header:
                return False
            token = None
            for part in cookie_header.split(";"):
                k, _, v = part.strip().partition("=")
                if k == "wb_session":
                    token = v
                    break
            if not token:
                return False
            with sess_lock:
                exp = sessions.get(token)
                if exp and exp > time.time():
                    return True
                sessions.pop(token, None)
            return False

        def _page(title, sidebar_active, body):
            """阿福风格布局：左侧深色菜单栏（分组可折叠子页面）+ 右侧内容区，窄屏折叠为顶部横排。"""
            sidebar_active = sidebar_active or ""
            items = []
            for gkey, name, icon in SETTINGS_GROUPS:
                active_now = sidebar_active == gkey or sidebar_active.startswith(gkey + "/")
                if gkey in SUBPAGES:
                    subs = []
                    for skey, sname in SUBPAGES[gkey]:
                        cls = "active" if sidebar_active == f"{gkey}/{skey}" else ""
                        subs.append(f"<a class='{cls}' href='/page/{gkey}/{skey}'>{sname}</a>")
                    items.append(
                        f"<details{' open' if active_now else ''}>"
                        f"<summary class='{'active' if active_now else ''}'>{icon}<span>{name}</span></summary>"
                        f"<div class='sub'>{''.join(subs)}</div></details>")
                else:
                    cls = "item active" if active_now else "item"
                    items.append(f"<a class='{cls}' href='/page/{gkey}'>{icon}<span>{name}</span></a>")
            return ("<!DOCTYPE html><html lang='zh'><head><meta charset='utf-8'>"
                    "<meta name='viewport' content='width=device-width, initial-scale=1'>"
                    f"<title>{title} - 机器人后台</title><style>"
                    "*{box-sizing:border-box}"
                    "body{background:#151621;color:#e6e5f0;font-family:system-ui,sans-serif;margin:0}"
                    ".wrap{display:flex;min-height:100vh}"
                    ".side{width:210px;background:#101120;border-right:1px solid #26273a;padding:18px 12px;flex-shrink:0}"
                    ".logo{font-size:16px;font-weight:500;padding:6px 10px 16px;color:#c9c4f2}"
                    ".side a{display:flex;align-items:center;gap:10px;color:#9a99ac;text-decoration:none;"
                    "font-size:14px;padding:10px 12px;border-radius:10px;margin-bottom:2px}"
                    ".side a:hover{background:#1c1d2e;color:#e6e5f0}"
                    ".side a.active{background:#2b2854;color:#fff}"
                    ".side details{margin-bottom:2px}"
                    ".side summary{list-style:none;cursor:pointer;display:flex;align-items:center;gap:10px;"
                    "font-size:14px;color:#e6e5f0;padding:10px 12px;border-radius:10px;user-select:none}"
                    ".side summary::-webkit-details-marker{display:none}"
                    ".side summary:hover{background:#1c1d2e}"
                    ".side summary::after{content:'⌄';margin-left:auto;color:#8a89a0;font-size:12px;transition:transform .15s}"
                    ".side details[open] summary::after{transform:rotate(180deg)}"
                    ".side summary.active{background:#2b2854;color:#fff}"
                    ".sub a{padding:8px 12px 8px 30px;font-size:13px;position:relative}"
                    ".sub a::before{content:'○';position:absolute;left:13px;font-size:9px;color:#7a7990}"
                    ".badge{margin-left:auto;font-size:10px;background:#34354a;color:#a9a8bd;"
                    "border-radius:6px;padding:1px 6px}"
                    ".main{flex:1;padding:22px;max-width:860px}"
                    ".card{background:#1d1e2d;border:1px solid #2b2c40;border-radius:14px;padding:22px;margin-bottom:18px}"
                    "h1{font-size:18px;font-weight:500;margin:0 0 4px}"
                    ".sub{font-size:12px;color:#8a89a0;margin-bottom:18px}"
                    "label{display:block;font-size:13px;color:#a9a8bd;margin:14px 0 5px}"
                    "input{width:100%;background:#151621;border:1px solid #34354a;color:#e6e5f0;"
                    "border-radius:10px;padding:10px 12px;font-size:15px}"
                    "input:focus{outline:none;border-color:#7c6cf0}"
                    "button{background:#7c6cf0;color:#fff;border:none;border-radius:10px;padding:11px 26px;"
                    "font-size:15px;cursor:pointer;margin-top:18px}"
                    "button:hover{background:#8d7ef5}"
                    ".ok{color:#6fd08c;font-size:13px;margin-bottom:12px}"
                    ".err{color:#f09595;font-size:13px;margin-bottom:12px}"
                    ".cards{display:grid;grid-template-columns:repeat(auto-fill,minmax(160px,1fr));gap:14px}"
                    ".stat{background:#1d1e2d;border:1px solid #2b2c40;border-radius:14px;padding:16px}"
                    ".stat .v{font-size:22px;font-weight:500;margin-top:6px}"
                    ".stat .t{font-size:12px;color:#8a89a0}"
                    ".q{display:inline-block;margin:6px 6px 0 0;background:#2b2854;color:#d6d2f5;"
                    "text-decoration:none;font-size:13px;padding:9px 14px;border-radius:10px}"
                    ".row{display:flex;align-items:center;justify-content:space-between;gap:16px;"
                    "padding:13px 2px;border-bottom:1px solid #26273a}"
                    ".row:last-child{border-bottom:none}"
                    ".row .lbl{font-size:14px;color:#c9c8da}"
                    ".row .lbl small{display:block;color:#8a89a0;font-size:12px;margin-top:2px}"
                    ".row input[type=number],.row input[type=text]{width:220px;flex-shrink:0}"
                    ".tg{position:relative;width:44px;height:24px;flex-shrink:0}"
                    ".tg input{opacity:0;width:0;height:0;position:absolute}"
                    ".tg .sl{position:absolute;inset:0;background:#34354a;border-radius:24px;transition:.2s;cursor:pointer}"
                    ".tg .sl:before{content:'';position:absolute;width:18px;height:18px;left:3px;top:3px;"
                    "background:#fff;border-radius:50%;transition:.2s}"
                    ".tg input:checked+.sl{background:#7c6cf0}"
                    ".tg input:checked+.sl:before{transform:translateX(20px)}"
                    "textarea{width:100%;background:#151621;border:1px solid #34354a;color:#e6e5f0;"
                    "border-radius:10px;padding:10px 12px;font-size:14px;font-family:inherit}"
                    "textarea:focus{outline:none;border-color:#7c6cf0}"
                    ".tbl{width:100%;border-collapse:collapse;font-size:13px;margin-top:8px}"
                    ".tbl td,.tbl th{padding:8px 6px;border-bottom:1px solid #26273a;text-align:left}"
                    ".tbl th{color:#8a89a0;font-weight:400}"
                    ".tbl tr:last-child td{border-bottom:none}"
                    "@media(max-width:720px){.wrap{flex-direction:column}.side{width:100%;display:flex;"
                    "overflow-x:auto;border-right:none;border-bottom:1px solid #26273a;padding:10px}"
                    ".logo{display:none}.side a{flex-shrink:0}.main{padding:14px}"
                    ".side details{display:contents}.side summary{flex-shrink:0;padding:8px 12px;font-size:13px}"
                    ".side summary::after{display:none}.sub{display:contents}.sub a{padding:8px 12px}"
                    ".sub a::before{display:none}}"
                    "</style></head><body><div class='wrap'>"
                    f"<nav class='side'><div class='logo'>🤖 机器人后台</div>{''.join(items)}</nav>"
                    f"<main class='main'>{body}</main></div></body></html>").encode("utf-8")

        def _login_page(err=""):
            msg = "<div class='err'>密码错误，请重试</div>" if err else ""
            return ("<!DOCTYPE html><html lang='zh'><head><meta charset='utf-8'>"
                    "<meta name='viewport' content='width=device-width, initial-scale=1'>"
                    "<title>登录 - 机器人后台</title><style>"
                    "body{background:#151621;color:#e6e5f0;font-family:system-ui,sans-serif;margin:0;"
                    "display:flex;justify-content:center;padding-top:12vh}"
                    ".card{background:#1d1e2d;border:1px solid #2b2c40;border-radius:14px;padding:28px;width:min(400px,92vw)}"
                    "h1{font-size:18px;font-weight:500;margin:0 0 18px}"
                    "label{display:block;font-size:13px;color:#a9a8bd;margin-bottom:5px}"
                    "input{width:100%;background:#151621;border:1px solid #34354a;color:#e6e5f0;border-radius:10px;padding:10px 12px;font-size:15px}"
                    "button{width:100%;background:#7c6cf0;color:#fff;border:none;border-radius:10px;padding:12px;font-size:15px;cursor:pointer;margin-top:16px}"
                    ".err{color:#f09595;font-size:13px;margin-bottom:10px}"
                    ".tip{font-size:12px;color:#8a89a0;margin-top:14px}"
                    "</style></head><body><div class='card'><h1>🔐 机器人后台</h1>" + msg +
                    "<form method='post' action='/login'>"
                    "<label>管理密码</label><input type='password' name='password' autofocus>"
                    "<button type='submit'>登 录</button></form>"
                    "<div class='tip'>初始密码 admin888，登录后请立即在「安全」页修改。</div>"
                    "</div></body></html>").encode("utf-8")

        def _field_rows(gkey):
            rows = []
            for key, _g, label, ftype, lo, hi, grp in SETTINGS_FIELDS:
                if grp != gkey:
                    continue
                cur = globals().get(_g)
                if ftype == "bool":
                    checked = " checked" if cur else ""
                    rows.append(f"<div class='row'><div class='lbl'>{html.escape(label)}</div>"
                                f"<label class='tg'><input type='checkbox' name='{key}'{checked}>"
                                f"<span class='sl'></span></label></div>")
                elif ftype in ("levels", "items"):
                    if isinstance(cur, (list, tuple)) and cur and isinstance(cur[0], dict):
                        val = "\n".join(f"{x['name']}:{x['value']}" for x in cur)
                    else:
                        val = str(cur or "")
                    rows.append(f"<div style='padding:13px 2px;border-bottom:1px solid #26273a'>"
                                f"<div class='lbl'>{html.escape(label)}<small>每行一条：名称:数值</small></div>"
                                f"<textarea name='{key}' rows='5' style='margin-top:8px'>{html.escape(val)}</textarea></div>")
                elif ftype == "text":
                    rows.append(f"<div style='padding:13px 2px;border-bottom:1px solid #26273a'>"
                                f"<div class='lbl' style='display:flex;align-items:center;justify-content:space-between'>"
                                f"<span>{html.escape(label)}<small>可用占位符见默认值；支持换行</small></span>"
                                f"<a class='q' href='/tplprev/{key}'>🔍 预览</a></div>"
                                f"<textarea name='{key}' rows='5' style='margin-top:8px'>{html.escape(cur or '')}</textarea></div>")
                elif ftype == "short":
                    rows.append(f"<div class='row'><div class='lbl'>{html.escape(label)}</div>"
                                f"<input type='text' name='{key}' value='{html.escape(cur, quote=True)}' maxlength='8'></div>")
                elif ftype == "cmd":
                    rows.append(f"<div class='row'><div class='lbl'>{html.escape(label)}"
                                f"<small>改完立即生效，无需重启；旧指令同时失效</small></div>"
                                f"<input type='text' name='{key}' value='{html.escape(cur, quote=True)}' maxlength='16'></div>")
                elif ftype in ("names", "emoji", "bets"):
                    val = ",".join(str(x) for x in cur) if isinstance(cur, (list, tuple)) else str(cur)
                    rows.append(f"<div class='row'><div class='lbl'>{html.escape(label)}</div>"
                                f"<input type='text' name='{key}' value='{html.escape(val, quote=True)}'></div>")
                else:
                    rows.append(f"<div class='row'><div class='lbl'>{html.escape(label)}"
                                f"<small>范围 {lo} ~ {hi}</small></div>"
                                f"<input type='number' name='{key}' value='{cur}' step='{'0.1' if ftype == 'float' else '1'}'></div>")
            return "".join(rows)

        def _home_page():
            def stat(label, gname):
                return f"<div class='stat'><div class='t'>{label}</div><div class='v'>{globals().get(gname)}</div></div>"
            quick = "".join(f"<a class='q' href='/page/{g}'>{i} {n}</a>" for g, n, i in SETTINGS_GROUPS if g != "dashboard")
            return _page("群体总览", "dashboard",
                "<h1>📊 群体总览</h1><div class='sub'>当前生效的关键数值（改设置去左侧菜单）</div>"
                "<div class='cards'>" +
                stat("德州入座门槛", "MIN_ENTRY_CHIPS") +
                stat("新玩家初始积分", "GAME_STARTING_CHIPS") +
                stat("单回合思考(秒)", "TURN_TIMEOUT") +
                stat("赛车自动开赛(秒)", "RACE_AUTO_START") +
                stat("应急每日次数", "EMERGENCY_MAX_USES") +
                stat("炸金花底注", "JINHUA_ANTE") +
                "</div><div class='card' style='margin-top:18px'><h1>快捷入口</h1>" + quick + "</div>")

        def _members_body():
            """群组管理只读页：成员档案 / 进出记录 / 入群申请 / 白名单 / 操作记录。"""
            def tbl(headers, rows):
                if not rows:
                    return "<div class='sub' style='margin-top:8px'>暂无记录</div>"
                head = "".join(f"<th>{h}</th>" for h in headers)
                body = "".join("<tr>" + "".join(f"<td>{c}</td>" for c in r) + "</tr>" for r in rows)
                return f"<table class='tbl'><tr>{head}</tr>{body}</table>"
            parts = []
            # 1. 已见成员档案（按群汇总，每群展示活跃前 30）
            for cid, users in member_profiles.items():
                if not users:
                    continue
                ranked = sorted(users.items(), key=lambda kv: -(kv[1].get("msgs", 0) or 0))[:30]
                rows = [[html.escape(str(v.get("name", f"用户{u}"))), f"<code>{u}</code>",
                         v.get("msgs", 0), v.get("first", "-"), v.get("last", "-")] for u, v in ranked]
                parts.append(f"<div class='card'><h1>👥 已见成员 · 群 {cid}（共 {len(users)} 人，活跃前 30）</h1>"
                             f"<div class='sub'>发过言/进过群才会建档；Telegram 不允许 bot 拉取从不说话的潜水名单</div>"
                             + tbl(["成员", "ID", "消息数", "首次见到", "最近发言"], rows) + "</div>")
            if not member_profiles:
                parts.append("<div class='card'><h1>👥 已见成员</h1><div class='sub' style='margin-top:8px'>暂无档案</div></div>")
            # 2. 退群/入群记录
            lv_rows = [[r.get("ts", ""), html.escape(r.get("name", "")), f"<code>{r.get('uid', '')}</code>",
                        "🟢 入群" if r.get("join") else "🔴 退群"]
                       for cid, lst in leave_records.items() for r in reversed(lst[-30:])]
            parts.append("<div class='card'><h1>进出记录（最近 30 条）</h1>"
                         "<div class='sub'>bot 需为群管理员才能收到成员进出事件</div>"
                         + tbl(["时间", "成员", "ID", "类型"], lv_rows[-30:]) + "</div>")
            # 3. 入群申请
            jq_rows = [[r.get("ts", ""), html.escape(r.get("name", "")), f"<code>{r.get('uid', '')}</code>"]
                       for cid, lst in join_requests.items() for r in reversed(lst[-30:])]
            parts.append("<div class='card'><h1>📨 入群申请（最近 30 条）</h1>"
                         "<div class='sub'>群需开启「申请加入」；批准/拒绝在 Telegram 客户端原生操作</div>"
                         + tbl(["时间", "申请人", "ID"], jq_rows[-30:]) + "</div>")
            # 4. 白名单
            wl_rows = [[cid, html.escape(user_names.get(u, str(u))), f"<code>{u}</code>"]
                       for cid, us in whitelist.items() for u in sorted(us)]
            parts.append("<div class='card'><h1>🛡️ 白名单</h1>"
                         "<div class='sub'>免疫禁言/群封；群里回复消息发「加白」「删白」管理</div>"
                         + tbl(["群", "成员", "ID"], wl_rows) + "</div>")
            # 5. 管理员操作记录
            op_rows = [[r.get("ts", ""), f"群 {r.get('cid', '')}", html.escape(r.get("admin", "")),
                        html.escape(r.get("action", "")), html.escape(r.get("target", ""))]
                       for r in reversed(admin_logs[-30:])]
            parts.append("<div class='card'><h1>📜 管理员操作记录（最近 30 条）</h1>"
                         "<div class='sub'>bot 执行的每次禁言/封禁/白名单操作自动留档</div>"
                         + tbl(["时间", "群", "操作人", "动作", "对象"], op_rows[-30:]) + "</div>")
            return "".join(parts)

        def _admin_page(gkey, sub=None, saved=False, bad=False, note="", err=""):
            gname, gicon = next((n, i) for k, n, i in SETTINGS_GROUPS if k == gkey)
            msg = "<div class='ok'>✅ 已保存并立即生效</div>" if saved else ""
            msg += "<div class='err'>部分数值超出范围或非法，已跳过这些项</div>" if bad else ""
            msg += f"<div class='ok'>{html.escape(note)}</div>" if note else ""
            msg += f"<div class='err'>{html.escape(err)}</div>" if err else ""
            if gkey == "members":
                body = f"<h1>{gicon} {gname}</h1><div class='sub'>数据只读展示，管理操作在群里用命令完成</div>{msg}" + _members_body()
            elif gkey == "admin":
                def _btn(action, key, val, label, color="#7c6cf0"):
                    return (f"<form style='display:inline' method='post' action='/adminops2'>"
                            f"<input type='hidden' name='op' value='{action}'>"
                            f"<input type='hidden' name='{key}' value='{val}'>"
                            f"<button style='margin:0;padding:4px 12px;font-size:12px;background:{color};margin-top:0'>{label}</button></form>")
                if sub == "auth":
                    rows = "".join(f"<tr><td><code>{g}</code></td><td>{_btn('authdel', 'cid', g, '取消授权', '#e06666')}</td></tr>"
                                   for g in sorted(AUTHORIZED_GROUPS))
                    body = (f"<h1>{gicon} 授权群管理</h1>"
                            "<div class='sub'>授权群里的玩家才能使用游戏；也可在群里发 /授权</div>{msg}"
                            "<div class='card'><table class='tbl'><tr><th>群 ID</th><th>操作</th></tr>"
                            + (rows or "<tr><td colspan='2'>暂无授权群</td></tr>") + "</table>"
                            "<form method='post' action='/adminops2' style='display:flex;gap:10px;margin-top:14px'>"
                            "<input type='hidden' name='op' value='authadd'>"
                            "<input type='number' name='cid' placeholder='群 ID（-100 开头）' required style='flex:1'>"
                            "<button type='submit' style='margin-top:0'>➕ 添加授权</button></form></div>")
                elif sub == "blacklist":
                    rows = "".join(f"<tr><td><code>{u}</code></td><td>{html.escape(user_names.get(u, ''))}</td>"
                                   f"<td>{_btn('unblack', 'uid', u, '解黑')}</td></tr>"
                                   for u in sorted(BLACKLISTED_USERS))
                    body = (f"<h1>{gicon} 拉黑管理</h1>"
                            "<div class='sub'>被拉黑的玩家无法使用机器人任何功能；也可群里 /拉黑 /解黑</div>{msg}"
                            "<div class='card'><table class='tbl'><tr><th>ID</th><th>名字</th><th>操作</th></tr>"
                            + (rows or "<tr><td colspan='3'>黑名单为空</td></tr>") + "</table>"
                            "<form method='post' action='/adminops2' style='display:flex;gap:10px;margin-top:14px'>"
                            "<input type='hidden' name='op' value='black'>"
                            "<input type='number' name='uid' placeholder='用户 ID' required style='flex:1'>"
                            "<button type='submit' style='margin-top:0;background:#e06666'>🔨 拉黑</button></form></div>")
                elif sub == "god":
                    god = next((u for u, ts in user_titles.items() if TITLE_GAMBLING_GOD in ts), None)
                    cur = (f"<code>{god}</code> {html.escape(user_names.get(god, ''))}" if god else "暂无（全局唯一，封新撤旧）")
                    body = (f"<h1>{gicon} 赌神称号</h1><div class='sub'>全局唯一：封新人自动撤销上任</div>{msg}"
                            "<div class='card'><table class='tbl'><tr><th>现任赌神</th></tr>"
                            f"<tr><td>{cur}　{_btn('godrevoke', 'uid', god or 0, '撤销', '#e06666') if god else ''}</td></tr></table>"
                            "<form method='post' action='/adminops2' style='display:flex;gap:10px;margin-top:14px'>"
                            "<input type='hidden' name='op' value='godgrant'>"
                            "<input type='number' name='uid' placeholder='用户 ID' required style='flex:1'>"
                            "<button type='submit' style='margin-top:0'>👑 封赌神</button></form></div>")
                elif sub == "seasonpts":
                    body = (f"<h1>{gicon} 排位分调整</h1>"
                            "<div class='sub'>给玩家加/减排位分（正加负减）；赛季未开始时需玩家已在赛季名单</div>{msg}"
                            "<div class='card'><form method='post' action='/adminops2'>"
                            "<input type='hidden' name='op' value='seasonpts'>"
                            "<div class='row'><div class='lbl'>群 ID</div><input type='number' name='cid' required></div>"
                            "<div class='row'><div class='lbl'>用户 ID</div><input type='number' name='uid' required></div>"
                            "<div class='row'><div class='lbl'>排位分变动<small>正数=加，负数=减</small></div>"
                            "<input type='number' name='amount' value='100' required></div>"
                            "<button type='submit'>💾 执行调整</button></form></div>")
                elif sub == "orders":
                    rows = "".join(f"<tr><td>{html.escape(str(o.get('ts', '')))}</td><td>{html.escape(str(o.get('name', '')))}</td>"
                                   f"<td>{html.escape(str(o.get('item', '')))}</td><td>{o.get('price', 0)}</td>"
                                   f"<td><code>{o.get('cid', '')}</code></td></tr>"
                                   for o in reversed(mall_orders[-50:]))
                    body = (f"<h1>{gicon} 商城订单（最近 50）</h1>"
                            "<div class='sub'>玩家下单记录；发货请线下完成</div>{msg}"
                            "<div class='card'><table class='tbl'><tr><th>时间</th><th>玩家</th><th>商品</th><th>价格</th><th>群</th></tr>"
                            + (rows or "<tr><td colspan='5'>暂无订单</td></tr>") + "</table></div>")
                else:
                    first = SUBPAGES["admin"][0][0]
                    return _admin_page(gkey, sub=first, saved=saved, bad=bad, note=note, err=err)
            elif gkey == "security":
                is_default = _web_password == WEB_DEFAULT_PASSWORD
                warn = "<div class='err'>⚠️ 当前还在用初始密码，建议立即修改（至少4位）</div>" if is_default else ""
                body = (f"<h1>{gicon} {gname}</h1><div class='sub'>修改后台登录密码</div>{msg}{warn}"
                        "<form method='post' action='/save'>"
                        "<input type='hidden' name='group' value='security'>"
                        "<label>新密码（至少4位）<input type='password' name='new_password'></label>"
                        "<button type='submit'>💾 保存密码</button></form>")
            elif sub:
                # 子页面制（照阿福模板：积分相关 → 积分设置/每日签到/…）
                subs = {k: n for k, n in SUBPAGES.get(gkey, [])}
                sname = subs.get(sub, sub)
                if gkey == "points" and sub == "adjust":
                    body = (f"<h1>{gicon} {sname}</h1>"
                            "<div class='sub'>直接给玩家加/减统一积分（正数加、负数减），立即生效并落盘；等效群里的 /add 命令</div>{msg}"
                            "<div class='card'><form method='post' action='/points_adj'>"
                            "<div class='row'><div class='lbl'>群 ID<small>授权群聊的数字 ID（-100 开头）</small></div>"
                            "<input type='number' name='cid' required></div>"
                            "<div class='row'><div class='lbl'>用户 ID<small>玩家的数字 ID</small></div>"
                            "<input type='number' name='uid' required></div>"
                            "<div class='row'><div class='lbl'>积分变动<small>正数=加分，负数=扣分，0 无效</small></div>"
                            "<input type='number' name='amount' value='1000' required></div>"
                            "<button type='submit'>💾 执行加减分</button></form></div>")
                elif gkey == "points" and sub == "rule":
                    cap = f"每日上限 {CHAT_DAILY_CAP} 分" if CHAT_DAILY_CAP else "不设上限"
                    fee = f"（手续费 {INHERIT_FEE_PERCENT}%）" if INHERIT_FEE_PERCENT else "（免手续费）"
                    body = (f"<h1>💰 {sname}</h1><div class='sub'>当前生效规则（改设置自动更新）</div>{msg}"
                            "<div class='card'><table class='tbl'>"
                            f"<tr><th>获取</th><td>聊天：每满 {CHAT_CHARS_PER} 字符记 {CHAT_REWARD} 分，{cap}；"
                            f"签到：基础 {SIGN_BASE_REWARD} 分，连续满 7 天额外 +{SIGN_STREAK_BONUS} 分；抢积分红包"
                            + (f"；充值：{BUY_MIN}~{BUY_MAX}/次（管理员确认到账）" if BUY_ENABLED else "") + "</td></tr>"
                            "<tr><th>消耗</th><td>发积分红包；积分商城下单（"
                            + ("、".join(f"{x['name']} {x['value']}分" for x in MALL_ITEMS) or "暂无商品")
                            + "）；参与拍卖出价</td></tr>"
                            f"<tr><th>转赠</th><td>{'开启' if INHERIT_ENABLED else '关闭'}，把积分转给群内成员{fee}</td></tr>"
                            f"<tr><th>拍卖</th><td>{'开启' if AUCTION_ENABLED else '关闭'}，每次加价 {AUCTION_STEP}，时长 {AUCTION_DURATION} 秒</td></tr>"
                            "<tr><th>等级</th><td>"
                            + " ≥ ".join(f"{x['name']} {x['value']}分" for x in POINT_LEVELS) + "</td></tr>"
                            "</table></div>")
                else:
                    body = (f"<h1>{gicon} {sname}</h1><div class='sub'>保存立即生效，无需重启</div>{msg}"
                            "<div class='card'><form method='post' action='/save'>"
                            f"<input type='hidden' name='group' value='{gkey}/{sub}'>"
                            + _field_rows(f"{gkey}/{sub}") +
                            "<button type='submit'>💾 保 存</button></form></div>")
            else:
                # 无子页分组照旧；有子页分组落到第一个子页
                if gkey in SUBPAGES and SUBPAGES[gkey]:
                    first = SUBPAGES[gkey][0][0]
                    return _admin_page(gkey, sub=first, saved=saved, bad=bad)
                body = (f"<h1>{gicon} {gname}</h1><div class='sub'>保存立即生效，无需重启</div>{msg}"
                        "<div class='card'><form method='post' action='/save'>"
                        f"<input type='hidden' name='group' value='{gkey}'>"
                        + _field_rows(gkey) +
                        "<button type='submit'>💾 保 存</button></form></div>")
                if gkey == "general":
                    admin_rows = ""
                    for a in sorted(BOT_ADMINS):
                        if a in ADMIN_USER_IDS:
                            src = "种子管理员(代码写入,不可移除)"
                        else:
                            src = (f"<form style='display:inline' method='post' action='/adminops'>"
                                   f"<input type='hidden' name='action' value='del'>"
                                   f"<input type='hidden' name='uid' value='{a}'>"
                                   f"<button style='margin:0;padding:4px 12px;font-size:12px;background:#e06666;margin-top:0'>移除</button></form>")
                        admin_rows += f"<tr><td><code>{a}</code></td><td>{src}</td></tr>"
                    body += ("<div class='card'><h1>🛡️ Bot 管理员</h1>"
                             "<div class='sub'>种子管理员来自代码/环境变量，防锁死不可移除；新增的重启不丢。</div>"
                             f"<table class='tbl'><tr><th>ID</th><th>操作</th></tr>{admin_rows}</table>"
                             "<form method='post' action='/adminops' style='display:flex;gap:10px;margin-top:14px'>"
                             "<input type='hidden' name='action' value='add'>"
                             "<input type='number' name='uid' placeholder='用户数字ID' required style='flex:1'>"
                             "<button type='submit' style='margin-top:0'>➕ 添加管理员</button></form></div>")
            return _page(gname, gkey, body)

        def _tpl_preview(key):
            samples = {
                "sign_msg_tpl": dict(name="玩家A", streak=7, reward=1000, bonus="（含连续7天额外奖励）", balance=50000),
                "query_msg_tpl": dict(name="玩家A", balance=50000, level_line="🎖 等级：黄金\n", signed="✅ 已签", streak=7, today_chat=100),
                "add_msg_tpl": dict(target="玩家B", verb="添加", amount=1000, balance=51000),
            }
            kw = samples.get(key)
            if not kw:
                out = "该字段不支持预览"
            else:
                gname = next((g for k, g, *_r in SETTINGS_FIELDS if k == key), None)
                tpl = globals().get(gname, "") if gname else ""
                out = _fmt_tpl(key, **kw) if (tpl or "").strip() else MSG_TPL_DEFAULTS[key].format(**kw)
            return ("<!DOCTYPE html><html lang='zh'><head><meta charset='utf-8'>"
                    "<meta name='viewport' content='width=device-width, initial-scale=1'>"
                    "<title>预览 - 机器人后台</title><style>"
                    "body{background:#151621;color:#e6e5f0;font-family:system-ui,sans-serif;margin:0;"
                    "display:flex;justify-content:center;padding-top:10vh}"
                    "pre{background:#1d1e2d;border:1px solid #2b2c40;border-radius:14px;padding:24px;"
                    "width:min(420px,92vw);white-space:pre-wrap;font-size:15px;line-height:1.7;font-family:inherit}"
                    "</style></head><body><pre>" + html.escape(out) + "</pre></body></html>").encode("utf-8")

        class _AdminHandler(BaseHTTPRequestHandler):
            def _send(self, code, body, headers=None):
                self.send_response(code)
                for k, v in (headers or []):
                    self.send_header(k, v)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)

            def _redirect(self, to, cookie=None):
                headers = [("Location", to)]
                if cookie:
                    headers.append(("Set-Cookie", cookie))
                self.send_response(302)
                for k, v in headers:
                    self.send_header(k, v)
                self.send_header("Content-Length", "0")
                self.end_headers()

            def do_GET(self):
                path = urlparse(self.path).path
                if path == "/health":
                    self._send(200, b"ok", [("Content-Type", "text/plain")]); return
                if not _check_session(self.headers.get("Cookie")):
                    self._send(200, _login_page()); return
                qs = parse_qs(urlparse(self.path).query)
                saved, bad = "saved" in qs, "bad" in qs
                note = qs.get("note", [""])[0]
                err = qs.get("err", [""])[0]
                if path == "/":
                    self._send(200, _home_page()); return
                mm = re.fullmatch(r"/tplprev/([a-z0-9_]+)", path)
                if mm:
                    self._send(200, _tpl_preview(mm.group(1))); return
                m = re.fullmatch(r"/page/([a-z]+)(?:/([a-z0-9_]+))?", path)
                if m and m.group(1) in {g for g, _n, _i in SETTINGS_GROUPS}:
                    self._send(200, _admin_page(m.group(1), sub=m.group(2), saved=saved, bad=bad, note=note, err=err)); return
                self._send(404, b"not found", [("Content-Type", "text/plain")])

            def do_POST(self):
                try:
                    length = int(self.headers.get("Content-Length", 0))
                    form = parse_qs(self.rfile.read(length).decode("utf-8"))
                except Exception:
                    form = {}
                path = urlparse(self.path).path
                if path == "/login":
                    pwd = (form.get("password", [""])[0] or "").strip()
                    if secrets.compare_digest(pwd, _web_password):
                        token = secrets.token_urlsafe(32)
                        with sess_lock:
                            sessions[token] = time.time() + 7 * 86400
                        self._redirect("/", cookie=f"wb_session={token}; Path=/; HttpOnly; SameSite=Lax; Max-Age=604800")
                    else:
                        self._send(200, _login_page(err=1))
                    return
                if path == "/adminops":
                    action = form.get("action", [""])[0]
                    try:
                        uid = int(form.get("uid", [""])[0])
                    except ValueError:
                        self._redirect("/page/general"); return
                    if action == "add" and uid > 0 and uid not in BOT_ADMINS:
                        BOT_ADMINS.add(uid); save_data()
                    elif action == "del" and uid not in ADMIN_USER_IDS:
                        BOT_ADMINS.discard(uid); save_data()
                    self._redirect("/page/general"); return
                if path == "/adminops2":
                    op = form.get("op", [""])[0]
                    sub_map = {"authadd": "auth", "authdel": "auth", "black": "blacklist",
                               "unblack": "blacklist", "godgrant": "god", "godrevoke": "god", "seasonpts": "seasonpts"}
                    def _back(note="", err=""):
                        sub = sub_map.get(op, "auth")
                        q = ("?note=" + quote(note)) if note else ("?err=" + quote(err) if err else "")
                        self._redirect(f"/page/admin/{sub}" + q)
                    try:
                        cid_ = int(form["cid"][0]) if form.get("cid") else None
                        uid_ = int(form["uid"][0]) if form.get("uid") else None
                        amt = int(form["amount"][0]) if form.get("amount") else None
                    except ValueError:
                        _back(err="参数必须是数字"); return
                    if op == "authadd" and cid_:
                        AUTHORIZED_GROUPS.add(cid_); save_data(); _back(note=f"✅ 已授权群 {cid_}")
                    elif op == "authdel" and cid_:
                        AUTHORIZED_GROUPS.discard(cid_); save_data(); _back(note=f"✅ 已取消授权 {cid_}")
                    elif op == "black" and uid_:
                        BLACKLISTED_USERS.add(uid_); save_data(); _back(note=f"🔨 已拉黑 {uid_}")
                    elif op == "unblack" and uid_:
                        BLACKLISTED_USERS.discard(uid_); save_data(); _back(note=f"✅ 已解黑 {uid_}")
                    elif op == "godgrant" and uid_:
                        for _u in list(user_titles.keys()):
                            user_titles[_u].discard(TITLE_GAMBLING_GOD)
                            if not user_titles[_u]: del user_titles[_u]
                        user_titles.setdefault(uid_, set()).add(TITLE_GAMBLING_GOD)
                        save_data(); _back(note=f"👑 已将 {uid_} 封为赌神（覆盖上任）")
                    elif op == "godrevoke" and uid_:
                        user_titles[uid_].discard(TITLE_GAMBLING_GOD)
                        if title_equipped.get(uid_) == TITLE_GAMBLING_GOD: title_equipped.pop(uid_, None)
                        if uid_ in user_titles and not user_titles[uid_]: del user_titles[uid_]
                        save_data(); _back(note=f"🔻 已撤销 {uid_} 的赌神称号")
                    elif op == "seasonpts" and cid_ and uid_ and amt is not None:
                        if not season_active and uid_ not in season_points.get(cid_, {}):
                            _back(err="该玩家不在当前赛季，且赛季未激活"); return
                        if amt < 0 and season_points.get(cid_, {}).get(uid_, 0) < -amt:
                            _back(err="该玩家排位分不足"); return
                        season_points[cid_][uid_] = season_points.get(cid_, {}).get(uid_, 0) + amt
                        save_data(); _back(note=f"✅ 用户 {uid_} 排位分 {amt:+d}，当前 {season_points[cid_][uid_]}")
                    else:
                        _back(err="参数错误"); return
                    return
                if path == "/points_adj":
                    def _back(note="", err=""):
                        q = ("?note=" + quote(note)) if note else ("?err=" + quote(err) if err else "")
                        self._redirect("/page/points/adjust" + q)
                    try:
                        cid = int(form.get("cid", [""])[0]); uid = int(form.get("uid", [""])[0])
                        amount = int(form.get("amount", [""])[0])
                        if amount == 0: raise ValueError
                    except ValueError:
                        _back(err="参数错误：群ID/用户ID 必须是数字，金额不能为 0"); return
                    if player_is_busy(cid, uid):
                        _back(err="该玩家正在游戏中，请等牌局结束再调整积分"); return
                    if amount < 0 and game_chips[cid][uid] < -amount:
                        _back(err=f"扣分失败：该玩家当前积分 {game_chips[cid][uid]} 不足 {-amount}"); return
                    game_chips[cid][uid] += amount
                    force_save_now()
                    _back(note=f"✅ 已{'给' if amount > 0 else '扣除'} 用户 {uid} {abs(amount)} 积分，当前余额 {game_chips[cid][uid]}（群 {cid}）")
                    return
                if path == "/save":
                    if not _check_session(self.headers.get("Cookie")):
                        self._redirect("/"); return
                    group = form.get("group", [""])[0]
                    if group == "security":
                        save_settings({}, form.get("new_password", [""])[0])
                        self._redirect("/page/security?saved=1"); return
                    valid_keys = {k for k, _g, _l, _t, _lo, _hi, grp in SETTINGS_FIELDS if grp == group}
                    cfg = {k: v[0] for k, v in form.items() if k in valid_keys}
                    for k, _g, _l, ft, _lo, _hi, _grp in SETTINGS_FIELDS:  # checkbox 未勾选时表单不含该键 → 显式补 0（仅 bool）
                        if k in valid_keys and ft == "bool":
                            cfg.setdefault(k, "0")
                    applied = save_settings(cfg)
                    skipped = [k for k in cfg if k not in applied]
                    self._redirect(f"/page/{group}?saved=1" + ("&bad=1" if skipped else ""))
                    return
                self._send(404, b"not found", [("Content-Type", "text/plain")])

            def log_message(self, *args):
                pass  # 抑制访问日志，避免刷屏

        server = ThreadingHTTPServer(("0.0.0.0", port), _AdminHandler)
        threading.Thread(target=server.serve_forever, daemon=True).start()
        logger.info("网页后台已启动：端口 %s（/health 健康检查 · / 设置面板）", port)
    except Exception:
        logger.exception("网页后台启动失败（不影响 bot 运行）")


async def auto_backup(context):
    """定时把数据文件发给管理员私聊，当作云端持久化备份。

    无持久磁盘的平台容器重启会清空磁盘，有这份备份就能用 /restore 恢复，
    最坏只丢一个备份周期（30 分钟）的积分变动。
    """
    try:
        ok = await asyncio.to_thread(force_save_now)
        if not ok:
            logger.warning("自动备份：写盘失败，跳过本次")
            return
        if not os.path.exists(DATA_FILE):
            logger.warning("自动备份：数据文件不存在，跳过本次")
            return
        with open(DATA_FILE, "rb") as f:
            await context.bot.send_document(
                chat_id=ADMIN_USER_ID,
                document=f,
                filename=f"auto_backup_{datetime.now().strftime('%Y%m%d_%H%M')}.json",
                caption="🤖 每日自动备份（需要恢复时：回复此文件发 /restore）",
            )
        logger.info("自动备份完成")
    except Exception:
        logger.exception("自动备份失败")


def main():
    global save_event
    load_settings()  # 先套用网页端保存的设置，再启动 bot
    token = os.environ.get("BOT_TOKEN")
    if not token: logger.error("未设置 BOT_TOKEN"); return
    
    # 在主循环启动前初始化 Event
    save_event = asyncio.Event()
    
    # 资金系统：关闭并发更新，串行处理所有 update handler，消除「检查余额→扣款」之间的竞态
    # （后台任务如赛车动画、定时调度仍为并发；仅 handler 之间不再交错，杜绝并发负分）。
    builder = Application.builder().token(token).concurrent_updates(False).post_init(post_init).post_shutdown(post_shutdown)
    app = builder.build()

    # 云平台保活：健康检查服务，供 UptimeRobot 定时 ping 防止休眠
    start_health_server()

    # 云端持久化：每 24 小时自动把数据备份发给管理员，容器重启可用 /restore 恢复
    if getattr(app, "job_queue", None) is not None:
        app.job_queue.run_repeating(auto_backup, interval=86400, first=60)
        logger.info("自动备份任务已注册：每 86400 秒（24 小时）执行一次")
    else:
        logger.warning("JobQueue 不可用，自动备份未启用（需安装 python-telegram-bot[job-queue]）")

    app.add_handler(MessageHandler(filters.TEXT & filters.Regex(r'^/'), route_command))
    app.add_handler(CallbackQueryHandler(on_button)); app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND & ~filters.Regex(r'^/'), on_text))
    app.add_handler(ChatMemberHandler(on_member_event))       # 退群/入群事件（bot 需群管理员）
    app.add_handler(ChatJoinRequestHandler(on_join_request))  # 入群申请事件（群需开「申请加入」）
    app.run_polling(allowed_updates=Update.ALL_TYPES, drop_pending_updates=True)

if __name__ == "__main__": main()
