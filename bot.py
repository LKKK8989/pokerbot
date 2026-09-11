import asyncio
import contextvars
import html
import io
import json
# 版本标记：/health 与登录页底部都会显示，用于一眼核对"线上跑的是不是最新代码"
BOT_VERSION = "2026-09-11-1400"
# 主题色：key -> (主色, 深主色, 强色上的文字色, 页面底色, 侧栏底, 卡片底, 输入框底, 边框, 表头底, 悬停底)
# 网页顶栏色点一键切换，存 SETTINGS_SNAPSHOT["ui_theme"] 持久化；整套色板全量生效，不是只换 accent
_UI_THEMES = {
    "purple": ("#8b5cf6", "#6d3fd4", "#ffffff", "#161320", "#1b1728", "#211c30", "#191527", "#352e4d", "#28223d", "#262038"),
    "blue":   ("#3b82f6", "#2563eb", "#ffffff", "#131722", "#161c2a", "#1b2231", "#171d2a", "#2c3a54", "#202a40", "#212b3e"),
    "cyan":   ("#06b6d4", "#0e7490", "#ffffff", "#0f181c", "#121f26", "#17252c", "#131f26", "#25414c", "#1b3039", "#1a2b33"),
    "green":  ("#10b981", "#047857", "#ffffff", "#111813", "#141d17", "#1a251d", "#151d17", "#294233", "#1d3125", "#1b2a20"),
    "rose":   ("#f43f5e", "#be123c", "#ffffff", "#1a1215", "#1e1519", "#261a1f", "#1e1519", "#432c37", "#33222b", "#2a1d23"),
    "amber":  ("#f59e0b", "#d97706", "#ffffff", "#181510", "#1c1811", "#242017", "#1d1911", "#42391f", "#322b18", "#2b251a"),
    "black":  ("#7b8194", "#3f4453", "#ffffff", "#121214", "#161617", "#1b1b1e", "#161617", "#2c2c31", "#222225", "#1f1f23"),
    "white":  ("#dbe0ea", "#aab2c2", "#1f2430", "#131419", "#17181e", "#1d1f26", "#17181e", "#2f323d", "#232630", "#20222b"),
}
# 成员列表首字母头像色环（按 uid 取模固定颜色，同人永远同色）
_AV_COLORS = ("#8b5cf6", "#3b82f6", "#10b981", "#f59e0b", "#f43f5e", "#06b6d4", "#ec4899", "#a3e635")
_group_admins_cache = {}   # cid -> (拉取时间戳, {uid: "owner"|"admin"})，网页成员列表徽章用（5 分钟缓存）
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
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, quote, urlparse

from telegram import BotCommand, InlineKeyboardButton, InlineKeyboardMarkup, Update, ChatPermissions
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
EMERGENCY_MIN_GAMES = 0     # 归零赠送要求「累计玩过 N 局」（0=不限）；防小号纯靠归零薅分

# 游戏时间配置 (秒)
TURN_TIMEOUT = 60          # 德州/21点单回合思考时间
JINHUA_OPEN_PENDING_TIMEOUT = 600  # 金花跟平阶段（open_pending）超时自动开牌，防全员掉线牌局卡死
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
# 4 游戏总开关/仅管理员开局（后台各游戏分组可调，保存立即生效）
TEXAS_ENABLED, TEXAS_ADMIN_ONLY = 1, 0
# 德州两个模式各自独立开关（用户要求：可以只开排位、关日常，随时切换）
DAILY_TEXAS_ENABLED, RANKED_TEXAS_ENABLED = 1, 1
BJ_ENABLED, BJ_ADMIN_ONLY = 1, 0
JINHUA_ENABLED, JINHUA_ADMIN_ONLY = 1, 0
RACE_ENABLED, RACE_ADMIN_ONLY = 1, 0
STALE_TEXT_COMMAND_SECONDS = 120
# ---------- 德州排位赛 ----------
SEASON_START_CHIPS = 20000     # 排位赛起始分（独立账本，7天不清零）
SEASON_MIN_PLAYERS = 20        # 报名满 20 人自动开赛
SEASON_MIN_GAMES = 5           # 上榜最少局数
SEASON_REBUY_COUNT = 3         # 破产应急补分次数
SEASON_REBUY_AMOUNT = 2000     # 每次应急补分
SEASON_DAYS = 7                # 赛季周期（天）
SEASON_BET_PERCENT = 0.2       # 排位赛单局每人投入上限 = 本局落座玩家筹码总和 × 此比例（人少上限低，防串通）
# 排位赛德州独立参数（用户要求：排位赛可单独调规则，不用动日常德州）
# 0 = 继承日常德州对应设置；填了非 0 值则排位局用这里的值
SEASON_MIN_ENTRY_CHIPS = 0     # 入座最低排位分（0=沿用「排位分>0」的原有判定）
SEASON_FIXED_MIN_RAISE = 0     # 最低加注额
SEASON_TURN_TIMEOUT = 0        # 单回合思考时间（秒）
SEASON_ROOM_WAIT_TIMEOUT = 0   # 等待房倒计时（秒）
SEASON_SMALL_BLIND = 0         # 小盲注（0=继承；日常也是 0 时表示不设盲注）
SEASON_BIG_BLIND = 0           # 大盲注（同上）
SEASON_ANTE = 0                # 前注（每人发牌前强制投入）
# ---------- 聊天积分兑换排位分 ----------
RANKED_EXCHANGE_ENABLED = 1    # 兑换开关
RANKED_EXCHANGE_COST = 1       # 兑换比例-消耗的聊天积分（分母）
RANKED_EXCHANGE_GAIN = 1       # 兑换比例-得到的排位分（分子）→ 默认 1:1
RANKED_EXCHANGE_DAILY_LIMIT = 0  # 每人每日兑换上限（按消耗的聊天积分累计，0=不限）
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
# 设置快照：与 bot_data.json 同步持久化。
# 无持久磁盘的平台（Northflank 等）重建容器会清空 bot_settings.json，导致每次重新部署后
# 网页设置全部回退成代码默认值。把整份设置快照嵌进 bot_data.json 的 _settings 键后，
# 设置就能跟着数据一起被自动备份 / /restore 恢复，重新部署不再丢设置。
SETTINGS_SNAPSHOT = {}
WEB_DEFAULT_PASSWORD = "qwer1234"  # 首次登录用，登录后请在面板里立即修改
# 左侧菜单分组：(分组键, 显示名, 图标)
SETTINGS_GROUPS = [
    ("dashboard", "群体总览",   "📊"),
    ("texas",     "德州扑克",   "🃏"),
    ("blackjack", "21点",      "♠️"),
    ("jinhua",    "炸金花",     "♣️"),
    ("dice",      "大话骰",     "🎲"),
    ("race",      "赛车",       "🏎️"),
    ("rake",      "游戏抽水",   "💸"),
    ("points",    "积分系统",   "💰"),
    ("lottery",   "群组抽奖",   "🎉"),
    ("invite",    "邀请系统",   "🎟️"),
    ("season",    "排位赛",     "🏆"),
    ("members",   "群组管理",   "👥"),
    ("mod",       "群管中心",   "🛡️"),
    ("autodel",   "自动删除",   "🗑️"),
    ("schedule",  "定时任务",   "⏰"),
    ("commands",  "命令管理",   "⌨️"),
    ("tpls",      "话术库",     "💬"),
    ("general",   "通用与应急", "⚙️"),
    ("admin",     "管理员中心", "👑"),
    ("security",  "安全",       "🔒"),
]
# 子页面制：有子页的分组在侧边栏折叠展开（照阿福模板）。None=未开通占位页
SIDEBAR_ORDER = []   # 侧边栏自定义排序（组键列表，网页「群体总览」可 ▲▼ 调整，随设置持久化）
SIDEBAR_CHILDREN = {"texas": ["season"]}  # 把某些独立组折叠进父组显示（路由不变）：排位赛归入德州
# 群管中心（跨组聚合页）直接内嵌的高频开关；新增群管功能时往这里加键即可
MOD_PAGE_FIELDS = []
# 侧边栏四大节（照阿福/方丈：节标题 + 节内菜单项）。不在任何节里的组保持原样渲染在最后。
# 排序逻辑：机器人日常 → 群治理(成员/群管/删除) → 增长与经济(邀请/积分/抽奖) → 娱乐游戏 → 系统管理殿后
SIDEBAR_SECTIONS = [
    ("🤖 机器人设置", ["dashboard", "schedule", "commands", "tpls", "general"]),
    ("👥 群组设置",   ["members", "mod", "autodel", "invite", "points", "lottery"]),
    ("🎲 娱乐功能",   ["texas", "blackjack", "jinhua", "dice", "race", "rake"]),
    ("🛠 系统管理",   ["admin", "security"]),
]
SUBPAGES = {
    "points": [
        ("set",      "积分设置"),
        ("adjust",   "积分管理"),
        ("impexp",   "积分导入导出"),
        ("cap",      "积分每日上限"),
        ("sign",     "每日签到"),
        ("rule",     "积分规则"),
        ("rp",       "积分红包"),
        ("level",    "积分等级"),
        ("levelguard", "等级消息管控"),
        ("inherit",  "积分继承"),
        ("redeem",   "积分兑换"),
        ("mall",     "积分商城"),
        ("mallord",  "商城订单"),
        ("buy",      "购买积分"),
        ("buypkg",   "积分套餐管理"),
        ("guess",    "积分竞猜"),
    ],
    "invite": [
        ("config",  "邀请链接配置"),
        ("records", "邀请记录"),
        ("daily",   "统计"),
        ("summary", "汇总"),
        ("qualify", "合格结算"),
    ],
    "members": [
        ("mlist",   "群组成员列表"),
        ("records", "进出与申请"),
        ("ops",     "白名单与操作"),
        ("join",    "入群与观察"),
    ],
    "admin": [
        ("admins",    "Bot 管理员"),
        ("auth",      "授权群管理"),
        ("blacklist", "拉黑管理"),
        ("god",       "赌神称号"),
        ("seasonpts", "排位分调整"),
        ("fundflow",  "资金流审查"),
    ],
}
# ===== 多选字段（类型 "multi"）的可选项：settings键 -> [(值, 显示名), ...] =====
# 值只允许英文小写+下划线，渲染成一组勾选框，保存为逗号分隔字符串（顺序按这里定义）。
MULTI_OPTIONS = {
    "autodel_text_rules": [
        ("link", "链接消息(http/t.me/链接实体)"),
        ("long", "超长消息"),
        ("premium_emoji", "会员表情(自定义表情)"),
    ],
    "autodel_media_types": [
        ("photo", "图片"),
        ("video", "视频"),
        ("sticker", "贴纸"),
        ("gif", "动图(GIF)"),
        ("voice", "语音/视频圆"),
        ("document", "文档文件"),
        ("archive", "压缩包(zip/rar/7z)"),
        ("executable", "可执行文件(exe/apk)"),
        ("contact", "分享联系人"),
        ("service", "系统消息(入退群/改群名)"),
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
    ("bj_enabled",              "BJ_ENABLED",              "21点开关",                  "bool",  0,   1,       "blackjack"),
    ("bj_admin_only",           "BJ_ADMIN_ONLY",           "21点仅管理员开局",          "bool",  0,   1,       "blackjack"),
    ("jinhua_ante",             "JINHUA_ANTE",             "底注",                      "int",   1,   100000,  "jinhua"),
    ("jinhua_base",             "JINHUA_BASE",             "单注基准",                  "int",   1,   100000,  "jinhua"),
    ("jinhua_seen_double",      "JINHUA_SEEN_DOUBLE",      "看牌者投注加倍开关",        "bool",  0,   1,       "jinhua"),
    ("jinhua_enabled",          "JINHUA_ENABLED",          "炸金花开关",                "bool",  0,   1,       "jinhua"),
    ("jinhua_admin_only",       "JINHUA_ADMIN_ONLY",       "炸金花仅管理员开局",        "bool",  0,   1,       "jinhua"),
    # ---------- 大话骰（吹牛·港式标准） ----------
    ("dice_ante",               "DICE_ANTE",               "底注(开局一次性扣进奖池)",  "int",   1,   100000,  "dice"),
    ("dice_dice_count",        "DICE_DICE_COUNT",         "每人骰子数",                "int",   1,   10,      "dice"),
    ("dice_wild_one",          "DICE_WILD_ONE",           "1万能牌开关(关=无万能局,首手可叫1)", "bool", 0, 1, "dice"),
    ("dice_straight_zero",     "DICE_STRAIGHT_ZERO",      "顺子算0个(0关/1仅两人局/2所有人数;含1补位的假顺)", "int", 0, 2, "dice"),
    ("dice_leopard_bonus",     "DICE_LEOPARD_BONUS",      "豹子加成(0关/1仅两人局/2所有人数;纯豹+2花豹+1)", "int", 0, 2, "dice"),
    ("dice_drop_dice",         "DICE_DROP_DICE",          "掉骰子多轮制(0关=任何人数都一把定胜负;1开=三人以上掉骰)", "bool", 0, 1, "dice"),
    ("dice_think_seconds",     "DICE_THINK_SECONDS",      "叫牌思考秒数(超时自动开骰)", "int",   10,  600,     "dice"),
    ("dice_max_players",       "DICE_MAX_PLAYERS",        "单桌最多人数",              "int",   2,   20,      "dice"),
    ("dice_enabled",           "DICE_ENABLED",            "大话骰开关",                "bool",  0,   1,       "dice"),
    ("dice_admin_only",        "DICE_ADMIN_ONLY",         "大话骰仅管理员开局",        "bool",  0,   1,       "dice"),
    ("race_auto_start",         "RACE_AUTO_START",         "自动开赛时间(秒)",          "int",   10,  600,     "race"),
    ("race_animation_interval", "RACE_ANIMATION_INTERVAL", "动画帧间隔(秒)",            "float", 0.5, 30,      "race"),
    ("horse_count",             "HORSE_COUNT",             "赛马数量(匹)",              "int",   2,   8,       "race"),
    ("horse_names",             "HORSE_NAMES",             "赛马名称(逗号分隔)",        "names", 0,   0,       "race"),
    ("horse_emoji",             "HORSE_EMOJI",             "赛马表情(逗号分隔)",        "emoji", 0,   0,       "race"),
    ("race_track_length",       "RACE_TRACK_LENGTH",       "赛道长度(格)",              "int",   5,   50,      "race"),
    ("fixed_bet_amounts",       "FIXED_BET_AMOUNTS",       "下注按钮金额(逗号分隔)",    "bets",  0,   0,       "race"),
    ("race_odds_cap",           "RACE_ODDS_CAP",           "赔率上限(倍,0=无上限)",     "float", 0,   100,     "race"),
    ("race_enabled",            "RACE_ENABLED",            "赛车开关",                  "bool",  0,   1,       "race"),
    ("race_subsidy_enabled",    "RACE_SUBSIDY_ENABLED",    "赛车系统加奖开关(每场给奖池加钱拉人气)", "bool", 0, 1, "race"),
    ("race_subsidy_amount",     "RACE_SUBSIDY_AMOUNT",     "赛车系统加奖金额(每场,押中者按注额分)", "int", 0, 100000, "race"),
    ("race_subsidy_min_players","RACE_SUBSIDY_MIN_PLAYERS","加奖生效最少下注人数(防单人薅)", "int", 1, 50, "race"),
    ("race_subsidy_daily_cap",  "RACE_SUBSIDY_DAILY_CAP",  "加奖每日上限(每群,0=不限)", "int", 0, 10000000, "race"),
    ("race_subsidy_auto_only",  "RACE_SUBSIDY_AUTO_ONLY",  "加奖仅限自动开赛(个人发起的赛车不派奖)", "bool", 0, 1, "race"),
    ("race_admin_only",         "RACE_ADMIN_ONLY",         "赛车仅管理员开局",          "bool",  0,   1,       "race"),
    ("rake_enabled",            "RAKE_ENABLED",            "游戏抽水开关(官方模式结算)", "bool",  0,   1,       "rake"),
    ("rake_percent",            "RAKE_PERCENT",            "抽水比例(%·赢家净赢抽成)",  "int",   0,   50,      "rake"),
    ("rake_min_net",            "RAKE_MIN_NET",            "抽水门槛(净赢低于此值不抽)", "int",   0,   1000000, "rake"),
    ("broadcast_enabled",       "BROADCAST_ENABLED",       "大奖战报自动广播开关",      "bool",  0,   1,       "general"),
    ("broadcast_min_amount",    "BROADCAST_MIN_AMOUNT",    "战报阈值(单局净赢≥此值广播)", "int",  100, 10000000,"general"),
    ("game_starting_chips",     "GAME_STARTING_CHIPS",     "新玩家初始积分(全游戏统一)", "int",  100, 1000000, "general"),
    ("small_blind",             "SMALL_BLIND",             "德州小盲注(0=不设盲注)",    "int",   0,   100000,  "texas"),
    ("big_blind",               "BIG_BLIND",               "德州大盲注(0=不设盲注)",    "int",   0,   100000,  "texas"),
    ("ante",                    "ANTE",                    "德州前注(每人发牌前强制投入)", "int", 0,  100000,  "texas"),
    ("texas_enabled",           "TEXAS_ENABLED",           "德州扑克开关",              "bool",  0,   1,       "texas"),
    ("daily_texas_enabled",     "DAILY_TEXAS_ENABLED",     "日常德州开关",              "bool",  0,   1,       "texas"),
    ("ranked_texas_enabled",    "RANKED_TEXAS_ENABLED",    "排位德州开关",              "bool",  0,   1,       "texas"),
    ("texas_admin_only",        "TEXAS_ADMIN_ONLY",        "德州仅管理员开局",          "bool",  0,   1,       "texas"),
    ("stale_text_command_seconds","STALE_TEXT_COMMAND_SECONDS","过期消息忽略(秒,防翻旧账命令)", "int", 5, 3600, "general"),
    # ---------- 定时任务（时间可自行设置） ----------
    ("daily_reset_time",        "DAILY_RESET_TIME",        "每日重置时间(时:分,排位分重置等)", "short", 0, 0, "schedule"),
    ("daily_reset_enabled",     "DAILY_RESET_ENABLED",     "每日重置开关",              "bool",  0,   1,       "schedule"),
    ("leaderboard_time",        "LEADERBOARD_TIME",        "德州日榜推送时间(时:分)",   "short", 0, 0,      "schedule"),
    ("leaderboard_enabled",     "LEADERBOARD_ENABLED",     "德州日榜推送开关",          "bool",  0,   1,       "schedule"),
    ("race_hourly_minute",      "RACE_HOURLY_MINUTE",      "赛车每小时自动开赛(第几分钟)", "int", 0, 59,    "schedule"),
    ("race_auto_enabled",       "RACE_AUTO_ENABLED",       "赛车自动开赛开关(仍受时段限制)", "bool", 0, 1,    "schedule"),
    ("race_hourly_start",       "RACE_HOURLY_START",       "自动开赛时段·开始(填小时0-23)",   "int",   0,   23,      "schedule"),
    ("race_hourly_end",         "RACE_HOURLY_END",         "自动开赛时段·结束(填小时0-23；比“开始”小=通宵到第二天。例：开始18+结束2=每天18点到次日凌晨2点多)", "int",   0,   23,      "schedule"),
    ("backup_interval_hours",   "BACKUP_INTERVAL_HOURS",   "自动备份间隔(小时,改间隔重启后生效)", "int", 1, 168,   "schedule"),
    ("backup_enabled",          "BACKUP_ENABLED",          "自动备份开关(保存即时生效)", "bool",  0,   1,       "schedule"),
    ("admin_report_time",       "ADMIN_REPORT_TIME",       "经营日报推送时间(时:分,私聊管理员)", "short", 0, 0, "schedule"),
    ("admin_report_enabled",    "ADMIN_REPORT_ENABLED",    "经营日报推送开关",          "bool",  0,   1,       "schedule"),
    ("sep_announce",            None, "📣 定时群公告（每天定点推送到全部授权群）", "sep", 0, 0, "schedule"),
    ("announce_enabled",        "ANNOUNCE_ENABLED",        "定时群公告开关",            "bool",  0,   1,       "schedule"),
    ("announce_time",           "ANNOUNCE_TIME",           "公告推送时间(时:分,北京时间)", "short", 0, 0,     "schedule"),
    ("announce_text",           "ANNOUNCE_TEXT",           "公告内容(支持 {date}=当天日期)", "text", 0, 0,   "schedule"),
    ("sep_ad_botmsg",           None,                       "① 机器人自身消息自动回收(秒,0=不删)", "sep", 0, 0, "autodel"),
    ("panel_delete_seconds",    "PANEL_DELETE_SECONDS",    "游戏卡片/下注面板删除(秒,0=不删)", "int", 0, 86400, "autodel"),
    ("points_delete_seconds",   "POINTS_DELETE_SECONDS",   "你发的命令消息删除(秒,0=不删)", "int", 0, 86400, "autodel"),
    ("reply_delete_seconds",    "REPLY_DELETE_SECONDS",    "查询类回复删除(秒,0=不删)", "int", 0, 86400, "autodel"),
    ("settle_delete_seconds",   "SETTLE_DELETE_SECONDS",   "游戏结算消息删除(秒,0=不删)", "int", 0, 86400, "autodel"),
    ("race_notice_delete_seconds", "RACE_NOTICE_DELETE_SECONDS", "赛车倒计时提示删除(秒,0=不删)", "int", 0, 86400, "autodel"),
    ("web_base_url",            "WEB_BASE_URL",            "后台公网地址(/后台一键登录用)",          "text", 0,   0,    "general"),
    ("observe_enabled",         "OBSERVE_ENABLED",         "新成员观察期开关(入群未满时长禁言)", "bool", 0, 1, "members/join"),
    ("observe_seconds",         "OBSERVE_SECONDS",         "新成员观察期时长(秒,0=不限制)", "int", 0, 86400, "members/join"),
    ("sep_ad_spam",             None,                       "② 刷屏识别（复读/定时脚本）", "sep", 0, 0, "autodel"),
    ("antispam_enabled",        "ANTISPAM_ENABLED",        "定时刷屏识别开关(复读+定时器特征)", "bool", 0,   1,    "autodel"),
    ("antispam_repeat_n",       "ANTISPAM_REPEAT_N",       "复读命中条数(窗口内同内容)", "int",  2,   10,   "autodel"),
    ("antispam_window",         "ANTISPAM_WINDOW",         "复读检测窗口(秒)", "int",  10,  3600, "autodel"),
    ("antispam_timer_n",        "ANTISPAM_TIMER_N",        "定时器特征最少累计条数", "int",  3,   20,   "autodel"),
    ("antispam_timer_tol",      "ANTISPAM_TIMER_TOL",      "定时器间隔偏差容忍(%)", "int",  5,   90,   "autodel"),
    ("antispam_mute_seconds",   "ANTISPAM_MUTE_SECONDS",   "命中禁言基础时长(秒,0=只删不禁)", "int",  0,   86400,"autodel"),
    ("antispam_mute_escalate",  "ANTISPAM_MUTE_ESCALATE",  "累犯禁言翻倍", "bool", 0,   1,    "autodel"),
    ("antispam_notice_seconds", "ANTISPAM_NOTICE_SECONDS", "刷屏命中通告删除(秒,0=不删)", "int", 0, 86400, "autodel"),
    # ===== 内容规则（合并后的两个多选，替代原先 12 个单开关） =====
    ("sep_ad_rule", None, "③ 内容规则（勾选即删，管理员豁免）", "sep", 0, 0, "autodel"),
    ("autodel_text_rules",     "AUTODEL_TEXT_RULES",     "文本类规则",          "multi", 0, 0, "autodel"),
    ("autodel_long_len",       "AUTODEL_LONG_LEN",       "超长消息长度阈值(选了「超长」才生效)", "int", 50, 4096, "autodel"),
    ("autodel_text_seconds",   "AUTODEL_TEXT_SECONDS",   "文本类删除延迟(秒,0=立即删)", "int", 0, 86400, "autodel"),
    ("autodel_media_types",    "AUTODEL_MEDIA_TYPES",    "媒体/系统类规则",     "multi", 0, 0, "autodel"),
    ("autodel_media_seconds",  "AUTODEL_MEDIA_SECONDS",  "媒体类删除延迟(秒,0=立即删)", "int", 0, 86400, "autodel"),
    # ===== 群管中心（新功能全部默认关闭，网页手动开启） =====
    ("sep_mod_verify",        None, "入群验证（新人点按钮才放行）", "sep", 0, 0, "mod"),
    ("join_verify_enabled",   "JOIN_VERIFY_ENABLED",   "入群验证开关",            "bool", 0, 1, "mod"),
    ("join_verify_seconds",   "JOIN_VERIFY_SECONDS",   "验证超时(秒)",            "int",  10, 3600, "mod"),
    ("join_verify_action",    "JOIN_VERIFY_ACTION",    "超时处理(0=只提醒 1=禁言 2=踢出 3=封禁)", "int", 0, 3, "mod"),
    ("join_verify_mode",      "JOIN_VERIFY_MODE",      "验证方式(0=按钮选答案 1=图片算术 2=一键通过)", "int", 0, 2, "mod"),
    ("join_verify_max_wrong", "JOIN_VERIFY_MAX_WRONG", "验证答错N次按超时档处理(0=不限)", "int", 0, 20, "mod"),
    ("join_verify_msg",       "JOIN_VERIFY_MSG",       "验证提示({name} {seconds})", "text", 0, 0, "mod"),
    ("join_verify_ok_msg",    "JOIN_VERIFY_OK_MSG",    "验证通过提示({name})",    "text", 0, 0, "mod"),
    ("sep_mod_word",          None, "② 敏感词与域名白名单", "sep", 0, 0, "mod"),
    ("sensitive_enabled",     "SENSITIVE_ENABLED",     "敏感词过滤开关",          "bool", 0, 1, "mod"),
    ("sensitive_words",       "SENSITIVE_WORDS",       "敏感词(逗号分隔；/正则/ 形式支持正则)", "names", 0, 0, "mod"),
    ("sensitive_action",      "SENSITIVE_ACTION",      "命中处理(0=删除 1=删+禁言 2=删+踢出)", "int", 0, 2, "mod"),
    ("sensitive_mute_seconds", "SENSITIVE_MUTE_SECONDS", "敏感词禁言时长(秒)",    "int",  0, 86400, "mod"),
    ("link_whitelist_enabled", "LINK_WHITELIST_ENABLED", "域名白名单开关(名单内链接不删)", "bool", 0, 1, "mod"),
    ("link_whitelist",        "LINK_WHITELIST",        "白名单域名(逗号分隔，子域名自动放行)", "names", 0, 0, "mod"),
    ("sep_mod_observe",       None, "观察期到期巡检（须先开观察期：群组管理→入群与观察，否则本段不生效）", "sep", 0, 0, "mod"),
    ("observe_check_enabled", "OBSERVE_CHECK_ENABLED", "到期巡检开关(需先开观察期)", "bool", 0, 1, "mod"),
    ("observe_check_msgs",    "OBSERVE_CHECK_MSGS",    "发言少于N条视为不活跃",   "int",  0, 1000, "mod"),
    ("observe_check_avatar",  "OBSERVE_CHECK_AVATAR",  "无头像也算不活跃(查API，仅零发言者)", "bool", 0, 1, "mod"),
    ("observe_check_action",  "OBSERVE_CHECK_ACTION",  "处理方式(0=提醒管理员 1=禁言 2=踢出)", "int", 0, 2, "mod"),
    ("sep_mod_gate",          None, "进群硬门槛（不满足直接移出，不进验证流程）", "sep", 0, 0, "mod"),
    ("join_gate_username",    "JOIN_GATE_USERNAME",    "须有用户名",              "bool", 0, 1, "mod"),
    ("join_gate_premium",     "JOIN_GATE_PREMIUM",     "须 Telegram Premium",     "bool", 0, 1, "mod"),
    ("join_gate_bio",         "JOIN_GATE_BIO",         "须有简介(需查API，失败放行)", "bool", 0, 1, "mod"),
    ("sep_mod_lurker",        None, "潜水号清理（老成员长期不冒泡）", "sep", 0, 0, "mod"),
    ("lurker_enabled",        "LURKER_ENABLED",        "潜水清理开关",            "bool", 0, 1, "mod"),
    ("lurker_days",           "LURKER_DAYS",           "入群超过N天才纳入扫描",    "int",  1, 365, "mod"),
    ("lurker_msgs",           "LURKER_MSGS",           "累计发言少于N条视为潜水",  "int",  0, 1000, "mod"),
    ("lurker_action",         "LURKER_ACTION",         "处理方式(0=提醒管理员 1=禁言 2=踢出)", "int", 0, 2, "mod"),
    ("sep_mod_raid",          None, "防突袭（短时间大量进群自动人墙）", "sep", 0, 0, "mod"),
    ("raid_enabled",          "RAID_ENABLED",          "防突袭开关",              "bool", 0, 1, "mod"),
    ("raid_window",           "RAID_WINDOW",           "检测窗口(秒)",            "int",  10, 600, "mod"),
    ("raid_threshold",        "RAID_THRESHOLD",        "窗口内N人进群视为突袭",    "int",  3, 50, "mod"),
    ("raid_cooldown",         "RAID_COOLDOWN",         "人墙持续秒数(到期自动解除)", "int", 60, 86400, "mod"),
    ("sep_mod_forcesub",      None, "强制订阅频道（未订阅者发言即删+提示，管理员豁免）", "sep", 0, 0, "mod"),
    ("force_sub_enabled",     "FORCE_SUB_ENABLED",     "强制订阅开关",            "bool", 0, 1, "mod"),
    ("force_sub_channels",    "FORCE_SUB_CHANNELS",    "须订阅的频道(@用户名 或 -100xxx频道id，逗号分隔，订阅其一即可；私有频道请填id，邀请链接检测不了)", "names", 0, 0, "mod"),
    ("force_sub_only_new",    "FORCE_SUB_ONLY_NEW",    "只检测新用户(入群10分钟内)", "bool", 0, 1, "mod"),
    ("force_sub_warn_seconds","FORCE_SUB_WARN_SECONDS","提示自动删除(秒,0=不删)",  "int",  0, 3600, "mod"),
    ("force_sub_warn_tpl",    "FORCE_SUB_WARN_TPL",    "订阅提示({name} {channels} {seconds})", "text", 0, 0, "mod"),
    ("welcome_enabled",         "WELCOME_ENABLED",         "入群欢迎开关",              "bool",  0,   1,       "members/join"),
    ("welcome_tpl",             "WELCOME_TPL",             "入群欢迎消息(支持 {name} {group} {id})", "text", 0, 0, "members/join"),
    ("emergency_chips",         "EMERGENCY_CHIPS",         "归零赠送积分",              "int",   0,   100000,  "general"),
    ("emergency_max_uses",      "EMERGENCY_MAX_USES",      "归零每日赠送次数",          "int",   0,   99,      "general"),
    ("emergency_min_games",     "EMERGENCY_MIN_GAMES",     "归零赠送要求累计玩过局数(0=不限)", "int", 0, 9999, "general"),
    ("season_start_chips",      "SEASON_START_CHIPS",      "每人起始分",                "int",   100, 1000000, "season"),
    ("season_min_players",      "SEASON_MIN_PLAYERS",      "最少开赛人数",              "int",   2,   50,      "season"),
    ("season_min_games",        "SEASON_MIN_GAMES",        "结算最少局数",              "int",   0,   999,     "season"),
    ("season_days",             "SEASON_DAYS",             "赛季天数",                  "int",   1,   90,      "season"),
    ("season_rebuy_count",      "SEASON_REBUY_COUNT",      "每日重买次数上限",          "int",   0,   20,      "season"),
    ("season_rebuy_amount",     "SEASON_REBUY_AMOUNT",     "每次重买金额",              "int",   0,   1000000, "season"),
    # ===== 排位赛德州独立参数（0=沿用日常德州设置；填非 0 值即排位局专用） =====
    ("sep_season_texas",        None, "排位赛德州规则（留空/0 = 沿用日常德州；填了就是排位局专用）", "sep", 0, 0, "season"),
    ("season_min_entry_chips",  "SEASON_MIN_ENTRY_CHIPS",  "入座最低排位分(0=只要>0即可)", "int", 0, 1000000, "season"),
    ("season_fixed_min_raise",  "SEASON_FIXED_MIN_RAISE",  "最低加注额(0=沿用日常)",     "int",   0,  100000, "season"),
    ("season_turn_timeout",     "SEASON_TURN_TIMEOUT",     "单回合思考时间(秒,0=沿用日常)", "int", 0, 600,   "season"),
    ("season_room_wait_timeout","SEASON_ROOM_WAIT_TIMEOUT","等待房倒计时(秒,0=沿用日常)", "int",  0,  600,   "season"),
    ("season_small_blind",      "SEASON_SMALL_BLIND",      "德州小盲注(0=沿用日常)",     "int",   0,  100000, "season"),
    ("season_big_blind",        "SEASON_BIG_BLIND",        "德州大盲注(0=沿用日常)",     "int",   0,  100000, "season"),
    ("season_ante",             "SEASON_ANTE",             "德州前注(0=沿用日常)",       "int",   0,  100000, "season"),
    # ===== 聊天积分兑换排位分（比例可调，默认 1:1） =====
    ("sep_season_exchange",     None, "聊天积分兑换排位分", "sep", 0, 0, "season"),
    ("ranked_exchange_enabled", "RANKED_EXCHANGE_ENABLED", "兑换开关",                  "bool",  0,   1,       "season"),
    ("ranked_exchange_cost",    "RANKED_EXCHANGE_COST",    "兑换比例·消耗聊天积分",      "int",   1,   1000000, "season"),
    ("ranked_exchange_gain",    "RANKED_EXCHANGE_GAIN",    "兑换比例·得到排位分",        "int",   1,   1000000, "season"),
    ("ranked_exchange_daily_limit","RANKED_EXCHANGE_DAILY_LIMIT","每人每日兑换上限(按消耗积分算,0=不限)", "int", 0, 10000000, "season"),
    # ---------- 积分系统（子页面制：points/子页键，照阿福模板） ----------
    ("admin_adjust",            "ADMIN_ADJUST_ENABLED",    "管理员可增减积分",          "bool",  0,   1,       "points/set"),
    ("rank_1_emoji",            "RANK_1_EMOJI",            "积分排行第一名表情",        "short", 0,   0,       "points/set"),
    ("rank_2_emoji",            "RANK_2_EMOJI",            "积分排行第二名表情",        "short", 0,   0,       "points/set"),
    ("rank_3_emoji",            "RANK_3_EMOJI",            "积分排行第三名表情",        "short", 0,   0,       "points/set"),
    ("add_msg_tpl",             "ADD_MSG_TPL",             "添加积分提示消息",          "text",  0,   0,       "points/set"),
    ("query_msg_tpl",           "QUERY_MSG_TPL",           "查询积分消息",              "text",  0,   0,       "points/set"),
    ("chat_enabled",            "CHAT_ENABLED",            "聊天积分开关(需关机器人隐私模式)", "bool", 0, 1,    "points/set"),
    ("chat_chars_per",          "CHAT_CHARS_PER",          "每满N个字符记分",           "int",   1,   200,     "points/set"),
    ("chat_reward",             "CHAT_REWARD",             "每满N字符记几分",           "int",   1,   1000,    "points/set"),
    ("chat_daily_cap",          "CHAT_DAILY_CAP",          "聊天积分每日上限(0=不限)",  "int",   0,   1000000, "points/cap"),
    # ===== 有效发言判定（2026-09-09 用户规则：正常讨论才计分） =====
    ("chat_min_len",            "CHAT_MIN_LEN",            "有效发言最少字数(低于不计分)", "int", 1, 200, "points/cap"),
    ("chat_junk_words",         "CHAT_JUNK_WORDS",         "无意义词(纯这些词的消息不计分)", "names", 0, 0, "points/cap"),
    ("chat_dup_n",              "CHAT_DUP_N",              "窗口内同内容达N条不计分(0=不查重)", "int", 0, 20, "points/cap"),
    ("chat_dup_window",         "CHAT_DUP_WINDOW",         "重复内容判定窗口(秒)",      "int",   10,  86400,   "points/cap"),
    ("sign_enabled",            "SIGN_ENABLED",            "每日签到开关",              "bool",  0,   1,       "points/sign"),
    ("sign_base_reward",        "SIGN_BASE_REWARD",        "签到基础奖励",              "int",   0,   1000000, "points/sign"),
    ("sign_streak_bonus",       "SIGN_STREAK_BONUS",       "连续签到满7天额外奖励",     "int",   0,   1000000, "points/sign"),
    ("sign_msg_tpl",            "SIGN_MSG_TPL",            "签到成功消息",              "text",  0,   0,       "points/sign"),
    ("redpacket_enabled",       "REDPACKET_ENABLED",       "积分红包开关",              "bool",  0,   1,       "points/rp"),
    ("redpacket_exclusive_enabled","RP_EXCLUSIVE_ENABLED", "专属红包开关(回复/ID指定)", "bool",  0,   1,       "points/rp"),
    ("redpacket_luck_enabled",  "RP_LUCK_ENABLED",         "拼手气红包开关(0=平均分)",  "bool",  0,   1,       "points/rp"),
    ("redpacket_log_enabled",   "RP_LOG_ENABLED",          "抢完公布手气排行",          "bool",  0,   1,       "points/rp"),
    ("rp_msg_grab",             "RP_MSG_GRAB",             "抢红包成功提示",            "text",  0,   0,       "points/rp"),
    ("rp_msg_none",             "RP_MSG_NONE",             "未抢到红包提示",            "text",  0,   0,       "points/rp"),
    ("rp_msg_dup",              "RP_MSG_DUP",              "已抢过提示",                "text",  0,   0,       "points/rp"),
    ("rp_msg_poor",             "RP_MSG_POOR",             "发红包积分不足提示",        "text",  0,   0,       "points/rp"),
    ("rp_msg_target",           "RP_MSG_TARGET",           "专属红包非目标提示",        "text",  0,   0,       "points/rp"),
    ("rp_msg_log",              "RP_MSG_LOG",              "拼手气日志(每行,{rank}=名次)", "text", 0, 0,       "points/rp"),
    ("level_notify_enabled",    "LEVEL_NOTIFY_ENABLED",    "用户升级通知开关",          "bool",  0,   1,       "points/level"),
    ("level_enabled",           "LEVEL_ENABLED",           "积分等级系统开关",          "bool",  0,   1,       "points/level"),
    ("level_allow_demote",      "LEVEL_ALLOW_DEMOTE",      "积分不足是否允许降级",      "bool",  0,   1,       "points/level"),
    ("level_sync_tag",          "LEVEL_SYNC_TAG",          "积分称号同步成员标签开关",  "bool",  0,   1,       "points/level"),
    ("level_up_msg_tpl",        "LEVEL_UP_MSG_TPL",        "用户升级通知",              "text",  0,   0,       "points/level"),
    ("level_down_notify_enabled", "LEVEL_DOWN_NOTIFY_ENABLED", "用户降级通知开关",      "bool",  0,   1,       "points/level"),
    ("level_down_msg_tpl",      "LEVEL_DOWN_MSG_TPL",      "用户降级通知",              "text",  0,   0,       "points/level"),
    ("level_query_msg_tpl",     "LEVEL_QUERY_MSG_TPL",     "用户查询等级消息",          "text",  0,   0,       "points/level"),
    ("level_query_none_tpl",    "LEVEL_QUERY_NONE_TPL",    "用户查询等级无规则提示",    "text",  0,   0,       "points/level"),
    ("point_levels",            "POINT_LEVELS",            "积分等级表",               "levels", 0, 0,      "points/level_hidden"),
    ("level_msg_guard_enabled", "LEVEL_MSG_GUARD_ENABLED", "积分等级权限(等级消息管控)","bool",  0,   1,       "points/levelguard"),
    ("level_msg_warn_tpl",      "LEVEL_MSG_WARN_TPL",      "等级消息违规提示",          "text",  0,   0,       "points/levelguard"),
    ("level_msg_window",        "LEVEL_MSG_WINDOW",        "违规窗口时间(秒)",          "int",   1,   3600,    "points/levelguard"),
    ("level_msg_max_hits",      "LEVEL_MSG_MAX_HITS",      "窗口违规次数",              "int",   1,   100,     "points/levelguard"),
    ("level_msg_punish",        "LEVEL_MSG_PUNISH",        "频繁违规惩罚类型(0=只提醒 1=禁言 2=踢出)", "int", 0, 2, "points/levelguard"),
    ("level_msg_mute_seconds",  "LEVEL_MSG_MUTE_SECONDS",  "违规后禁言(秒 0不禁言 小于30秒永久)", "int", 0, 86400, "points/levelguard"),
    ("level_msg_mute_tpl",      "LEVEL_MSG_MUTE_TPL",      "禁言提示消息",              "text",  0,   0,       "points/levelguard"),
    ("mall_items",              "MALL_ITEMS",              "商城商品表",               "items", 0, 0,       "points/mall_hidden"),
    ("mall_enabled",            "MALL_ENABLED",            "开启积分商城",              "bool",  0,   1,       "points/mall"),
    ("mall_page_size",          "MALL_PAGE_SIZE",          "商城列表每页商品数",        "int",   1,   50,      "points/mall"),
    ("mall_msg_buy",            "MALL_MSG_BUY",            "兑换成功消息",              "text",  0,   0,       "points/mall"),
    ("mall_msg_empty",          "MALL_MSG_EMPTY",          "无商品提示消息",            "text",  0,   0,       "points/mall"),
    ("mall_min_age_days",       "MALL_MIN_AGE_DAYS",       "兑换门槛-使用满N天(0=不限,防小号)", "int", 0, 365, "points/mall"),
    ("mall_min_active_days",    "MALL_MIN_ACTIVE_DAYS",    "兑换门槛-游戏活跃天数≥N(0=不限)", "int", 0, 365,   "points/mall"),
    ("inherit_enabled",         "INHERIT_ENABLED",         "积分转赠(继承)开关",        "bool",  0,   1,       "points/inherit"),
    ("inherit_msg_ok",          "INHERIT_MSG_OK",          "转赠成功消息",              "text",  0,   0,       "points/inherit"),
    ("inherit_daily_limit",     "INHERIT_DAILY_LIMIT",     "每日转赠上限(0=不限,防小号)", "int",  0,   1000000, "points/inherit"),
    ("fund_flow_alert",         "FUND_FLOW_ALERT",         "资金流标红阈值(单对单向累计)", "int",  100, 10000000,"admin/fundflow"),
    ("inherit_fee_percent",     "INHERIT_FEE_PERCENT",     "转赠手续费(%,0=无)",        "int",   0,   50,      "points/inherit"),
    ("guess_enabled",           "GUESS_ENABLED",           "积分竞猜开关",              "bool",  0,   1,       "points/guess"),
    ("guess_min_bet",           "GUESS_MIN_BET",           "竞猜单注下限(积分)",        "int",   1,   100000,  "points/guess"),
    ("guess_max_bet",           "GUESS_MAX_BET",           "竞猜单注上限(积分,0=不限)", "int",   0,   1000000, "points/guess"),
    ("guess_duration",          "GUESS_DURATION",          "竞猜下注时长(分钟)",        "int",   1,   1440,    "points/guess"),
    # 群组抽奖（基础版：1 个 prize+count 形式；点数抽奖/乐透等高级类型后续按需扩展）
    ("lottery_enabled",         "LOTTERY_ENABLED",         "群组抽奖总开关",            "bool",  0,   1,       "lottery"),
    ("lottery_keyword",         "LOTTERY_KEYWORD",         "参与触发词(也支持 /开奖)",   "short", 0,   0,       "lottery"),
    ("lottery_default_duration","LOTTERY_DEFAULT_DURATION","倒计时默认时长(秒)",          "int",   10,  3600,    "lottery"),
    ("lottery_fee",             "LOTTERY_FEE",             "参与扣积分(0=免费)",         "int",   0,   10000,   "lottery"),
    ("lottery_msg_start",       "LOTTERY_MSG_START",       "活动公告模板",              "text", 0,   0,       "lottery"),
    ("lottery_msg_joined",      "LOTTERY_MSG_JOINED",      "参与成功模板",              "text", 0,   0,       "lottery"),
    ("lottery_msg_dup",         "LOTTERY_MSG_DUP",         "重复参与模板",              "text", 0,   0,       "lottery"),
    ("lottery_msg_fail",        "LOTTERY_MSG_FAIL",        "参与失败模板(余额不足等)",  "text", 0,   0,       "lottery"),
    ("lottery_msg_result",      "LOTTERY_MSG_RESULT",      "开奖结果模板",              "text", 0,   0,       "lottery"),
    ("buy_enabled",             "BUY_ENABLED",             "购买积分开关(管理员人工确认)", "bool", 0, 1,     "points/buy"),
    ("buy_min",                 "BUY_MIN",                 "单次最低购买数量",          "int",   100, 1000000, "points/buy"),
    ("buy_max",                 "BUY_MAX",                 "单次最高购买数量",          "int",   100, 10000000,"points/buy"),
    ("redeem_max_per_user",     "REDEEM_MAX_PER_USER",     "每人最大兑换数量(0=不限)",  "int",   0,   9999,    "points/redeem"),
    ("redeem_start",            "REDEEM_START",            "兑换开始时间(YYYY-MM-DD HH:MM,留空不限)", "short", 0, 0, "points/redeem"),
    ("redeem_end",              "REDEEM_END",              "兑换结束时间(同上,留空不限)", "short", 0,  0,       "points/redeem"),
    ("redeem_msg_list",         "REDEEM_MSG_LIST",         "兑换商品行模板",            "text",  0,   0,       "points/redeem"),
    ("redeem_msg_ok_group",     "REDEEM_MSG_OK_GROUP",     "兑换成功群通知",            "text",  0,   0,       "points/redeem"),
    ("redeem_msg_ok_dm",        "REDEEM_MSG_OK_DM",        "兑换成功私聊通知",          "text",  0,   0,       "points/redeem"),
    # ---------- 邀请系统（群组设置 → 邀请系统，子页面制照阿福模板） ----------
    ("invite_enabled",          "INVITE_ENABLED",          "邀请系统开关",              "bool",  0,   1,       "invite/config"),
    ("invite_notify",           "INVITE_NOTIFY",           "邀请人私聊通知开关",        "bool",  0,   1,       "invite/config"),
    ("invite_reward",           "INVITE_REWARD",           "邀请奖励(积分/合格1人)",     "int",   0,   1000000, "invite/config"),
    ("invite_reward_times",     "INVITE_REWARD_TIMES",     "每人最多发放奖励次数",      "int",   1,   10000,   "invite/config"),
    ("invite_daily_cap_times",  "INVITE_DAILY_CAP_TIMES",  "每人每日拉新人数上限(0=不限)", "int", 0,   1000,    "invite/config"),
    ("invite_daily_cap_points", "INVITE_DAILY_CAP_POINTS", "每人每日拉新积分上限(0=不限)", "int", 0,   1000000, "invite/config"),
    ("newbie_reward_enabled",   "NEWBIE_REWARD_ENABLED",   "新人欢迎奖励开关(首次发言发)", "bool", 0, 1,      "invite/config"),
    ("newbie_reward",           "NEWBIE_REWARD",           "新人欢迎奖励积分",          "int",   0,   1000000, "invite/config"),
    ("invite_rank_admin_only",  "INVITE_RANK_ADMIN_ONLY",  "排行仅管理员可查开关",      "bool",  0,   1,       "invite/config"),
    # （2026-09-08 去重移除：今日/本月/总邀请排行指令三字段与「命令管理」页重复，
    #   触发词改由别名层统一管理：今日邀请排行/本月邀请排行/总邀请排行 照常可用）
    ("invite_ok_group",         "INVITE_OK_GROUP",         "邀请成功群内通知模板",      "text",  0,   0,       "invite/config"),
    ("invite_rank_today_msg",   "INVITE_RANK_TODAY_MSG",   "今日邀请排行标题模板",      "text",  0,   0,       "invite/config"),
    ("invite_rank_month_msg",   "INVITE_RANK_MONTH_MSG",   "本月邀请排行标题模板",      "text",  0,   0,       "invite/config"),
    ("invite_rank_all_msg",     "INVITE_RANK_ALL_MSG",     "总邀请排行标题模板",        "text",  0,   0,       "invite/config"),
    ("invite_rank_line_fmt",    "INVITE_RANK_LINE_FMT",    "排行行格式模板",            "text",  0,   0,       "invite/config"),
    ("invite_invalid_msg",      "INVITE_INVALID_MSG",      "无效邀请链接消息",          "text",  0,   0,       "invite/config"),
    ("invite_self_msg",         "INVITE_SELF_MSG",         "自己邀请自己消息",          "text",  0,   0,       "invite/config"),
    # 合格邀请结算（2026-09-08 替代旧「进群前置」死字段）：被邀请人本群达标才算合格才发奖
    ("invite_qualify_enabled",  "INVITE_QUALIFY_ENABLED",  "合格结算开关(达标才发奖)",   "bool",  0,   1,       "invite/qualify"),
    ("invite_manual_count",     "INVITE_MANUAL_COUNT",     "手动拉人计入邀请(添加人=邀请人)", "bool", 0, 1,  "invite/qualify"),
    ("invite_auto_approve",     "INVITE_AUTO_APPROVE",     "带链接申请自动批准(确认制归因不受此限)", "bool", 0, 1,  "invite/qualify"),
    ("invite_qualify_msgs",     "INVITE_QUALIFY_MSGS",     "质量要求-本群发言≥N条(0=不限)", "int", 0,  100000,  "invite/qualify"),
    ("invite_qualify_points",   "INVITE_QUALIFY_POINTS",   "质量要求-本群净赚积分≥M(0=不限)", "int", 0, 1000000, "invite/qualify"),
    ("invite_qualify_avatar",   "INVITE_QUALIFY_AVATAR",   "质量要求-进群须有头像(无则拒)", "bool", 0,   1,      "invite/qualify"),
    ("invite_qualify_username", "INVITE_QUALIFY_USERNAME", "质量要求-进群须有用户名(无则拒)","bool",0,   1,      "invite/qualify"),
]
# settings键 -> 模块全局变量名（群级读写与网页渲染共用）
_KEY2VAR = {f[0]: f[1] for f in SETTINGS_FIELDS if f[1]}
# 全站唯一、按群覆盖无意义的键（网页密码/备份接收人/调度作用对象/公网地址/功能开关类）
_GROUP_NEVER = {
    "web_base_url", "backup_interval_hours", "backup_enabled",
    "admin_report_time", "admin_report_enabled", "announce_enabled", "announce_time", "announce_text",
    "daily_reset_time", "daily_reset_enabled", "leaderboard_time", "leaderboard_enabled",
    "race_hourly_minute", "race_auto_enabled", "race_hourly_start", "race_hourly_end",
    "stale_text_command_seconds", "broadcast_enabled", "broadcast_min_amount",
    "admin_adjust", "fund_flow_alert",
    "rank_1_emoji", "rank_2_emoji", "rank_3_emoji",
}
_settings_lock = threading.Lock()
_web_password = WEB_DEFAULT_PASSWORD  # 运行时明文（仅内存，落盘绝不写它）；改密后由 hash 接管校验
_web_password_hash = ""  # pbkdf2-sha256 hex：真正落盘/进备份的凭据（拿到备份也还原不出密码）
_web_salt = ""           # 上面 hash 配套的盐

# ---------- 群级设置覆盖（2026-09-10 用户诉求：后台按群切设置） ----------
# 结构：{cid(int): {settings键: 值}}。语义 = **只存差异**：某群没覆盖的键，读取时继承全局默认。
# 因此改全局默认，所有没覆盖该项的群自动跟着变；群级只放"这个群特意要不一样"的值。
# 用 group_get(cid, key) 读取，永远不要直接 globals()[GNAME]——那样会绕过群级覆盖。
GROUP_SETTINGS = {}

# 哪些设置键支持群级覆盖（= 与具体群玩法/策略相关的键）。
# 刻意排除的：网页密码、备份接收人、调度作用对象、web_base_url 等"全站唯一"的键——
# 它们按群覆盖没有意义，反而会让管理员困惑。
# 具体清单在 SETTINGS_FIELDS 之后填充（需先有字段表才能推导）。
GROUP_SCOPED_KEYS = set()
GROUP_SCOPED_KEYS.update(
    f[0] for f in SETTINGS_FIELDS
    if f[1] and f[3] not in ("sep", "levels", "items", "cmd") and f[0] not in _GROUP_NEVER
)
# 排除理由：
#   sep   = 分组标题行，不是真设置
#   levels/items = 积分等级表 / 商城表（全站共享的数据表，按群覆盖会让"等级"概念崩掉）
#   cmd   = 自定义指令名（Telegram 命令是全 Bot 唯一，做不到按群）
# 其余（数字/开关/多选/话术模板/表情/词表/下注档位）全部支持按群覆盖。

def group_get(cid, key, default=None):
    """读设置项：该群有覆盖用覆盖值，否则用全局默认。

    cid 为 0/None/非法 → 直接走全局（全局页与所有旧调用点零影响）。
    key 不在 GROUP_SCOPED_KEYS 里 → 也走全局（不支持的键不参与群级覆盖）。
    """
    gname = _KEY2VAR.get(key)
    if gname is None:
        return default
    try:
        cid = int(cid or 0)
    except (TypeError, ValueError):
        cid = 0
    if cid and key in GROUP_SCOPED_KEYS:
        rec = GROUP_SETTINGS.get(cid) or {}
        if key in rec:
            return rec[key]
    return globals().get(gname, default)

def group_set(cid, key, value):
    """写群级覆盖。value=None 表示**清除覆盖**（回继承全局）。返回 True=写入成功。"""
    gname = _KEY2VAR.get(key)
    if gname is None:
        return False
    try:
        cid = int(cid or 0)
    except (TypeError, ValueError):
        return False
    if not cid or key not in GROUP_SCOPED_KEYS:
        return False
    if value is None:
        rec = GROUP_SETTINGS.get(cid)
        if rec:
            rec.pop(key, None)
            if not rec:
                GROUP_SETTINGS.pop(cid, None)
        return True
    GROUP_SETTINGS.setdefault(cid, {})[key] = value
    return True

def group_effective(cid, key, default=None):
    """该群当前生效值 + 是否来自群级覆盖。返回 (值, 是否覆盖)。网页回显用。"""
    try:
        cid = int(cid or 0)
    except (TypeError, ValueError):
        cid = 0
    if cid and key in GROUP_SCOPED_KEYS and key in (GROUP_SETTINGS.get(cid) or {}):
        return GROUP_SETTINGS[cid][key], True
    return group_get(cid, key, default), False

# ---------- 当前群上下文（contextvars）：业务读取点零改动拿到群级值 ----------
# 设计要点：业务代码里 500+ 处直接读模块全局（如 BJ_MIN_BET），不可能逐个改签名传 cid。
# 改用「上下文变量」承载"这条消息属于哪个群"，再让统一读取入口 sget() 按上下文解析：
#   - 处理某群更新时（handler / 定时任务 / 网页请求）set 一次 cid，整条调用链自动生效；
#   - 没 set（启动初始化、跨群聚合、私聊命令）→ cid=0 → 读全局默认，**行为与改前逐字节一致**。
# 这是「零回归」的关键：GROUP_SETTINGS 为空时 sget("X") 恒等于裸全局 X。
_CUR_CID = contextvars.ContextVar("cur_cid", default=0)
_VAR2KEY = {f[1]: f[0] for f in SETTINGS_FIELDS if f[1]}   # 全局变量名 -> settings键
_MISS = object()

def cur_cid():
    """当前上下文群 ID（0=无群上下文，走全局默认）。"""
    try:
        return int(_CUR_CID.get() or 0)
    except (TypeError, ValueError):
        return 0

@asynccontextmanager
async def group_ctx_async(cid):
    tok = _CUR_CID.set(_safe_cid(cid))
    try: yield
    finally: _CUR_CID.reset(tok)

class group_ctx:
    """同步上下文管理器：with group_ctx(cid): ... 期间 sget() 按该群解析。

    用于定时任务按群循环、网页请求渲染等**同步**场景。
    """
    __slots__ = ("_cid", "_tok")

    def __init__(self, cid):
        self._cid = _safe_cid(cid)

    def __enter__(self):
        self._tok = _CUR_CID.set(self._cid)
        return self._cid

    def __exit__(self, *exc):
        _CUR_CID.reset(self._tok)
        return False

def _safe_cid(cid):
    try:
        return int(cid or 0)
    except (TypeError, ValueError):
        return 0

def sget(name, default=None):
    """读设置项（**业务代码统一入口**）：name 是模块全局变量名，如 sget("BJ_MIN_BET")。

    解析顺序：当前群覆盖 → 全局默认。cid 来自 contextvars（handler/定时任务/网页请求会设）。
    GROUP_SETTINGS 为空或该群没覆盖该键时，返回值与直接读全局变量完全一致。
    """
    cid = cur_cid()
    if cid:
        key = _VAR2KEY.get(name)
        if key is not None:
            rec = GROUP_SETTINGS.get(cid)
            if rec:
                v = rec.get(key, _MISS)
                if v is not _MISS:
                    return v
    return globals().get(name, default)

def sget_key(key, default=None):
    """按 settings 键读（等价 sget，键名更顺手时用）。"""
    gname = _KEY2VAR.get(key)
    if gname is None:
        return default
    return sget(gname, default)

def _bind_update_cid(update):
    """把「这条更新属于哪个群」写进上下文，让整条调用链的 sget() 自动解析群级覆盖。

    7 个更新入口（命令/回调/文本/媒体/成员变动/入群消息/入群申请）第一行调用。
    私聊、频道、无 chat 的更新 → cid=0 → 全部走全局默认（与改前一致）。
    """
    try:
        chat = update.effective_chat
        _CUR_CID.set(int(chat.id) if chat is not None else 0)
    except Exception:
        _CUR_CID.set(0)
    return cur_cid()

def _group_settings_json():
    """群级覆盖的落盘形式（json 的键必须是字符串，读回时再转 int）。"""
    return {str(cid): dict(rec) for cid, rec in GROUP_SETTINGS.items() if rec}

def _normalize_settings_values(cfg: dict):
    """按 apply_settings 的规则算出"标准值"，但**不改动**内存里的全局设置。

    用途：群级保存要拿"标准值"跟全局默认比对，才能只存差异。
    做法：先快照所有设置全局变量 → 调 apply_settings 归一化 → 立刻还原。
    只传入群级键（levels/items/cmd 已在 GROUP_SCOPED_KEYS 里排除），
    因此 _normalize_levels() 之类会原地改列表的分支不会被触发。
    """
    sub = {k: v for k, v in cfg.items() if k in GROUP_SCOPED_KEYS}
    if not sub:
        return {}
    snap = {}
    for _f in SETTINGS_FIELDS:
        _g = _f[1]
        if _g and _g not in snap:
            snap[_g] = globals().get(_g)
    try:
        return apply_settings(sub)
    finally:
        for _g, _v in snap.items():
            globals()[_g] = _v

def _hash_web_pwd(pwd, salt):
    """后台密码摘要（pbkdf2-sha256）。落盘只存它，明文只活在内存里。"""
    import hashlib
    return hashlib.pbkdf2_hmac("sha256", str(pwd).encode("utf-8"), str(salt).encode("utf-8"), 120000).hex()

def _pwd_ok(pwd):
    """校验后台登录密码：有 hash 就用 hash 比对，没有（首次/旧明文存档）才退回到明文比对。"""
    try:
        if _web_password_hash and _web_salt:
            return secrets.compare_digest(_hash_web_pwd(pwd, _web_salt), _web_password_hash)
    except Exception:
        return False
    return bool(pwd) and secrets.compare_digest(str(pwd), str(_web_password))


def _client_ip(handler):
    """⑲ 取真实客户端 IP：反代场景（Northflank ingress 等）socket 地址恒为代理 IP，
    若直接用它做登录限速键，一人试错就会锁死全部管理员。

    规则：有 X-Forwarded-For 取最后一段（ingress 在末尾追加的真实连接来源）；
    无 XFF（直连）用 socket 地址。注意：直连部署时 XFF 可被伪造绕过限速，
    本 bot 部署在 Northflank（必经 ingress），信任 XFF 是正确取舍。
    """
    try:
        xff = (handler.headers.get("X-Forwarded-For") or "").split(",")
        for seg in reversed(xff):
            seg = seg.strip()
            if seg:
                return seg
    except Exception:
        pass
    try:
        return handler.client_address[0]
    except Exception:
        return "unknown"

# ---------- 积分系统：运行时配置默认值（网页可改） ----------
SIGN_ENABLED = 1
SIGN_BASE_REWARD = 1000
SIGN_STREAK_BONUS = 500
CHAT_ENABLED = 1
CHAT_CHARS_PER = 5
CHAT_REWARD = 1
CHAT_DAILY_CAP = 500
# 有效发言判定（2026-09-09 用户规则：正常讨论才计分，无意义/重复灌水不计）
CHAT_MIN_LEN = 4            # 消息最少字数（低于此不计分）
CHAT_JUNK_WORDS = []        # 无意义词黑名单（整条消息由这些词构成则不计分）
CHAT_DUP_WINDOW = 300       # 重复内容判定窗口（秒）
CHAT_DUP_N = 2              # 窗口内同内容达到 N 条即视为灌水，不再计分
POINTS_DELETE_SECONDS = 30
REPLY_DELETE_SECONDS = 30   # 查询类命令的 bot 回复自动删除（0=不删）
SETTLE_DELETE_SECONDS = 600 # 游戏结算消息自动删除（0=不删）
PANEL_DELETE_SECONDS = 300 # 游戏卡片/下注面板：本局结束后自动删除（0=不删）
RACE_NOTICE_DELETE_SECONDS = 60  # 赛车倒计时提示自动删除（0=不删）
_pending_deletes = []      # 待删消息队列 [[cid, mid, 到期时间戳], ...]：随 bot_data 持久化，重启后重放，重部署不再残留消息
_delete_tasks = set()      # 持有删除 task 的引用：裸 create_task 不保引用可能被事件循环 GC，删除凭空消失
WEB_OTP_ENABLED = False  # 一键登录(/后台)为主，密码直登为备用；验证码步骤默认关闭（要开改这里）
WEB_BASE_URL = ""  # 后台公网地址（如 https://xxx.northflank.app），/后台 一键登录链接用；不配则该功能不可用
# ---------- 群组抽奖 ----------
LOTTERY_ENABLED = True             # 总开关（网页 general→points/lottery 可关）
LOTTERY_KEYWORD = "抽奖"            # 玩家参与的触发词（也支持 /开奖 命令）
LOTTERY_DEFAULT_DURATION = 60       # 倒计时默认时长：群内命令开抽奖不带时间时用；网页倒计时模式预填值
LOTTERY_FEE = 0                     # 参与扣积分（0=免费）；参与门槛在每场活动创建时单独设置
LOTTERY_MAX_PRIZES = 8              # 单次抽奖最多几档奖品
LOTTERY_MSG_START = (
    "🧧━━━━━━━━━━━━━━━━━\n"
    "🎉 <b>{title}</b>\n"
    "🧧━━━━━━━━━━━━━━━━━\n"
    "{desc_line}"
    "⏰ 开奖时间：<b>{end_line}</b>\n"
    "🎁 奖品：\n{prize_list}\n"
    "{min_line}{fee_line}👥 已参与 <b>{n}</b> 人\n"
    "💬 发送 <code>{keyword}</code> 或 /抽奖 立即参与"
)
LOTTERY_MSG_JOINED = "✅ {nick} 参与成功！你是第 <b>{n}</b> 位参与者\n💰 余额：<b>{balance}</b>"
LOTTERY_MSG_DUP = "⚠️ {nick} 你已经参与过啦，等开奖即可"
LOTTERY_MSG_FAIL = "❌ {nick} {reason}"
LOTTERY_MSG_RESULT = (
    "🎊━━━━━━━━━━━━━━━━━\n"
    "🎉 <b>{title}</b> · 开奖结果\n"
    "🎊━━━━━━━━━━━━━━━━━\n"
    "{winners}\n"
    "📊 共 <b>{n}</b> 人参与，中奖 <b>{w}</b> 人\n"
    "🙏 感谢参与，中奖信息永久保留"
)
OBSERVE_ENABLED = 0         # 新成员观察期开关（1=开启：入群未满时长的成员发言即删并禁言到期满）
OBSERVE_SECONDS = 300       # 观察期时长（秒）
# ===== 群管中心（mod 组）：入群验证 / 敏感词 / 域名白名单 / 观察期巡检 =====
# 全部默认关闭，网页「🛡️ 群管中心」手动开启（用户要求：新功能先关，自己开）
JOIN_VERIFY_ENABLED = 0     # 入群验证：新人进群先限制发言，点按钮才放行
JOIN_VERIFY_SECONDS = 120   # 验证超时（秒）
JOIN_VERIFY_ACTION = 0      # 超时处理：0=只提醒 1=禁言 2=踢出
JOIN_VERIFY_MSG = "👋 {name} 欢迎进群！请在 {seconds} 秒内点下方按钮完成验证，超时将按群规处理。"
JOIN_VERIFY_OK_MSG = "✅ {name} 验证通过，已解除限制，畅聊吧！"
JOIN_VERIFY_MODE = 0       # 验证方式：0=按钮选答案（题目+5个选项，点对的通过，默认）/ 1=图片算术（打字回复，未装 Pillow 降级文字算式）/ 2=一键通过
JOIN_VERIFY_MAX_WRONG = 0  # 验证答错 N 次按超时档处理（0=不限次数）
JOIN_GATE_USERNAME = 0     # 进群硬门槛：须有用户名（不满足直接移出，不进验证流程）
JOIN_GATE_PREMIUM = 0      # 进群硬门槛：须 Telegram Premium
JOIN_GATE_BIO = 0          # 进群硬门槛：须有简介（需额外查 API；查询失败宁放过不误杀）
SENSITIVE_ENABLED = 0       # 敏感词过滤
SENSITIVE_WORDS = []        # 敏感词表（明文子串，或 /正则/ 形式）
SENSITIVE_ACTION = 0        # 命中处理：0=删除 1=删除+禁言 2=删除+踢出
SENSITIVE_MUTE_SECONDS = 600
LINK_WHITELIST_ENABLED = 0  # 域名白名单：名单内链接不按「链接消息」规则删
LINK_WHITELIST = []         # 白名单域名（t.me、example.com；子域名自动放行）
OBSERVE_CHECK_ENABLED = 0   # 观察期到期巡检
OBSERVE_CHECK_MSGS = 1      # 到期时本群发言少于 N 条视为不活跃
OBSERVE_CHECK_AVATAR = 0    # 无头像也算不活跃（需额外 API 查询，仅在发言为 0 时才查）
OBSERVE_CHECK_ACTION = 0    # 0=私聊提醒管理员 1=禁言 2=踢出
join_verify_pending = {}    # "cid:uid" -> {"ts":秒级时间戳, "msg_id":验证消息ID, "mode":0/1, "a","b","wrong"}
observe_checked = set()     # 已完成观察期复核的 "cid:uid"（防重复处理）
LURKER_ENABLED = 0          # 潜水号清理：入群超 N 天且累计发言不足 → 按档处理
LURKER_DAYS = 30            # 入群超过 N 天才纳入扫描
LURKER_MSGS = 5             # 累计发言少于 N 条视为潜水
LURKER_ACTION = 0           # 0=私聊提醒管理员 1=禁言 2=踢出
lurker_checked = set()      # 已处理/已豁免的 "cid:uid"（防重复骚扰）
RAID_ENABLED = 0            # 防突袭：短时间大量进群 → 临时人墙（新人强制走验证禁言）
RAID_WINDOW = 60            # 检测窗口（秒）
RAID_THRESHOLD = 5          # 窗口内 N 人进群视为突袭
RAID_COOLDOWN = 600         # 人墙持续秒数，到期自动解除
raid_joins = {}             # cid -> [进群时间戳,...]（滑动窗口，重启清零即可）
raid_until = {}             # cid -> 人墙解除时间戳
raid_counted = {}           # "cid:uid" -> 进群时间戳（同一次进群双事件源只计一次）
FORCE_SUB_ENABLED = 0       # 强制订阅频道：未订阅者发言即删+提示（默认关，网页手动开启）
FORCE_SUB_CHANNELS = []     # 须订阅的频道（@用户名 或 -100 开头频道 id；订阅其一即可）
FORCE_SUB_ONLY_NEW = 0      # 只检测新用户（入群 10 分钟内），关=所有人
FORCE_SUB_WARN_SECONDS = 60 # 订阅提示自动删除秒数，0=不删
_fsub_ok_cache = defaultdict(dict)  # _fsub_ok_cache[cid][uid] = (判定时间, 是否已订阅)
_fsub_invite_cache = {}     # 频道id -> 邀请链接（私有频道 get_chat 结果缓存，避免每条消息打 API）
ANNOUNCE_ENABLED = 0        # 定时群公告：每天到点向全部授权群推一条
ANNOUNCE_TIME = "09:00"     # 推送时间（时:分，北京时间）
ANNOUNCE_TEXT = ""          # 公告内容（支持 {date}=当天日期）
announce_last_date = ""     # 当天已发标记（YYYY-MM-DD，重启不重发）
# ---------- 邀请系统 ----------
INVITE_ENABLED = 1          # 邀请系统总开关
INVITE_NOTIFY = 1           # 邀请成功私聊通知邀请人开关
INVITE_REWARD = 50          # 每合格 1 人奖励积分（达到质量要求才发）
INVITE_REWARD_TIMES = 10    # 单邀请人最多发放奖励次数（超额合格不再发，防白嫖）
# 每日拉新上限（2026-09-09 用户规则：单人每日最多 6 人 / 300 分，避免诱导乱拉人）
INVITE_DAILY_CAP_TIMES = 6      # 单人每日最多发放奖励的次数（0=不限）
INVITE_DAILY_CAP_POINTS = 300   # 单人每日拉新积分上限（0=不限）
# 新人欢迎奖励（2026-09-09 用户规则：新人完成入群审核 +200，帮助其有基础分）
NEWBIE_REWARD_ENABLED = 0   # 新人欢迎奖励开关
NEWBIE_REWARD = 200         # 新人首次发言奖励积分
# 归因策略（2026-09-08 二次改：申请制链接）：实测 chat_member 进群事件的 invite_link 字段
# 经常为空（直链/主链/时序都踩过），导致归因恒 0。而 chat_join_request 事件由 API 保证携带
# invite_link → /link 改发「申请制链接」（creates_join_request=True）：点链接 → 申请（带链接
# 入 invite_pending）→ 批准 → 进群 → 从 pending 精确归因。事件/申请都没带链接时仍不归因（宁缺毋滥）。
# 自动批准开关 INVITE_AUTO_APPROVE（默认 0=管理员手动批，可开 1=bot 对可归因申请自动批准）。
INVITE_LINK_CMD = "link"    # 获取专属邀请链接指令
INVITE_RANK_ADMIN_ONLY = 0  # 邀请排行仅管理员可查开关
INVITE_RANK_TODAY_CMD = "今日邀请排行"
INVITE_RANK_MONTH_CMD = "本月邀请排行"
INVITE_RANK_ALL_CMD = "总邀请排行"
# 合格邀请结算（2026-09-08 改造，替代旧「进群前置」死字段——旧逻辑人没进群查本群积分/发言，
# 新人必然 0 永远不满足=100% 死代码）：
# 机制：被邀请人经专属直链进群只记账（待达标）；在本群真实活动（发言/净赚积分）达阈值才标合格并发奖；
# 达标检查事件驱动（发言/签到/刷新按钮兜底重判）；单邀请人发放次数 ≤ INVITE_REWARD_TIMES。
INVITE_QUALIFY_ENABLED = 1   # 合格结算开关（1=达标才发奖；0=进群即发，兼容老行为）
INVITE_MANUAL_COUNT = 0      # 手动拉人计入邀请（1=管理员/成员手动添加的人记到添加人名下；默认关，防拉小号刷奖励）
INVITE_AUTO_APPROVE = 0      # 申请制链接自动批准（1=bot 自动批准携带链接的入群申请；0=管理员手动批，网页「成员/入群申请」可批）
INVITE_QUALIFY_MSGS = 10     # 质量要求：被邀请人本群累计发言 ≥ N 条（0=不限）
INVITE_QUALIFY_POINTS = 0    # 质量要求：被邀请人本群净赚积分 ≥ M（0=不限；净赚=余额-初始分）
INVITE_QUALIFY_AVATAR = 0    # 质量要求：进群须有头像（无则拒绝，永不发；防小号）
INVITE_QUALIFY_USERNAME = 0  # 质量要求：进群须有用户名（无则拒绝，永不发；防小号）
# ===== 定时刷屏识别（TG 定时消息发出后无标记，只能按行为特征抓：复读机 + 定时器节奏） =====
ANTISPAM_ENABLED = 1        # 1=开启
ANTISPAM_REPEAT_N = 3       # 复读命中：窗口内同内容第 N 条
ANTISPAM_WINDOW = 120       # 复读检测窗口（秒）
ANTISPAM_TIMER_N = 4        # 定时器特征：同内容累计至少 N 条才开始判定
ANTISPAM_TIMER_TOL = 30     # 定时器间隔偏差容忍（百分比，间隔需落在均值 ±30% 内）
ANTISPAM_MUTE_SECONDS = 3600  # 命中禁言基础时长（秒，0=只删不禁）
ANTISPAM_MUTE_ESCALATE = 1  # 累犯禁言翻倍（1h→2h→4h…）
ANTISPAM_OFFENSE_WINDOW = 7 * 86400  # 累犯计数的有效期（秒，默认 7 天）：窗口外的命中不再计入翻倍，防"历史总次数"把人变成事实永久禁言
ANTISPAM_NOTICE_SECONDS = 60  # 命中通告自动删除（秒，0=不删）
ANTISPAM_MIN_LEN = 5        # 参与统计的最短内容长度（防误伤"哈哈哈"类闲聊）
antispam_hist = {}          # (cid, uid, 内容归一化) -> [ts,...] 最多保留 12 条
antispam_offense = {}       # (cid, uid) -> [命中 ts,...] 用于累犯加重
# ===== 自动删除规则中心默认值（网页「自动删除」页可改，保存立即生效） =====
# ===== 自动删除：合并后的多选规则（旧的单开关已由 _migrate_legacy_autodel 自动换算） =====
AUTODEL_TEXT_RULES = "link,long"          # 文本类规则：link=链接 long=超长 premium_emoji=会员表情
AUTODEL_TEXT_SECONDS = 0                  # 文本类命中后延迟删除秒数（0=立即删）
AUTODEL_MEDIA_TYPES = "executable,contact,service"   # 媒体/系统类规则（见 MULTI_OPTIONS）
AUTODEL_MEDIA_SECONDS = 0                 # 媒体/系统类命中后延迟删除秒数（0=立即删）
AUTODEL_LONG_LEN = 200                    # 超长阈值（仅在选中 long 时生效）
WELCOME_ENABLED = 0         # 入群欢迎开关（1=开启）
WELCOME_TPL = "🎉 欢迎 {name} 加入本群！\n积分游戏请在群内发送 /start 查看玩法。"
REDPACKET_ENABLED = 1
POINT_LEVELS = [
    # 2026-09-09 用户截图口径：L1~L20 对应 100~20000 分
    # 权限阶梯：L1 只能文字 → L3 起可发贴纸 → L5 起可发图/视频 → L8 起可发音频
    #          → L13 起可发链接 → L18 起可转发/编辑（每级可在网页单独改）
    {"name": "L1",  "value": 100,   "perms": "text",                                          "on": 1},
    {"name": "L2",  "value": 200,   "perms": "text",                                          "on": 1},
    {"name": "L3",  "value": 350,   "perms": "text,sticker",                                  "on": 1},
    {"name": "L4",  "value": 550,   "perms": "text,sticker",                                  "on": 1},
    {"name": "L5",  "value": 800,   "perms": "text,sticker,photo,video",                      "on": 1},
    {"name": "L6",  "value": 1100,  "perms": "text,sticker,photo,video",                      "on": 1},
    {"name": "L7",  "value": 1450,  "perms": "text,sticker,photo,video",                      "on": 1},
    {"name": "L8",  "value": 1850,  "perms": "text,sticker,photo,video,audio",                "on": 1},
    {"name": "L9",  "value": 2300,  "perms": "text,sticker,photo,video,audio",                "on": 1},
    {"name": "L10", "value": 2800,  "perms": "text,sticker,photo,video,audio",                "on": 1},
    {"name": "L11", "value": 3400,  "perms": "text,sticker,photo,video,audio",                "on": 1},
    {"name": "L12", "value": 4100,  "perms": "text,sticker,photo,video,audio",                "on": 1},
    {"name": "L13", "value": 4900,  "perms": "text,sticker,photo,video,audio,link",           "on": 1},
    {"name": "L14", "value": 5800,  "perms": "text,sticker,photo,video,audio,link",           "on": 1},
    {"name": "L15", "value": 6800,  "perms": "text,sticker,photo,video,audio,link",           "on": 1},
    {"name": "L16", "value": 8000,  "perms": "text,sticker,photo,video,audio,link",           "on": 1},
    {"name": "L17", "value": 9500,  "perms": "text,sticker,photo,video,audio,link",           "on": 1},
    {"name": "L18", "value": 12000, "perms": "text,sticker,photo,video,audio,link,forward",   "on": 1},
    {"name": "L19", "value": 15000, "perms": "text,sticker,photo,video,audio,link,forward",   "on": 1},
    {"name": "L20", "value": 20000, "perms": "text,sticker,photo,video,audio,forward,link,edit", "on": 1},
]
MALL_ITEMS = []  # [{"name": 商品名, "value": 价格}]
INHERIT_ENABLED = 1
INHERIT_FEE_PERCENT = 0
GUESS_ENABLED = 1           # 积分竞猜开关
GUESS_MIN_BET = 10          # 竞猜单注下限
GUESS_MAX_BET = 0           # 竞猜单注上限（0=不限）
GUESS_DURATION = 5          # 竞猜下注时长（分钟），到点封盘等管理员结算
GUESS_AUTO_SETTLE_MINUTES = 60  # 封盘后多久仍未结算就自动撤销退款（0=永不自动）。防管理员忘记 → 玩家积分永久卡死
BUY_ENABLED = 1
BUY_MIN = 1000
BUY_MAX = 100000
REDEEM_CMD = "积分兑换"      # 积分兑换触发词
REDEEM_MAX_PER_USER = 0     # 每人最大兑换数量（0=不限）
REDEEM_START = ""           # 兑换开始时间（YYYY-MM-DD HH:MM，留空不限）
REDEEM_END = ""             # 兑换结束时间（同上，留空不限）
RP_EXCLUSIVE_ENABLED = 1    # 专属红包开关（回复/指定ID红包）
RP_LUCK_ENABLED = 1         # 1=拼手气随机拆分 0=平均分
RP_LOG_ENABLED = 1          # 抢完公布手气排行
MALL_ENABLED = 1            # 积分商城开关
MALL_PAGE_SIZE = 10         # 商城列表每页商品数
MALL_LIST_DELETE_SECONDS = 300  # 兑换/商城列表消息自动删除秒数（5 分钟；按钮要活所以不能 30 秒太短；0=不删）
LEVEL_NOTIFY_ENABLED = 1    # 等级升降群内通知开关
LEVEL_ENABLED = 1           # 积分等级系统总开关（2026-09-09 用户截图「积分等级系统开关」）
LEVEL_ALLOW_DEMOTE = 0      # 积分不足是否允许降级（用户截图，默认否）
LEVEL_SYNC_TAG = 1          # 积分称号同步成员标签开关（用户截图）
LEVEL_MSG_GUARD_ENABLED = 1 # 等级消息管控总开关（按等级限制可发的消息类型）
LEVEL_MSG_WARN_TPL = ("⚠️ {name}，你当前等级「{level}」还不能发送{kind}。\n"
                      "多发消息或参与游戏升级后即可解锁。")
LEVEL_MSG_MUTE_TPL = "🔇 {name} 因频繁发送超出等级权限的消息，已被禁言 {seconds} 秒。"
LEVEL_MSG_WINDOW = 10       # 违规窗口（秒）
LEVEL_MSG_MAX_HITS = 2      # 窗口内违规次数达此值触发惩罚
LEVEL_MSG_PUNISH = 1        # 频繁违规惩罚：0=只提醒 1=禁言 2=踢出
LEVEL_MSG_MUTE_SECONDS = 60 # 违规后禁言秒数（0=不禁言；小于30视为永久）
LEVEL_QUERY_NONE_TPL = "ℹ️ 积分等级未配置（后台「积分系统 → 积分等级」添加）。"
LEVEL_DOWN_NOTIFY_ENABLED = 1   # 用户降级通知开关（用户截图）
LEVEL_DOWN_MSG_TPL_DEFAULT = "📉 {name} 降级到「{level}」。\n💰 当前积分：{balance}"
# 等级可授权的消息类型（键=存储值，值=显示名）。顺序即网页勾选顺序
LEVEL_PERM_OPTIONS = [
    ("text",    "允许发送文字（纯文字，无媒体、非转发）"),
    ("photo",   "允许发送图片"),
    ("video",   "允许发送视频"),
    ("audio",   "允许发送音频"),
    ("sticker", "允许发送贴纸"),
    ("forward", "允许转发消息"),
    ("link",    "允许发送含链接的消息"),
    ("edit",    "允许编辑消息"),
]
LEVEL_PERM_NAMES = {k: v.split("（")[0].replace("允许发送", "").replace("允许转发", "转发").replace("允许编辑", "编辑")
                    for k, v in LEVEL_PERM_OPTIONS}
LEVEL_PERM_DEFAULT = ",".join(k for k, _v in LEVEL_PERM_OPTIONS)   # 旧数据默认全放行
level_msg_violations = {}   # (cid, uid) -> [违规时间戳...]，等级消息越权计数（窗口内）
LEVEL_CMD = "我的等级"
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
    "rp_msg_grab": "🧧 抢到 {amount} 积分！",
    "rp_msg_none": "手慢了～什么都没抢到～",
    "rp_msg_dup": "❌ 你已经抢过该红包了",
    "rp_msg_poor": "❌ 积分不足：需要 {need}，当前 {balance}。",
    "rp_msg_target": "🎯 这是专属红包，只有 {name} 能抢",
    "rp_msg_log": "{rank} {name}：{amount} 积分",
    "level_up_msg_tpl": "🎉 恭喜 {name} 升级「{level}」！\n💰 当前积分：{balance}",
    "level_down_msg_tpl": "📉 {name} 降级到「{level}」。\n💰 当前积分：{balance}",
    "level_query_msg_tpl": ("🎖 {name} 的等级：{level}\n"
                            "💰 当前积分：{balance}\n"
                            "{base_line}{next_line}"),
    "level_query_none_tpl": "ℹ️ 积分等级未配置（后台「积分系统 → 积分等级」添加）。",
    "level_msg_warn_tpl": ("⚠️ {name}，你当前等级「{level}」还不能发送{kind}。\n"
                           "多发消息或参与游戏升级后即可解锁。"),
    "level_msg_mute_tpl": "🔇 {name} 因频繁发送超出等级权限的消息，已被禁言 {seconds} 秒。",
    "mall_msg_buy": "🛍 购买成功：{item}（-{price} 积分）\n💰 余额 {balance}\n管理员会尽快处理发货。",
    "mall_msg_empty": "🛒 商城暂无商品，管理员可在后台上架。",
    "inherit_msg_ok": "✅ {name} → {target}：{amount} 积分{fee}\n💰 对方到账 {recv}｜你当前 {balance}",
    "redeem_msg_list": "🎁 {goodsName}｜{pointNum} 积分｜剩余 {leftNum}",
    "redeem_msg_ok_group": "🎉 {name} 兑换成功：{goodsName}（-{pointNum} 积分）\n💰 余额 {balance}",
    "redeem_msg_ok_dm": "🎉 你已成功兑换「{goodsName}」（{pointNum} 积分），请联系管理员发货。",
    "invite_ok_group": "🎉 {invitee} 通过 {inviter} 的邀请加入本群！\n💰 {inviter} 获得邀请奖励 {reward} 积分",
    "invite_rank_today_msg": "📈 <b>今日邀请排行</b>",
    "invite_rank_month_msg": "📅 <b>本月邀请排行</b>",
    "invite_rank_all_msg": "🏆 <b>总邀请排行</b>",
    "invite_rank_line_fmt": "{i}. {name}｜邀请 {count} 人",
    "invite_invalid_msg": "⚠️ {name} 的邀请链接无效，请让邀请人重新生成",
    "invite_self_msg": "😅 不能邀请自己哦",
    "force_sub_warn_tpl": "📢 {name}，请先订阅我们的频道再发言～\n- 加入频道：{channels}\n订阅后重新发一次消息即可正常聊天。\n（本提示 {seconds} 秒后自动消失）",
}
INVITE_OK_GROUP = MSG_TPL_DEFAULTS["invite_ok_group"]
INVITE_RANK_TODAY_MSG = MSG_TPL_DEFAULTS["invite_rank_today_msg"]
INVITE_RANK_MONTH_MSG = MSG_TPL_DEFAULTS["invite_rank_month_msg"]
INVITE_RANK_ALL_MSG = MSG_TPL_DEFAULTS["invite_rank_all_msg"]
INVITE_RANK_LINE_FMT = MSG_TPL_DEFAULTS["invite_rank_line_fmt"]
INVITE_INVALID_MSG = MSG_TPL_DEFAULTS["invite_invalid_msg"]
INVITE_SELF_MSG = MSG_TPL_DEFAULTS["invite_self_msg"]
SIGN_MSG_TPL = MSG_TPL_DEFAULTS["sign_msg_tpl"]
QUERY_MSG_TPL = MSG_TPL_DEFAULTS["query_msg_tpl"]
ADD_MSG_TPL = MSG_TPL_DEFAULTS["add_msg_tpl"]
RP_MSG_GRAB = MSG_TPL_DEFAULTS["rp_msg_grab"]
RP_MSG_NONE = MSG_TPL_DEFAULTS["rp_msg_none"]
RP_MSG_DUP = MSG_TPL_DEFAULTS["rp_msg_dup"]
RP_MSG_POOR = MSG_TPL_DEFAULTS["rp_msg_poor"]
RP_MSG_TARGET = MSG_TPL_DEFAULTS["rp_msg_target"]
RP_MSG_LOG = MSG_TPL_DEFAULTS["rp_msg_log"]
LEVEL_UP_MSG_TPL = MSG_TPL_DEFAULTS["level_up_msg_tpl"]
LEVEL_DOWN_MSG_TPL = MSG_TPL_DEFAULTS["level_down_msg_tpl"]
LEVEL_QUERY_MSG_TPL = MSG_TPL_DEFAULTS["level_query_msg_tpl"]
MALL_MSG_BUY = MSG_TPL_DEFAULTS["mall_msg_buy"]
MALL_MSG_EMPTY = MSG_TPL_DEFAULTS["mall_msg_empty"]
INHERIT_MSG_OK = MSG_TPL_DEFAULTS["inherit_msg_ok"]
REDEEM_MSG_LIST = MSG_TPL_DEFAULTS["redeem_msg_list"]
REDEEM_MSG_OK_GROUP = MSG_TPL_DEFAULTS["redeem_msg_ok_group"]
REDEEM_MSG_OK_DM = MSG_TPL_DEFAULTS["redeem_msg_ok_dm"]
FORCE_SUB_WARN_TPL = MSG_TPL_DEFAULTS["force_sub_warn_tpl"]

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
newbie_rewarded = {}                                 # "cid:uid" -> True 新人欢迎奖励已发放（防重复）
chat_dup_hist = {}                                   # (cid,uid,内容归一化) -> [ts,...] 有效发言查重用
invite_daily = defaultdict(lambda: defaultdict(lambda: defaultdict(dict)))
# invite_daily[date][cid][inviter] = {"times": 已发奖次数, "points": 已发奖积分}（每日拉新上限用）
mall_orders = []                                     # [{"ts","cid","uid","name","item","price"}]
chat_rules = []                                      # 阿福式聊天积分规则 [{"match","points","on"}] 命中即停；空=走每N字符旧规则
buy_packages = []                                    # 购买积分套餐 [{"name","cny","points","sort","on"}]
rp_packets = {}                                      # pid -> {"cid","from","left_amt","left_n","grabbed":{uid:amt},"ts","msg_id"}
guesses = {}                                         # cid -> 竞猜 {"q","a","b","end_ts","locked","bets":{uid:{"A","B"}},"side_pots":{"A","B"},"msg_id","task"}
_guess_tasks = set()                                 # 兜底任务的强引用：只 create_task 不保存引用可能被 GC 掉，兜底就形同虚设
invite_links = defaultdict(dict)                     # cid -> {uid: {"link","invite_id","ts"}} 每人专属邀请链接（必须 defaultdict：恢复/写入走 [cid][uid] 两级，普通 dict 会 KeyError 被吞→整表丢失→归因全失败、邀请进度恒 0）
invite_records = {}                                  # "cid:uid" -> {"cid","inviter","invitee","invitee_name","ts","qualified","rejected","left","award","link"}；旧存档可能带 audit(ok/pending/unmet/rejected) 兼容读取
invite_pending = {}                                  # "cid:uid" -> 进群申请携带的邀请链接（人审批后 join 事件常不带链接，靠这个兜底归因；内存态）
invite_confirmed = {}                                # "cid:uid" -> 邀请人 uid（deep-link START / 主动问按钮 锁定的归因；落盘持久化）
invite_debug = defaultdict(list)                     # cid -> [最近10条邀请链路调试事件]（每环失败不再静默，/邀请调试 可查）
_inv_notice_ts = {}                                  # "cid:uid" -> 上次发「进群未计入邀请/归因失败」提示的时间戳（运行时态）
                                                     # 同一次进群会同时到 chat_member 与服务消息两个事件源，提示类副作用必须按人短窗去重（2026-09-10 用户报「收到 2 条」）


def _inv_notice_fresh(key, window=60):
    """诊断/失败提示的窗口去重：窗口内同一人只发一次。返回 True=允许发（并登记）。

    注意：只去重「提示类」副作用，不挡归因本身——第二个事件源若带来链接仍会正常归因。"""
    now = time.time()
    last = float(_inv_notice_ts.get(key, 0) or 0)
    if last and now - last < max(10, int(window)):
        return False
    _inv_notice_ts[key] = now
    if len(_inv_notice_ts) > 3000:                   # 防无限膨胀：清 1 小时前的旧键
        for k in [k for k, t in _inv_notice_ts.items() if now - float(t) > 3600]:
            _inv_notice_ts.pop(k, None)
    return True


def _inv_dbg(cid, msg):
    """邀请链路调试事件：任何一环（发链接/申请/进群/归因）走到都记录，失败不再无声无息。"""
    try:
        invite_debug[cid].append(f"{now_bj().strftime('%H:%M:%S')} {msg}")
        invite_debug[cid] = invite_debug[cid][-10:]
    except Exception:
        pass
buy_orders = {}                                      # oid -> {"cid","uid","amount","ts"} 购买积分申请（管理员人工确认）
warn_counts = defaultdict(lambda: defaultdict(int))  # warn_counts[cid][uid] = 警告次数（网页成员列表加减）
redeem_goods = []                                    # 积分兑换商品 [{"name","price","left","redeemed","desc","on"}] left=0 不限
redeem_counts = {}                                   # uid -> 全期已兑换次数（每人限购用）
redeem_orders = []                                   # 兑换订单（防伪）：[{"no","ts","cid","uid","item","price","bal"}]，只留最近 500 条
game_flows = []                                      # 游戏对局人对人净转移（德州/金花/竞猜，审查"通过游戏故意输牌送分"用），只留最近 2000 条

# ---------- 群组管理数据 ----------
member_profiles = defaultdict(lambda: defaultdict(dict))  # member_profiles[cid][uid] = {"name","first","last","msgs"}
whitelist = defaultdict(set)                         # whitelist[cid] = {uid} 白名单（免疫禁言等）
leave_records = defaultdict(list)                    # leave_records[cid] = [{"ts","uid","name"}] 退群记录(每群留100)
join_requests = defaultdict(list)                    # join_requests[cid] = [{"ts","uid","name"}] 入群申请(每群留100)
member_joined_at = defaultdict(lambda: defaultdict(float))  # member_joined_at[cid][uid] = 入群时间戳（新成员观察期用，运行时态）
_bot_app = None   # 运行中的 Application（网页后台跨线程调 bot API 用，post_init 里赋值）
_bot_loop = None  # bot 主事件循环
_BOT_USERNAME = ""  # bot 用户名缓存（兑换按钮跳私聊深链 https://t.me/<用户名>?start=... 用）
admin_logs = []                                      # [{"ts","cid","admin","action","target"}] 管理员操作记录(留300)

# ---------- 防小号资金监管 ----------
BOT_BOOT_TS = time.time()                            # 进程启动时间（/status 运行时长用）
ledger = []                                          # 资金流台账 [{"ts","cid","frm","to","amt","typ"}] 红包领取/转赠逐笔(留5000)
inherit_daily = defaultdict(lambda: defaultdict(lambda: defaultdict(int)))  # inherit_daily[date][cid][uid] = 当日累计转赠支出
user_first_seen = {}                                 # uid -> 首次与 bot 互动的时间戳（兑换门槛用）
backup_msg_ids = []                                  # 自动备份文件消息ID（管理员私聊，轮换只留7份）
settings_backup_msg_ids = []                         # 设置备份文件消息ID（单独轮换只留7份）
web_pending_otp = {}                                 # 后台二次验证待确认：otp_token -> {"code","exp","ip"}
web_magic_tokens = {}                                # /后台 一键登录：token -> {"uid","exp"}（2分钟、一次性）
# 群组抽奖：每群同时最多一个进行中活动
# lotteries[cid] = {title, prizes, fee, keyword, start_ts, end_ts, msg_id,
#                   participants:[(uid, ts, name)], status, winners, creator, chat_id}
lotteries = {}

def _write_settings_file(cfg: dict, password: str, cmd_aliases=None, tg_menu=None, sidebar_order=None):
    """写设置文件 + 同步到数据快照。

    安全红线：密码**只存 hash**，明文绝不落盘——否则它会随 bot_data.json 的自动备份
    发到每个备份接收人手里，等于把后台口令交给普通管理员。
    """
    global _web_password_hash, _web_salt, _web_password
    if sidebar_order is None:
        sidebar_order = list(SETTINGS_SNAPSHOT.get("sidebar_order") or [])
    if password:
        try:
            _web_salt = secrets.token_hex(16)
            _web_password_hash = _hash_web_pwd(password, _web_salt)
            _web_password = password   # 仅内存，供本次运行期的明文分支比对
        except Exception:
            logger.exception("密码摘要计算失败（保持原凭据不变）")
    if not _web_password_hash:
        # 内存还没凭据（如恢复流程早于 load_settings）：从现有文件继承，绝不写空凭据把人锁在门外
        try:
            with open(SETTINGS_FILE, "r", encoding="utf-8") as f:
                r0 = json.load(f)
            h0 = str(r0.get("web_password_hash", "")).strip()
            s0 = str(r0.get("web_password_salt", "")).strip()
            if h0 and s0:
                _web_password_hash, _web_salt = h0, s0
            elif not password and str(r0.get("web_password", "")).strip():
                _web_password = str(r0.get("web_password", "")).strip()
        except Exception:
            pass
    payload = {"fields": cfg, "web_password_hash": _web_password_hash,
               "web_password_salt": _web_salt,
               "cmd_aliases": cmd_aliases or {}, "tg_menu": tg_menu or [],
               "sidebar_order": sidebar_order,
               # 群级覆盖：{群ID: {设置键: 值}}，只存与该群"全局默认"不同的项
               "group_settings": _group_settings_json(),
               "chat_rules": list(chat_rules), "buy_packages": list(buy_packages),
               "point_levels": list(POINT_LEVELS), "mall_items": list(MALL_ITEMS),
               "redeem_goods": list(redeem_goods),
               # 4 个调度任务的作用对象（json 不支持 set，存 list）
               "schedule_targets": {
                   "daily_reset_groups": sorted(daily_reset_groups),
                   "leaderboard_groups": sorted(leaderboard_groups),
                   "backup_admins": sorted(backup_admins),
                   "admin_report_admins": sorted(admin_report_admins),
               }}
    try:
        tmp = f"{SETTINGS_FILE}.tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(payload, f, ensure_ascii=False, indent=2)
        os.replace(tmp, SETTINGS_FILE)
    except Exception:
        logger.exception("设置文件写盘失败")
    # 同步进快照：随 bot_data.json 一起落盘与备份，容器重建后可从数据文件还原设置
    try:
        SETTINGS_SNAPSHOT.clear()
        SETTINGS_SNAPSHOT.update(payload)
        save_data()
    except Exception:
        logger.exception("设置快照同步失败")

_DYN_CMD_OWNED = {}  # gname -> 上次注册的动态指令名（改名后移除旧指令）

def _fn_legit_aliases(fn):
    """某命令当前**应当**生效的别名集合：有覆盖=覆盖表里的全部；无覆盖=出厂别名。

    与 apply_command_aliases 的语义严格一致（覆盖即替换）。
    用途：判断「上一轮的动态指令名」是否还属于合法别名——是就别删。
    """
    overrides = globals().get("CMD_ALIAS_OVERRIDES") or {}
    base = globals().get("BASE_CMD_ALIASES") or {}
    override = overrides.get(fn.__name__)
    if override is not None:
        names = [a.strip() for a in str(override).replace("，", ",").split(",") if a.strip()]
        if names:
            return set(names)
    return {a for a, f in base.items() if f is fn}

def _sync_dyn_aliases():
    """把网页自定义的指令名（查询积分/签到/积分排行）注册进命令分发表；旧名随之失效。

    修复（2026-09-09 用户报告）：此前无条件 pop 掉「上一轮动态名」，而 SIGN_CMD 取的是
    覆盖表的**第一个**别名，于是把用户显式写在覆盖表里的其它别名一起删了——
    典型表现：签到页填「每日签到,签到」时「签到」失效，把顺序换成「签到,每日签到」才好。
    现在只移除「既不在出厂别名、也不在覆盖表」的陈旧动态名，用户配置的别名一律保留。
    """
    aliases = globals().get("CMD_ALIASES")
    if aliases is None:
        return
    for gname, fn in (("QUERY_CMD", cmd_my_points), ("SIGN_CMD", cmd_sign), ("RANK_CMD", cmd_points_rank), ("LEVEL_CMD", cmd_my_level), ("REDEEM_CMD", cmd_points_redeem),
                      ("INVITE_LINK_CMD", cmd_invite_link), ("INVITE_RANK_TODAY_CMD", cmd_invite_rank_today),
                      ("INVITE_RANK_MONTH_CMD", cmd_invite_rank_month), ("INVITE_RANK_ALL_CMD", cmd_invite_rank_all)):
        old = _DYN_CMD_OWNED.get(gname)
        if old and old not in _fn_legit_aliases(fn) and aliases.get(old) is fn:
            aliases.pop(old, None)
        name = globals().get(gname)
        if name:
            aliases[name] = fn
            _DYN_CMD_OWNED[gname] = name

def _cross_keys(group):
    """跨分组聚合页（话术库等）可编辑的字段集合；普通分组返回 None（维持按组过滤）。

    话术模板散落在 11 个分组里，以前改一句欢迎语要先想清楚它在哪个菜单。
    """
    if group == "tpls":
        return {k for k, _g, _l, t, _lo, _hi, _grp in SETTINGS_FIELDS if t == "text"}
    if group == "mod":
        return ({k for k, _g, _l, _t, _lo, _hi, grp in SETTINGS_FIELDS if grp == "mod"}
                | set(MOD_PAGE_FIELDS))
    return None


def _grp_title(grp):
    """把分组键（points/sign）翻成人类可读标题（积分系统 · 每日签到）。"""
    base, _, sub = str(grp).partition("/")
    gnames = {k: n for k, n, _i in SETTINGS_GROUPS}
    name = gnames.get(base, base)
    if sub:
        subname = dict(SUBPAGES.get(base, [])).get(sub, sub)
        name = f"{name} · {subname}"
    return name


def _multi_set(raw, key):
    """把多选字段的原始值（list 或逗号分隔字符串）规整成逗号分隔字符串，只保留合法选项。"""
    allowed = [v for v, _l in MULTI_OPTIONS.get(key, [])]
    if isinstance(raw, (list, tuple)):
        parts = [str(p).strip() for p in raw]
    else:
        parts = [p.strip() for p in re.split(r"[,，]", str(raw)) if p.strip()]
    return ",".join([p for p in parts if p in allowed])


def _multi_has(raw, opt):
    """判断多选字符串里是否含某项（自动删除规则判定用）。"""
    return opt in {p.strip() for p in str(raw or "").split(",") if p.strip()}


def _migrate_legacy_autodel(cfg: dict):
    """旧版「每类型一个开关」的自动删除配置 → 新版两个多选。

    老的 bot_settings.json 里还是 autodel_photo / autodel_links / autodel_service_seconds
    这类键，直接套用会全部丢失（用户已开的开关莫名关掉），所以先折算成新字段。
    只有新版字段没给值时才迁移，避免覆盖用户刚在网页上的新选择。
    """
    legacy_media = {
        "autodel_photo": "photo", "autodel_video": "video", "autodel_sticker": "sticker",
        "autodel_gif": "gif", "autodel_voice": "voice", "autodel_document": "document",
        "autodel_archive": "archive", "autodel_executable": "executable",
        "autodel_contact": "contact", "autodel_service": "service",
    }
    legacy_text = {"autodel_links": "link", "autodel_long_enabled": "long",
                   "autodel_premium_emoji": "premium_emoji"}
    def _on(v):
        return str(v).strip().lower() in ("1", "on", "true", "yes", "是")
    if any(k in cfg for k in legacy_media) and "autodel_media_types" not in cfg:
        picked = [opt for k, opt in legacy_media.items() if _on(cfg.get(k, 0))]
        cfg["autodel_media_types"] = ",".join([o for o, _l in MULTI_OPTIONS["autodel_media_types"]
                                               if o in picked])
    if any(k in cfg for k in legacy_text) and "autodel_text_rules" not in cfg:
        picked = [opt for k, opt in legacy_text.items() if _on(cfg.get(k, 0))]
        cfg["autodel_text_rules"] = ",".join([o for o, _l in MULTI_OPTIONS["autodel_text_rules"]
                                              if o in picked])
    if "autodel_service_seconds" in cfg and "autodel_media_seconds" not in cfg:
        try:
            cfg["autodel_media_seconds"] = int(float(cfg["autodel_service_seconds"]))
        except (ValueError, TypeError):
            pass
    return cfg


def apply_settings(cfg: dict):
    """把设置字典套用到内存全局常量（带类型与范围校验，非法值跳过）。

    数字字段先套用（HORSE_COUNT 先生效，名称/表情才好做数量联动校验）；
    names/emoji 要求拆分后条数 == 当前 HORSE_COUNT，否则整条跳过；
    bets 要求 1~6 个 1~100000 的正整数，自动去重升序。
    multi 为多选项，只保留 MULTI_OPTIONS 里登记的合法值，存为逗号分隔字符串。
    """
    cfg = _migrate_legacy_autodel(dict(cfg))
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
    # 多选字段（勾选组）：非法选项直接丢弃，顺序按 MULTI_OPTIONS 定义
    for key, gname, _label, ftype, _lo, _hi, _grp in SETTINGS_FIELDS:
        if key not in cfg or ftype != "multi":
            continue
        v = _multi_set(cfg[key], key)
        globals()[gname] = v
        applied[key] = v
    # 等级表 / 商品表：每行 "名称:数值"（支持中英文冒号），按数值升序
    for key, gname, ftype in (("point_levels", "POINT_LEVELS", "levels"), ("mall_items", "MALL_ITEMS", "items")):
        if key not in cfg:
            continue
        raw = cfg[key]
        if isinstance(raw, (list, tuple)):
            # 富结构直传（网页保存的等级表含 perms/on）：原样收下，只做字段校验
            if ftype == "levels" and raw and all(isinstance(x, dict) for x in raw):
                parsed, ok = [], True
                for it in raw:
                    name = str(it.get("name", "")).strip()[:12]
                    if not name or any(ch in name for ch in "<>&"):
                        ok = False; break
                    try:
                        v = int(float(it.get("value", 0) or 0))
                    except (TypeError, ValueError):
                        ok = False; break
                    if not (0 <= v <= 10000000):
                        ok = False; break
                    item = {"name": name, "value": v}
                    if "perms" in it:
                        item["perms"] = str(it.get("perms") or "")
                    if "on" in it:
                        item["on"] = it.get("on")
                    parsed.append(item)
                if ok and parsed and len(parsed) <= 30:
                    parsed.sort(key=lambda x: x["value"])
                    globals()[gname] = parsed
                    _normalize_levels()
                    applied[key] = parsed
                continue
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
            if ftype == "levels":
                _normalize_levels()   # 纯文本格式（名称:数值）也要补 perms/on
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
        elif ftype == "emoji":
            # 表情列表（如赛马表情）：每条 ≤4 字符；条数联动校验走下方赛马三件套
            if parts and all(0 < len(p) <= 4 and not any(ch in p for ch in "<>&") for p in parts):
                globals()[gname] = parts
                applied[key] = parts
        else:
            # 通用词表（敏感词/域名白名单等）：每条 ≤64 字符；删光提交空=清空词表。
            # 此前缺失本分支，导致保存被静默丢弃且页面永远提示「已跳过」——敏感词形同虚设的真 bug。
            if parts:
                if all(0 < len(p) <= 64 and not any(ch in p for ch in "<>&") for p in parts):
                    globals()[gname] = parts
                    applied[key] = parts
            else:
                globals()[gname] = []
                applied[key] = []
    return applied

def _load_settings_payload():
    """依次尝试：bot_settings.json → bot_data.json 内嵌快照。

    容器重建会清空 bot_settings.json，但 bot_data.json 有自动备份，
    所以从数据文件的 _settings 键还原，能让重新部署后的设置保持原样。
    """
    if os.path.exists(SETTINGS_FILE):
        try:
            with open(SETTINGS_FILE, "r", encoding="utf-8") as f:
                return json.load(f), "file"
        except Exception:
            logger.exception("设置文件读取失败，尝试从数据文件还原")
    for src in (DATA_FILE, DATA_BACKUP_FILE):
        if not os.path.exists(src):
            continue
        try:
            with open(src, "r", encoding="utf-8") as f:
                embedded = json.load(f).get("_settings")
            if isinstance(embedded, dict) and embedded.get("fields"):
                logger.warning("设置文件缺失，已从 %s 内嵌快照还原设置", src)
                return embedded, "data"
        except Exception:
            continue
    return None, ""


def load_settings():
    """启动时读取设置并套用；无设置文件则用数据内嵌快照，仍无则用代码内默认值。"""
    global _web_password, _web_password_hash, _web_salt
    payload, origin = _load_settings_payload()
    if not payload:
        logger.info("无可用设置（%s 与数据快照均无），全部使用默认配置", SETTINGS_FILE)
        return
    try:
        if "fields" not in payload and "_settings" in payload:
            payload = payload["_settings"]  # 误指向 bot_data.json 时拆出内嵌设置，表格化数据(chat_rules等)才读得到
        apply_settings(payload.get("fields", {}))
        # 密码：优先读 hash（新格式）；旧存档是明文则临时保留，下次写盘自动升级为 hash
        h = str(payload.get("web_password_hash", "")).strip()
        s = str(payload.get("web_password_salt", "")).strip()
        if h and s:
            _web_password_hash, _web_salt = h, s
            _web_password = ""   # 内存不再保留明文（hash 无法反推，登录走 _pwd_ok 的 hash 分支）
        pwd = str(payload.get("web_password", "")).strip()
        if pwd:
            _web_password = pwd
        # 命令管理：别名覆盖层 + Telegram / 菜单
        ca = payload.get("cmd_aliases") or {}
        if isinstance(ca, dict):
            CMD_ALIAS_OVERRIDES.clear()
            CMD_ALIAS_OVERRIDES.update({str(k): str(v) for k, v in ca.items()})
        tm = payload.get("tg_menu") or []
        if isinstance(tm, list) and tm:
            cleaned = [list(x) for x in tm if isinstance(x, (list, tuple)) and len(x) == 2]
            if cleaned:
                TG_MENU.clear(); TG_MENU.extend(cleaned)
        apply_command_aliases()
        SETTINGS_SNAPSHOT.clear(); SETTINGS_SNAPSHOT.update(payload)
        so = payload.get("sidebar_order") or []
        if isinstance(so, list):
            SIDEBAR_ORDER.clear(); SIDEBAR_ORDER.extend(str(x) for x in so)
        # 表格化数据：聊天积分规则 / 购买积分套餐
        for key, gl in (("chat_rules", chat_rules), ("buy_packages", buy_packages),
                        ("point_levels", POINT_LEVELS), ("mall_items", MALL_ITEMS),
                        ("redeem_goods", redeem_goods)):
            v = payload.get(key)
            if isinstance(v, list):
                gl.clear(); gl.extend(x for x in v if isinstance(x, dict))
        _normalize_levels()   # 旧存档等级表补 perms/on（幂等）
        # 群级覆盖：{群ID: {设置键: 值}}。旧存档没有这个键 → 不动内存（避免把已恢复的覆盖清掉）
        if "group_settings" in payload:
            _gs = payload.get("group_settings")
            GROUP_SETTINGS.clear()
            if isinstance(_gs, dict):
                for _cid, _rec in _gs.items():
                    try:
                        _c = int(_cid)
                    except (TypeError, ValueError):
                        continue
                    if isinstance(_rec, dict) and _rec:
                        GROUP_SETTINGS[_c] = {str(k): v for k, v in _rec.items()}
            logger.info("群级覆盖已恢复：%d 个群", len(GROUP_SETTINGS))
        # 4 个调度任务的作用对象
        st = payload.get("schedule_targets") or {}
        if isinstance(st, dict):
            try: daily_reset_groups.update(int(x) for x in st.get("daily_reset_groups", []) if str(x).lstrip("-").isdigit())
            except Exception: pass
            try: leaderboard_groups.update(int(x) for x in st.get("leaderboard_groups", []) if str(x).lstrip("-").isdigit())
            except Exception: pass
            try: backup_admins.update(int(x) for x in st.get("backup_admins", []) if str(x).lstrip("-").isdigit())
            except Exception: pass
            try: admin_report_admins.update(int(x) for x in st.get("admin_report_admins", []) if str(x).lstrip("-").isdigit())
            except Exception: pass
        # 懒填默认：空集合 = 默认全授权群/默认管理员
        if not daily_reset_groups: daily_reset_groups.update(AUTHORIZED_GROUPS)
        if not leaderboard_groups: leaderboard_groups.update(AUTHORIZED_GROUPS)
        if not backup_admins: backup_admins.add(ADMIN_USER_ID)
        if not admin_report_admins: admin_report_admins.add(ADMIN_USER_ID)
        # 从数据还原的：立刻回写设置文件，保证网页端与后续保存读到一致内容
        if origin == "data":
            _write_settings_file(payload.get("fields", {}), _web_password,
                                 payload.get("cmd_aliases") or {}, payload.get("tg_menu") or [])
        logger.info("设置已加载（来源：%s）", "设置文件" if origin == "file" else "数据内嵌快照")
    except Exception:
        logger.exception("设置套用失败，使用默认配置")

def save_settings(cfg: dict, new_password: str = ""):
    """网页保存入口：套用内存 + 与已有存档合并写盘（分页保存互不覆盖）+ 可选改密码。"""
    global _web_password
    with _settings_lock:
        try:
            with open(SETTINGS_FILE, "r", encoding="utf-8") as f:
                raw = json.load(f)
        except Exception:
            raw = {}
        stored = raw.get("fields", {})
        applied = apply_settings(cfg)
        stored.update(applied)
        if new_password and len(new_password.strip()) >= 4:
            _web_password = new_password.strip()
        _write_settings_file(stored, _web_password, raw.get("cmd_aliases") or {}, raw.get("tg_menu") or [])
    return applied

def save_group_settings(cid, cfg: dict):
    """网页在「某个群」下保存：只把与该群全局默认不同的项存成群级覆盖。

    用户确认的口径：① 全部设置项都能按群覆盖 ② 继承全局、只存差异。
    因此：
      - 标准值 == 全局默认 → **清除**该群覆盖（回继承）。否则会出现"存了个和全局一样的值，
        以后改全局这个群却不跟着变"的反直觉行为。
      - 标准值 != 全局默认 → 写入群级覆盖。
      - 不属于群级范围的键（密码/调度/备份/等级表/指令名）→ 退回按全局保存，行为与改前一致。
    返回 applied（键 → 标准值），网页据此提示"已保存/已跳过"。
    """
    cid = _safe_cid(cid)
    if not cid:
        return save_settings(cfg)
    scoped = {k: v for k, v in cfg.items() if k in GROUP_SCOPED_KEYS}
    rest = {k: v for k, v in cfg.items() if k not in GROUP_SCOPED_KEYS}
    norm = _normalize_settings_values(scoped)
    applied = {}
    for key, val in norm.items():
        gname = _KEY2VAR.get(key)
        if gname is None:
            continue
        if val == globals().get(gname):
            group_set(cid, key, None)      # 与全局一致 → 不存差异，回继承
        else:
            group_set(cid, key, val)       # 该群专属
        applied[key] = val
    if rest:
        applied.update(save_settings(rest))   # 全局键：照旧写全局
    else:
        save_settings({})                     # 仅触发落盘（把 group_settings 写进设置文件）
    logger.info("群 %s 保存群级设置：覆盖 %d 项，全局 %d 项", cid, len(norm), len(rest))
    return applied
BEIJING_TZ = timezone(timedelta(hours=8))
HAND_NAME_CN = {"High Card":"高牌", "Pair":"一对", "One Pair":"一对", "Two Pair":"两对", "Three of a Kind":"三条", "Straight":"顺子", "Flush":"同花", "Full House":"葫芦", "Four of a Kind":"四条", "Straight Flush":"同花顺", "Royal Flush":"皇家同花顺"}
RANK_ICONS = ["🥇", "🥈", "🥉", "4️⃣", "5️⃣", "6️⃣", "7️⃣", "8️⃣", "9️⃣", "🔟"]


def rank_marker(index):
    if index == 1 and sget("RANK_1_EMOJI"): return sget("RANK_1_EMOJI")
    if index == 2 and sget("RANK_2_EMOJI"): return sget("RANK_2_EMOJI")
    if index == 3 and sget("RANK_3_EMOJI"): return sget("RANK_3_EMOJI")
    return RANK_ICONS[index - 1] if 1 <= index <= len(RANK_ICONS) else f"🔸{index}"


def total_profit_by_game(game_profit, chat_id):
    """聚合某游戏所有日期的盈亏为累计总数。"""
    total = defaultdict(int)
    for dates in game_profit.values():
        for uid, v in dates.get(chat_id, {}).items():
            total[uid] += v
    return dict(total)


# ---------- 数据 ----------
game_chips = defaultdict(lambda: defaultdict(lambda: sget("GAME_STARTING_CHIPS")))  # 统一积分钱包（全游戏/签到/红包/商城共用，初始 5W）
AUTHORIZED_GROUPS = set()
BLACKLISTED_USERS = set()  # 被拉黑、禁止使用该机器人的用户（管理员可解封）
race_history = defaultdict(list)
blackjack_history = defaultdict(list) # 新增 21点历史
race_daily_stats = defaultdict(lambda: [0] * sget("HORSE_COUNT"))
poker_profit_by_date = defaultdict(lambda: defaultdict(lambda: defaultdict(int)))
race_profit_by_date = defaultdict(lambda: defaultdict(lambda: defaultdict(int)))
blackjack_profit_by_date = defaultdict(lambda: defaultdict(lambda: defaultdict(int)))
jinhua_profit_by_date = defaultdict(lambda: defaultdict(lambda: defaultdict(int)))
race_jackpot = defaultdict(int)
# 赛车系统加奖已发额：race_subsidy_by_day[日期][群] += 金额（用于「每日上限」判定，2026-09-11 用户要求）
race_subsidy_by_day = defaultdict(lambda: defaultdict(int))
hourly_race_enabled = defaultdict(lambda: False)
# 各调度任务的"作用对象"（网页可配）：每日重置/德州日榜=作用群；备份/日报=接收私聊的管理员
daily_reset_groups = set()    # 默认全授权群，启动时懒填
leaderboard_groups = set()
backup_admins = set()         # 默认 {ADMIN_USER_ID}，启动时懒填
admin_report_admins = set()
# 调度任务调试：每群最后成功开赛时间 + 跳过原因计数（/定时任务 调试命令读这些）
race_last_sent = {}                                  # cid -> "YYYY-MM-DD HH:MM"
race_skip_stats = defaultdict(lambda: defaultdict(int))  # cid -> {reason: count}
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
season_exchange_daily = defaultdict(lambda: defaultdict(lambda: defaultdict(int)))  # season_exchange_daily[date][cid][uid] = 当日已消耗的聊天积分（兑换每日上限用）
season_exchange_bonus = defaultdict(lambda: defaultdict(int))  # season_exchange_bonus[cid][uid] = 本赛季累计兑换得到的排位分（「额外底分」：每日重置保留、不计入盈亏榜）
# 累计获得账本（只增不减）：等级按它算，兑换实物/商城消费不掉级
# 语义：玩家在本群「历史累计赚到过多少积分」——不含游戏退款/下注返还等原路退回，
#       也不含转赠收到的分（那是他人分的转移，不是新产出）。
total_earned = defaultdict(lambda: defaultdict(int))   # total_earned[cid][uid] = 累计获得
games_played = defaultdict(lambda: defaultdict(int))   # games_played[cid][uid] = 累计参与局数（归零赠送门槛用）
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
                "race_subsidy_by_day": {date: {str(cid): amount for cid, amount in chats.items()} for date, chats in race_subsidy_by_day.items()},
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
                "season_exchange_daily": {date: {str(cid): {str(uid): int(v) for uid, v in users.items()} for cid, users in chats.items()} for date, chats in season_exchange_daily.items()},
                "season_exchange_bonus": {str(cid): dict(users) for cid, users in season_exchange_bonus.items()},
                # 累计获得账本 + 累计局数（等级按累计获得算，消费不掉级；局数用于归零门槛）
                "total_earned": {str(cid): {str(uid): int(v) for uid, v in users.items()} for cid, users in total_earned.items()},
                "games_played": {str(cid): {str(uid): int(v) for uid, v in users.items()} for cid, users in games_played.items()},
                "user_titles": {str(uid): sorted(t) for uid, t in user_titles.items()},
                "title_expiry": {str(uid): {t: int(exp) for t, exp in ts.items()} for uid, ts in title_expiry.items()},
                "title_equipped": {str(uid): t for uid, t in title_equipped.items()},
                "champions_history": champions_history,
                "user_names": {str(uid): n for uid, n in user_names.items()},
                "sign_data": {str(cid): {str(uid): dict(v) for uid, v in users.items()} for cid, users in sign_data.items()},
                "chat_today": {date: {str(cid): {str(uid): v for uid, v in users.items()} for cid, users in chats.items()} for date, chats in chat_today.items()},
                "newbie_rewarded": {k: 1 for k in newbie_rewarded},
                "invite_daily": {date: {str(cid): {str(u): dict(v) for u, v in us.items()}
                                        for cid, us in cs.items()} for date, cs in invite_daily.items()},
                "mall_orders": mall_orders[-200:],
                "guesses": {str(cid): {"q": g["q"], "a": g["a"], "b": g["b"], "end_ts": g["end_ts"],
                                       "locked": bool(g.get("locked")), "msg_id": g.get("msg_id"),
                                       "bets": {str(uid): {"A": int(v["A"]), "B": int(v["B"])} for uid, v in g["bets"].items()},
                                       "side_pots": {"A": int(g["side_pots"]["A"]), "B": int(g["side_pots"]["B"])}}
                            for cid, g in guesses.items()},
                "buy_orders": {oid: dict(o) for oid, o in buy_orders.items()},
                "redeem_counts": {str(uid): int(v) for uid, v in redeem_counts.items()},
                "redeem_orders": redeem_orders[-500:],
                "game_flows": game_flows[-2000:],
                "invite_records": {k: dict(v) for k, v in invite_records.items() if isinstance(v, dict)},
                "invite_pending": {k: v for k, v in invite_pending.items()},  # 待归因：容器重启也不丢
                "invite_confirmed": {k: int(v) for k, v in invite_confirmed.items()},  # deep-link/主动问 锁定的归因
                "join_verify_pending": {k: dict(v) for k, v in join_verify_pending.items() if isinstance(v, dict)},
                "observe_checked": sorted(observe_checked),
                "lurker_checked": sorted(lurker_checked),
                # 入群时间表：观察期巡检 + 潜水号清理的唯一数据源。
                # 此前没持久化，Railway 每次重部署都清零 → 两个巡检永远扫不到人（开关开了也没用）。
                "member_joined_at": {str(cid): {str(uid): float(t) for uid, t in users.items()}
                                     for cid, users in member_joined_at.items()},
                "announce_last_date": announce_last_date,
                "invite_debug": {str(cid): list(v) for cid, v in invite_debug.items()},
                "invite_links": {str(cid): {str(uid): dict(v) for uid, v in users.items()}
                                 for cid, users in invite_links.items()},
                "warn_counts": {str(cid): {str(uid): int(v) for uid, v in users.items()} for cid, users in warn_counts.items()},
                "member_profiles": {str(cid): {str(uid): dict(v) for uid, v in users.items()} for cid, users in member_profiles.items()},
                "whitelist": {str(cid): sorted(users) for cid, users in whitelist.items()},
                "leave_records": {str(cid): v[-100:] for cid, v in leave_records.items()},
                "join_requests": {str(cid): v[-100:] for cid, v in join_requests.items()},
                "admin_logs": admin_logs[-300:],
                "ledger": ledger[-5000:],
                "inherit_daily": {date: {str(cid): {str(uid): v for uid, v in users.items()} for cid, users in cids.items()} for date, cids in inherit_daily.items()},
                "user_first_seen": {str(uid): ts for uid, ts in user_first_seen.items()},
                # 设置快照内嵌进数据：跟着备份/恢复一起走，容器重建后设置不回退
                "_settings": dict(SETTINGS_SNAPSHOT, chat_rules=list(chat_rules),
                                  buy_packages=list(buy_packages),
                                  point_levels=list(sget("POINT_LEVELS")), mall_items=list(sget("MALL_ITEMS")),
                                  redeem_goods=list(redeem_goods)),
                # 群组抽奖：每群活动（含已结束的，方便历史展示）
                "_lotteries": {str(cid): {k: v for k, v in lo.items() if k != "msg_id"}
                               for cid, lo in lotteries.items()},
                # 进行中的红包（lock 不序列化）：不持久化的话重启后未领完的积分凭空消失
                "rp_packets": {pid: {k: v for k, v in p.items() if k != "lock"}
                               for pid, p in rp_packets.items()},
                # 待删消息队列：重启后重放，游戏面板不再因重部署而永久残留
                "pending_deletes": [list(q) for q in _pending_deletes[-2000:]],
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
    global last_business_date, season_active, season_id, season_name, season_start_ts, season_end_ts
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
        # 设置快照：数据文件里内嵌的网页设置，供 load_settings 在 bot_settings.json 缺失时还原
        embedded = data.get("_settings")
        if isinstance(embedded, dict) and embedded.get("fields") and not SETTINGS_SNAPSHOT:
            SETTINGS_SNAPSHOT.update(embedded)
            logger.info("已从数据文件读出内嵌设置快照（%s 项）", len(embedded.get("fields", {})))
    except Exception:
        logger.exception("内嵌设置快照读取失败")
    # 群组抽奖恢复
    try:
        lotteries.clear()
        for cid_s, lo in (data.get("_lotteries") or {}).items():
            try: cid = int(cid_s)
            except (ValueError, TypeError): continue
            if not isinstance(lo, dict): continue
            lo.setdefault("status", "open")
            # 启动时若活动已超时且仍 open → 立即标记 finished（避免重部署后仍显示在进行中）
            if lo["status"] == "open" and time.time() >= lo.get("end_ts", 0):
                lo["status"] = "finished"
            lotteries[cid] = lo
    except Exception:
        logger.exception("抽奖数据恢复失败")
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
        # 红包恢复：必须放在 game_chips 恢复/合并之后，否则退款会被 restore_nested 覆盖。
        # 未过期红包继续可抢；已过期的把剩余金额退回发包人（重启不再丢钱）。
        try:
            rp_packets.clear()
            _now = now_bj().timestamp()
            for pid, p in (data.get("rp_packets") or {}).items():
                if not isinstance(p, dict) or "cid" not in p or "from" not in p:
                    continue
                p["lock"] = asyncio.Lock()
                try:
                    _cid, _from = int(p["cid"]), int(p["from"])
                except (ValueError, TypeError):
                    continue
                _refund = p.get("left_amt", 0) or 0
                if _now - p.get("ts", 0) > 86400 or p.get("left_n", 0) <= 0:
                    if _refund > 0:
                        game_chips[_cid][_from] += _refund
                    continue  # 已过期/已抢完：退款后不入内存
                rp_packets[pid] = p
        except Exception:
            logger.exception("红包数据恢复失败")
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
        for date, cids in data.get("season_exchange_daily", {}).items():
            for cid, users in cids.items():
                for uid, v in users.items():
                    try: season_exchange_daily[str(date)][int(cid)][int(uid)] = int(v)
                    except (ValueError, TypeError): continue
        season_exchange_bonus.clear()
        restore_nested(season_exchange_bonus, data.get("season_exchange_bonus", {}))
        # 累计获得账本 + 累计局数：老存档没有这两个键，留空由 _earn_get 用余额兜底（不会掉级）
        total_earned.clear()
        restore_nested(total_earned, data.get("total_earned", {}))
        games_played.clear()
        restore_nested(games_played, data.get("games_played", {}))
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
        newbie_rewarded.clear()
        for k in (data.get("newbie_rewarded") or {}):
            newbie_rewarded[str(k)] = True
        invite_daily.clear()
        for date, cs in (data.get("invite_daily") or {}).items():
            for cid, us in cs.items():
                for u, v in us.items():
                    invite_daily[str(date)][int(cid)][int(u)] = {
                        "times": int((v or {}).get("times", 0)), "points": int((v or {}).get("points", 0))}
        mall_orders.clear()
        mall_orders.extend(data.get("mall_orders", [])[-200:])
        guesses.clear()
        for cid, g in data.get("guesses", {}).items():
            try:
                _bets = {int(u): {"A": int(v.get("A", 0)), "B": int(v.get("B", 0))}
                         for u, v in (g.get("bets") or {}).items()}
                _pots = g.get("side_pots") or {}
                guesses[int(cid)] = {"q": str(g["q"]), "a": str(g["a"]), "b": str(g["b"]),
                                     "end_ts": float(g["end_ts"]), "locked": bool(g.get("locked")),
                                     "bets": _bets,
                                     "side_pots": {"A": int(_pots.get("A", sum(v["A"] for v in _bets.values()))),
                                                   "B": int(_pots.get("B", sum(v["B"] for v in _bets.values())))},
                                     "msg_id": g.get("msg_id"), "task": None}
            except (KeyError, ValueError, TypeError): continue
        buy_orders.clear()
        for oid, o in data.get("buy_orders", {}).items():
            try: buy_orders[str(oid)] = {"cid": int(o["cid"]), "uid": int(o["uid"]), "amount": int(o["amount"]), "ts": o.get("ts", "")}
            except (KeyError, ValueError, TypeError): continue
        redeem_counts.clear()
        for uid, v in data.get("redeem_counts", {}).items():
            try: redeem_counts[int(uid)] = int(v)
            except (KeyError, ValueError, TypeError): continue
        redeem_orders.clear()
        for o in data.get("redeem_orders", [])[-500:]:
            if isinstance(o, dict): redeem_orders.append(dict(o))
        game_flows.clear()
        for o in data.get("game_flows", [])[-2000:]:
            if isinstance(o, dict): game_flows.append(dict(o))
        invite_records.clear()
        for k, v in data.get("invite_records", {}).items():
            if isinstance(v, dict): invite_records[str(k)] = dict(v)
        invite_pending.update(data.get("invite_pending", {}))
        invite_confirmed.update({str(k): int(v) for k, v in (data.get("invite_confirmed", {}) or {}).items()
                                 if str(v).lstrip("-").isdigit()})
        for k, v in (data.get("join_verify_pending", {}) or {}).items():   # 入群验证待处理（重启不丢）
            if isinstance(v, dict): join_verify_pending[str(k)] = dict(v)
        observe_checked.update(str(x) for x in (data.get("observe_checked", []) or []))
        lurker_checked.update(str(x) for x in (data.get("lurker_checked", []) or []))
        # 入群时间表恢复：与保存侧成对，重部署后观察期巡检/潜水清理才能继续工作
        for cid, users in (data.get("member_joined_at", {}) or {}).items():
            try:
                c = int(cid)
            except (ValueError, TypeError):
                continue
            for uid, ts in (users or {}).items():
                try:
                    member_joined_at[c][int(uid)] = float(ts)
                except (ValueError, TypeError):
                    continue
        # 待删消息队列恢复：重启/重部署后由 restore_pending_deletes 重放，游戏面板不再永久残留
        _pending_deletes[:] = [list(q) for q in (data.get("pending_deletes") or [])
                               if isinstance(q, (list, tuple)) and len(q) in (3, 4)]
        global announce_last_date
        announce_last_date = str(data.get("announce_last_date", "") or "")   # 重启同天不重发公告
        invite_debug.clear()
        for cid, lst in data.get("invite_debug", {}).items():
            invite_debug[int(cid)] = list(lst)[-10:]
        invite_links.clear()
        for cid, users in data.get("invite_links", {}).items():
            for uid, v in users.items():
                # 必须 setdefault：invite_links 即使已是 defaultdict，这里 clear() 后仍是 defaultdict，
                # 但旧的 except(KeyError) 会把类型错误也一并吞掉 → 整表静默丢失（邀请进度恒 0 的真凶）
                try:
                    invite_links.setdefault(int(cid), {})[int(uid)] = dict(v)
                except (ValueError, TypeError):
                    logger.warning("邀请链接恢复跳过异常项 cid=%s uid=%s", cid, uid)
        if not invite_links and data.get("invite_links"):
            logger.warning("邀请链接表恢复后为空，但存档里有 %d 条——请检查恢复逻辑", len(data["invite_links"]))
        for cid, users in data.get("warn_counts", {}).items():
            for uid, v in users.items():
                try: warn_counts[int(cid)][int(uid)] = int(v)
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
        ledger.clear(); ledger.extend(data.get("ledger", [])[-5000:])
        for date, cids in data.get("inherit_daily", {}).items():
            for cid, users in cids.items():
                for uid, v in users.items():
                    try: inherit_daily[str(date)][int(cid)][int(uid)] = int(v)
                    except (ValueError, TypeError): continue
        for uid, ts in data.get("user_first_seen", {}).items():
            try: user_first_seen[int(uid)] = float(ts)
            except (ValueError, TypeError): continue
        AUTHORIZED_GROUPS.update(int(cid) for cid in data.get("authorized_groups", []))
        BOT_ADMINS.clear(); BOT_ADMINS.update(ADMIN_USER_IDS)
        BOT_ADMINS.update(int(x) for x in data.get("bot_admins", []))
        BLACKLISTED_USERS.update(int(x) for x in data.get("blacklist", []))
        for cid, value in data.get("race_jackpot", {}).items(): race_jackpot[int(cid)] = int(value)
        for date, chats in data.get("race_subsidy_by_day", {}).items():
            for cid, amount in chats.items(): race_subsidy_by_day[date][int(cid)] = int(amount)
        for cid, value in data.get("hourly_race_enabled", {}).items(): hourly_race_enabled[int(cid)] = bool(value)
        for cid, value in data.get("race_history", {}).items(): race_history[int(cid)] = list(value)[-10:]
        for cid, value in data.get("blackjack_history", {}).items(): blackjack_history[int(cid)] = list(value)[-10:]
        for cid, value in data.get("race_daily_stats", {}).items(): race_daily_stats[int(cid)] = list(value)[:sget("HORSE_COUNT")]
        for cid, users in data.get("daily_emergency_used", {}).items():
            for uid, used in users.items(): daily_emergency_used[int(cid)][int(uid)] = min(int(used), sget("EMERGENCY_MAX_USES"))
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


def _data_file_status():
    """数据文件状态一行串：路径 + 存在/大小（供启动日志与 /health，让 Volume 是否生效一眼可见）。"""
    try:
        if os.path.exists(DATA_FILE):
            kb = os.path.getsize(DATA_FILE) / 1024
            return f"{DATA_FILE}（{kb:.0f} KB）"
        return f"{DATA_FILE}（不存在，将新建）"
    except Exception:
        return DATA_FILE


logger.info("数据文件：%s", _data_file_status())
load_data()
logger.info("数据加载完成：%s｜授权群 %d 个 · 管理员 %d 名 · 玩家名缓存 %d 条",
            _data_file_status(), len(AUTHORIZED_GROUPS), len(BOT_ADMINS), len(user_names))
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


async def _warm_group_names(app):
    """启动群名预热：把全部授权群的标题拉进 chat_name_cache。

    没有这步时，新部署/没来过消息的群在网页上全是裸群ID或 ?（用户点名要求补群名）。
    单群失败（bot 已不在该群等）只警告不炸，不影响其他群。
    """
    for cid in list(AUTHORIZED_GROUPS):
        if cid in chat_name_cache:
            continue
        try:
            ch = await app.bot.get_chat(cid)
            if getattr(ch, "title", None):
                chat_name_cache[cid] = ch.title
        except Exception:
            logger.warning("群名预热失败 cid=%s（bot 可能已不在该群）", cid)


def _in_bot_loop():
    """当前线程是否就在 bot 主事件循环里。

    用于同步函数判断「能不能跨线程回投」——在循环里跨线程回投同一个循环 = 自己等自己，
    必然等到超时（群管响应慢 8 秒/条的元凶）。
    """
    if not _bot_loop:
        return False
    try:
        return asyncio.get_running_loop() is _bot_loop
    except RuntimeError:
        return False   # 当前线程没有运行中的循环 → 不在 bot 循环里


async def _group_admins_get_async(cid, max_age=300):
    """群主/管理员缓存（5 分钟）·异步版：返回 {uid: "owner"|"admin"}。

    【handler 内必须用这个】直接 await，不走 run_coroutine_threadsafe，
    因此不会出现「循环里等循环」的自锁。bot 不在群/接口失败返回上次缓存或空 dict。
    """
    rec = _group_admins_cache.get(cid)
    now = time.time()
    if rec and now - float(rec[0]) < max_age:
        return rec[1]
    try:
        out = {}
        for a in await _bot_app.bot.get_chat_administrators(cid):
            out[a.user.id] = "owner" if getattr(a, "status", "") == "creator" else "admin"
        _group_admins_cache[cid] = (now, out)
        return out
    except Exception:
        logger.warning("拉取群管理员失败 cid=%s（按无徽章展示）", cid)
    return rec[1] if rec else {}


def _group_admins_get(cid, max_age=300):
    """群主/管理员缓存（5 分钟）·同步版：返回 {uid: "owner"|"admin"}。

    仅供「网页后台线程」等非异步上下文调用（跨线程投递到 bot 循环）。
    若当前已在 bot 主循环里，绝不能跨线程回投（会自锁 8 秒）——
    此时只返回缓存、不主动拉取；需要拉取的异步 handler 请用 _group_admins_get_async。
    """
    rec = _group_admins_cache.get(cid)
    now = time.time()
    if rec and now - float(rec[0]) < max_age:
        return rec[1]
    if _in_bot_loop():
        # 自锁防护：在 bot 循环内不跨线程回投，直接用现有缓存（下次异步路径会刷新）
        return rec[1] if rec else {}
    if _bot_app and _bot_loop:
        try:
            async def _fetch():
                out = {}
                for a in await _bot_app.bot.get_chat_administrators(cid):
                    out[a.user.id] = "owner" if getattr(a, "status", "") == "creator" else "admin"
                return out
            out = asyncio.run_coroutine_threadsafe(_fetch(), _bot_loop).result(8)
            _group_admins_cache[cid] = (now, out)
            return out
        except Exception:
            logger.warning("拉取群管理员失败 cid=%s（按无徽章展示）", cid)
    return rec[1] if rec else {}


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
    # 默认 HTML 解析：模板里的 <b> 生效；解析失败（昵称含 < 等）自动回退纯文本重发
    kwargs.setdefault("parse_mode", "HTML")
    for attempt in range(2):
        try: return await bot.send_message(chat_id=cid, text=text, **kwargs)
        except RetryAfter as exc:
            if attempt == 0: await asyncio.sleep(min(exc.retry_after, 5)); continue
        except BadRequest as exc:
            if "parse entities" in str(exc).lower() and kwargs.get("parse_mode"):
                kwargs.pop("parse_mode"); continue  # HTML 解析炸了 → 纯文本重发
            logger.exception("发送消息失败: %s", cid); break
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
    sent = []
    for index, part in enumerate(split_telegram_text(text)):
        part_kwargs = dict(kwargs)
        if index > 0: part_kwargs.pop("reply_markup", None)  # 只有第一段带键盘，后续段保留 parse_mode
        msg = await safe_send(bot, cid, part, **part_kwargs)
        if msg is None:
            logger.error("长消息发送失败，群 %s，第 %s 段未送达", cid, index + 1)
            return sent or None  # 返回已送达段（供自动删除回收）；全失败仍为 None
        sent.append(msg)
    return sent


async def safe_edit(bot, cid, msg_id, text, **kwargs):
    if not msg_id: return None
    kwargs.setdefault("parse_mode", "HTML")
    try: return await bot.edit_message_text(chat_id=cid, message_id=msg_id, text=text, **kwargs)
    except BadRequest as exc:
        if "parse entities" in str(exc).lower() and kwargs.get("parse_mode"):
            kwargs.pop("parse_mode")
            try: return await bot.edit_message_text(chat_id=cid, message_id=msg_id, text=text, **kwargs)
            except BadRequest as exc2:
                if "Message is not modified" not in str(exc2): logger.warning("编辑消息失败: %s", exc2)
            return None
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
    """删除消息；**遇限流必须重试**，返回 True=已删（或本来就没有），False=这次没删掉。

    2026-09-11 用户报「消息都不自动删除」的两个元凶之一就在这里：
    旧版 `except TelegramError: pass` 把 429（RetryAfter 是 TelegramError 子类）**静默吞掉**，
    而 `_flush_deletes` 随后又无条件把该条目清出队列 → 这条消息**永远删不掉了**。
    现在：429 退避重试最多 3 次；失败返回 False 由调用方（_flush_deletes）重新入队。
    """
    if not msg_id:
        return True
    for attempt in range(3):
        try:
            await bot.delete_message(chat_id=cid, message_id=msg_id)
            return True
        except RetryAfter as exc:
            if attempt == 2:
                return False
            await asyncio.sleep(min(getattr(exc, "retry_after", 1) + 0.5, 25))
        except TelegramError as exc:
            msg = str(exc).lower()
            # 「消息不存在 / 已被删」= 目的已达成，算成功，别反复重排
            for _ok in ("message to delete not found", "message can't be deleted",
                        "message identifier is not specified", "message is not found"):
                if _ok in msg:
                    return True
            logger.warning("删除消息失败 cid=%s mid=%s: %s", cid, msg_id, exc)
            return False
        except Exception:
            return False
    return False


async def _flush_deletes(app):
    """删除队列里所有已到期消息；**删失败的重新入队**（最多重试 5 次），不再静默丢弃。

    旧版无条件 `_pending_deletes[:] = [未到期]`，把删失败的条目一并清出 → 消息永久残留。
    """
    now = time.time()
    due = [q for q in _pending_deletes if q[2] <= now]
    if not due:
        return
    retry = []
    for q in due:
        try:
            cid, mid = int(q[0]), int(q[1])
        except (ValueError, TypeError, IndexError):
            continue
        tries = int(q[3]) if len(q) > 3 else 0
        if not await safe_delete(app.bot, cid, mid) and tries + 1 < 5:
            retry.append([cid, mid, now + 120, tries + 1])   # 2 分钟后再试
    _pending_deletes[:] = [q for q in _pending_deletes if q[2] > now] + retry


def restore_pending_deletes(app):
    """启动重放：把上次没删完的消息重新排程。已过期的立即补删，超过 1 天的陈条目直接丢弃。"""
    if not _pending_deletes:
        return
    now = time.time()
    old, _pending_deletes[:] = list(_pending_deletes), []
    for q in old:
        try:
            cid, mid, due = int(q[0]), int(q[1]), float(q[2])
        except (ValueError, TypeError, IndexError):
            continue
        if now - due > 86400:
            continue
        if due <= now:
            async def _del_now(_cid=cid, _mid=mid):
                await safe_delete(app.bot, _cid, _mid)
            try:
                t = asyncio.create_task(_del_now())
                _delete_tasks.add(t)
                t.add_done_callback(_delete_tasks.discard)
            except RuntimeError:
                _pending_deletes.append([cid, mid, due])   # 无 loop：退回队列等周期兜底
        else:
            schedule_delete_ids(app, cid, [mid], int(due - now) + 1)
    logger.info("已恢复 %d 条待删消息的删除排程", len(old))


def schedule_delete_ids(app, cid, ids, seconds):
    """延迟删除指定 message_id（用于只有 id、拿不到 Message 对象的场景，如原地编辑的下注面板）。

    队列随 bot_data 持久化：容器重启/重部署后由 restore_pending_deletes 重放，
    不再出现「消息说好自动删、重部署后永久残留」的问题。
    """
    if seconds <= 0 or not ids: return
    if isinstance(ids, int): ids = [ids]
    ids = [int(i) for i in ids if i]
    if not ids: return
    due = time.time() + int(seconds)
    for mid in ids:
        _pending_deletes.append([cid, mid, due])
    if len(_pending_deletes) > 5000:
        del _pending_deletes[:-2000]   # 防异常堆积
    async def _del_later():
        await asyncio.sleep(seconds)
        await _flush_deletes(app)
    try:
        t = asyncio.create_task(_del_later())
        _delete_tasks.add(t)
        t.add_done_callback(_delete_tasks.discard)
    except RuntimeError:
        pass   # 无事件循环（如网页线程调用）：条目已在队列，由周期兜底/启动重放接管


def schedule_delete(app, cid, msgs, seconds):
    """seconds 秒后自动删除 bot 发出的消息（0=不删）。msgs 可为单条 Message 或 Message 列表。
    用于：查询类回复（REPLY_DELETE_SECONDS）、游戏结算消息（SETTLE_DELETE_SECONDS）。"""
    if seconds <= 0 or not msgs: return
    if not isinstance(msgs, (list, tuple)): msgs = [msgs]
    ids = [m.message_id for m in msgs if m is not None and getattr(m, "message_id", None)]
    schedule_delete_ids(app, cid, ids, seconds)


async def send_settle(app, cid, text, kb=None, parse_mode="HTML", delete_after=None):
    """【新游戏必用】游戏结算/收尾消息统一出口：发送 + 自动按 SETTLE_DELETE_SECONDS 回收。

    以后写任何新游戏，结算消息一律走这个函数，别直接 reply_text/safe_send——
    结算自动删除在这里是默认行为，不用（也不会忘）另写 schedule_delete。
    回收时长由网页「通用与应急 → 游戏结算消息自动删除(秒)」控制，设 0 = 永久保留。
    """
    secs = int(sget("SETTLE_DELETE_SECONDS") if delete_after is None else delete_after)
    kwargs = {"parse_mode": parse_mode}
    if kb is not None:
        kwargs["reply_markup"] = kb
    msgs = await safe_send_long(app.bot, cid, text, **kwargs)
    if msgs and secs > 0:
        schedule_delete(app, cid, msgs, secs)
    return msgs


async def send_settle_rank(app, cid, lines):
    """【结算榜单专用】把「累计盈利榜」单独发一条消息。

    2026-09-11 用户要求：「把所有游戏的结算画面中的（累计盈利榜）拆开发，不然一个界面太长了，
    有点刷屏的感觉」——结算正文保持精简，榜单另起一条，同样走 SETTLE_DELETE_SECONDS 回收。
    lines 为已渲染好的行列表；为空/None 则一条都不发（无榜单就不产生空白消息）。
    """
    if not lines: return None
    return await send_settle(app, cid, "\n".join(lines))


async def send_reply(update, context, text, kb=None, parse_mode=None, delete_after=None):
    """【查询类命令必用】查询回复统一出口：发送 + 自动按 REPLY_DELETE_SECONDS 回收。

    以后写任何查询类命令（积分/战绩/排行/商城等），回复一律走这里——
    回复自动删除是默认行为，不用（也不会忘）另写 schedule_delete。
    时长由网页「积分系统 → 积分设置 → 查询回复自动删除(秒)」控制，0 = 永久保留。
    注意：用户发的命令本身按 POINTS_DELETE_SECONDS 在 _dispatch_alias 全局统一删，无需关心。
    """
    secs = int(sget("REPLY_DELETE_SECONDS") if delete_after is None else delete_after)
    kwargs = {}
    if parse_mode is None:
        parse_mode = "HTML"   # 默认 HTML：<b>/<code> 生效；解析失败自动回退纯文本
    if parse_mode:
        kwargs["parse_mode"] = parse_mode
    if kb is not None:
        kwargs["reply_markup"] = kb
    target = getattr(update, "message", None)
    if target is None:
        # 按钮触发（CallbackQuery）没有可回复的消息 → 发到群里，**同样走 REPLY_DELETE_SECONDS**。
        # 2026-09-11 补：此前按钮触发的查询（如「排位榜」）直接 safe_send_long，永不回收。
        msg = await safe_send_long(context.application.bot, update.effective_chat.id, text, **kwargs)
        if msg and secs > 0:
            schedule_delete(context.application, update.effective_chat.id, msg, secs)
        return msg
    try:
        reply = await target.reply_text(text, **kwargs)
    except BadRequest as exc:
        if "parse entities" in str(exc).lower() and kwargs.get("parse_mode"):
            kwargs.pop("parse_mode")  # 昵称含 < 等导致解析炸 → 纯文本重发
            reply = await target.reply_text(text, **kwargs)
        else:
            raise
    if reply and secs > 0:
        schedule_delete(context.application, update.effective_chat.id, reply, secs)
    return reply


def card_str(card):
    raw = Card.int_to_pretty_str(card).strip("[]")
    suit = {"♠":"♠️", "♥":"♥️", "♦":"♦️", "♣":"♣️"}.get(raw[-1], raw[-1])
    return f"{suit}{raw[:-1].replace('T', '10')}"


async def action_notice(cid, app, uid, desc):
    """游戏内「下注/加注/比牌」等即时提示：发一条、10 秒后删。

    **必须走 schedule_delete_ids**（持 task 引用 + 队列持久化 + 60s 兜底）——
    旧版裸 `asyncio.create_task(delete_later())` 不保存引用，任务可能在跑完前被事件循环 GC，
    「说好 10 秒删」的提示就永远留在群里（2026-09-11 用户报「消息都不自动删除」的元凶之一）。
    """
    message = await safe_send(app.bot, cid, f"🎲 {await get_name(app, uid)} {desc}")
    schedule_delete_ids(app, cid, message.message_id if message else None, 10)


def schedule_notice_delete(app, cid, message, kind="panel"):
    """给机器人「提示/播报」类消息挂后台自动回收（2026-09-11 用户报「超时自动过牌」「亮牌」等不删）。

    kind="panel"  过程类（超时自动行动提示、亮牌按钮卡、比牌公告）→ PANEL_DELETE_SECONDS
    kind="settle" 结算类播报（亮牌收池播报、结算失败提示）→ SETTLE_DELETE_SECONDS
    秒数为 0 表示不删（与后台设置语义一致）；message 为空时静默跳过。
    """
    if not message:
        return
    secs = sget("SETTLE_DELETE_SECONDS") if kind == "settle" else sget("PANEL_DELETE_SECONDS")
    try:
        secs = int(secs or 0)
    except (TypeError, ValueError):
        secs = 0
    if secs > 0:
        schedule_delete(app, cid, message, secs)


def ledger_add(cid, frm, to, amt, typ):
    """资金流台账：红包领取/转赠等人对人转移逐笔记账（防小号审查用，留 5000 条）。"""
    ledger.append({"ts": now_bj().strftime("%Y-%m-%d %H:%M"), "cid": cid, "frm": frm, "to": to, "amt": amt, "typ": typ})
    if len(ledger) > 5000: del ledger[:len(ledger) - 5000]


def calc_rake(nets):
    """计算抽水（纯计算不扣款）：对赢家净赢按 RAKE_PERCENT% 抽成。返回 (总抽水, {uid: 金额})。"""
    if not sget("RAKE_ENABLED") or sget("RAKE_PERCENT") <= 0:
        return 0, {}
    rake_total, rake_per = 0, {}
    for uid, net in (nets or {}).items():
        if not isinstance(uid, int) or uid <= 0 or net <= 0:
            continue
        if net < sget("RAKE_MIN_NET"):
            continue
        amt = int(net * sget("RAKE_PERCENT") / 100)
        if amt <= 0:
            continue
        rake_per[uid] = amt
        rake_total += amt
    return rake_total, rake_per


async def commit_rake(app, cid, rake_per, label):
    """抽水落账：从钱包扣除 + 写台账。不再单独发群消息——抽水在结算面板里直接体现为「实收」。

    修复（P1④ 记账边界）：此前先 max(0, 余额-抽水) 扣款、却把**应抽金额**写进台账，
    余额不足时（结算与抽水之间有 await，玩家可能已转出/被并发扣款）会出现
    「台账记了 X、钱包只扣了 Y<X」的账实不符。现在按**实际扣到的金额**记账，
    余额不足时少收多少就记多少，台账与钱包永远一致。
    """
    if not rake_per:
        return 0
    total = 0
    for uid, amt in rake_per.items():
        try:
            amt = int(amt or 0)
        except (TypeError, ValueError):
            continue
        if amt <= 0:
            continue
        async with wallet_locks[uid]:
            bal = int(game_chips[cid].get(uid, 0) or 0)
            real = min(amt, bal) if bal > 0 else 0
            if real <= 0:
                logger.warning("抽水跳过：cid=%s uid=%s 余额 %s 不足以支付抽水 %s（%s）", cid, uid, bal, amt, label)
                continue
            game_chips[cid][uid] = bal - real
        ledger_add(cid, uid, 0, real, f"抽水-{label}")
        total += real
    if total:
        save_data()
    return total


def record_game_flows(cid, nets, typ):
    """一局游戏的人对人净转移记入 game_flows（资金流审查页可见，防"通过游戏故意输牌送分"）。

    nets: {uid: 本局净输赢}（正=赢，负=输）。牌局是池模式，无法精确知道谁输给谁，
    按惯例分摊：每个输家的损失按赢家净赢比例折算成 输家→赢家 流向（二人局=精确值）。
    只记真实用户（uid>0）；全输（奖池沉没）/全赢/打平无人对人转移不记。
    21点/赛车是对庄家局，不存在人对人转移，不接此记账。
    """
    losers = {u: -n for u, n in nets.items() if u > 0 and n < 0}
    winners = {u: n for u, n in nets.items() if u > 0 and n > 0}
    if not losers or not winners:
        return
    lose_total = sum(losers.values())
    ts = now_bj().strftime("%Y-%m-%d %H:%M")
    for w, w_net in winners.items():
        for l, l_loss in losers.items():
            amt = int(l_loss * w_net // lose_total)
            if amt > 0:
                game_flows.append({"ts": ts, "cid": cid, "frm": l, "to": w, "amt": amt, "typ": typ})
    del game_flows[:-2000]


async def broadcast_big_win(app, cid, uid, game_name, net, detail=""):
    """大奖战报：单局净赢超阈值时推送到其他授权群（排除事发群），制造全群气氛。"""
    try:
        if not sget("BROADCAST_ENABLED") or net < max(1, sget("BROADCAST_MIN_AMOUNT")): return
        if cid not in AUTHORIZED_GROUPS: return
        name = await get_name(app, uid, cid=cid)
        extra = f"\n{detail}" if detail else ""
        text = (f"📣 <b>战报快讯</b>\n{game_name}｜{html.escape(name)} 单局豪赢 <b>{net}</b> 积分{extra}")
        for g in AUTHORIZED_GROUPS:
            if g == cid: continue
            await safe_send(app.bot, g, text, parse_mode="HTML")
    except Exception:
        logger.exception("大奖战报广播失败（不影响结算）")


async def emergency_if_needed(cid, uid, app, wallet=None, poker=None):
    used = daily_emergency_used[cid][uid]
    wallet = wallet or game_chips
    if wallet[cid][uid] != 0 or used >= sget("EMERGENCY_MAX_USES"): return False
    # 参与门槛：纯靠归零白嫖的小号不给（本群累计玩过 EMERGENCY_MIN_GAMES 局才发）
    if int(sget("EMERGENCY_MIN_GAMES") or 0) > 0 and int(games_played[cid][uid] or 0) < int(sget("EMERGENCY_MIN_GAMES")):
        return False
    wallet[cid][uid] = sget("EMERGENCY_CHIPS")
    if poker and uid in poker.chips: poker.chips[uid] += sget("EMERGENCY_CHIPS")
    _earn_add(cid, uid, sget("EMERGENCY_CHIPS"))   # 归零赠送属于「白给分」，计入累计获得
    daily_emergency_used[cid][uid] = used + 1; save_data()
    remaining = sget("EMERGENCY_MAX_USES") - daily_emergency_used[cid][uid]
    schedule_notice_delete(app, cid, await safe_send(app.bot, cid, f"🆘 {await get_name(app, uid)} 积分归零，已赠送 {sget('EMERGENCY_CHIPS')} 应急积分（今日已补充 {daily_emergency_used[cid][uid]}/{sget('EMERGENCY_MAX_USES')} 次，剩余 {remaining} 次）。"))
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
        self.deck = [r + s for r in "23456789TJQKA" for s in "shdc"] * sget("BLACKJACK_DECKS")
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
            self.deck = [r + s for r in "23456789TJQKA" for s in "shdc"] * sget("BLACKJACK_DECKS")
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


def _season_rule(game, daily_val, season_val):
    """排位赛独立参数取值：排位局且排位参数非 0 时用排位值，否则沿用日常德州的值。

    约定 SEASON_* = 0 表示「沿用日常」，这样新增参数不需要迁移旧设置。
    盲注/前注本身允许为 0（不设），0 与「沿用日常」语义冲突，
    故盲注类单独走 _season_blind。
    """
    return season_val if (getattr(game, "season", False) and season_val) else daily_val


def _season_blind(game, daily_val, season_val):
    """盲注/前注专用：排位局且「排位盲注类参数被管理员显式设过」时用排位值，否则沿用日常。

    判定口径：排位小盲/大盲/前注任一 > 0，就说明管理员在后台填了排位专用盲注，
    此时三个值整体按排位参数走（填 0 的项即「排位局该项为 0」）。
    全部为 0 = 没动过 → 沿用日常德州。
    """
    if getattr(game, "season", False) and (sget("SEASON_SMALL_BLIND") or sget("SEASON_BIG_BLIND") or sget("SEASON_ANTE")):
        return season_val
    return daily_val


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

    # ---------- 规则参数（排位局可独立配置，0/未填 = 沿用日常德州） ----------
    @property
    def min_raise(self):
        """最低加注额。"""
        return _season_rule(self, sget("FIXED_MIN_RAISE"), sget("SEASON_FIXED_MIN_RAISE"))

    @property
    def turn_timeout(self):
        """单回合思考时间（秒）。"""
        return _season_rule(self, sget("TURN_TIMEOUT"), sget("SEASON_TURN_TIMEOUT"))

    @property
    def wait_timeout(self):
        """等待房倒计时（秒）。"""
        return _season_rule(self, sget("ROOM_WAIT_TIMEOUT"), sget("SEASON_ROOM_WAIT_TIMEOUT"))

    @property
    def ante_value(self):
        """前注。"""
        return _season_blind(self, sget("ANTE"), sget("SEASON_ANTE"))

    @property
    def small_blind_value(self):
        """小盲注。"""
        return _season_blind(self, sget("SMALL_BLIND"), sget("SEASON_SMALL_BLIND"))

    @property
    def big_blind_value(self):
        """大盲注。"""
        return _season_blind(self, sget("BIG_BLIND"), sget("SEASON_BIG_BLIND"))

    def add(self, uid):
        if self.phase != "waiting" or uid in self.players: return False
        if self.season:
            # 排位赛：必须已报名、且排位分 > 0（可选再加一道「入座最低排位分」门槛）
            if uid not in season_joined.get(self.chat_id, set()):
                return False
            wallet = season_points
            if wallet[self.chat_id][uid] <= 0: return False
            if sget("SEASON_MIN_ENTRY_CHIPS") and wallet[self.chat_id][uid] < sget("SEASON_MIN_ENTRY_CHIPS"): return False
        else:
            wallet = game_chips
            if wallet[self.chat_id][uid] < sget("MIN_ENTRY_CHIPS"): return False
        self.players.append(uid); self.chips[uid] = wallet[self.chat_id][uid]; self.total_bet[uid] = 0
        return True

    def start(self):
        if len(self.players) < 2: return False
        random.shuffle(self.players)
        self.cancel_auto(); self.cancel_wait(); self.folded.clear(); self.all_in.clear(); self.acted.clear(); self.raise_locked.clear(); self.board = []; self.pot = 0; self.settled = False
        wallet = season_points if self.season else game_chips
        _ante = self.ante_value
        for uid in self.players:
            self.chips[uid] = wallet[self.chat_id][uid]; self.initial_chips[uid] = self.chips[uid]
            self.total_bet[uid] = self.round_bets[uid] = 0
            ante = min(_ante, self.chips[uid]); self.chips[uid] -= ante; self.total_bet[uid] += ante; self.pot += ante
            if not self.chips[uid]: self.all_in.add(uid)
        # 排位赛：单局每人投入上限 = 本局落座玩家带入筹码总和 × 百分比（人少上限低，防串通）
        self.max_total_bet = max(int(sum(self.initial_chips.values()) * SEASON_BET_PERCENT), _ante) if self.season else None
        self.deck = [Card.new(rank + suit) for rank in "23456789TJQKA" for suit in "shdc"]
        random.shuffle(self.deck); self.hands = {uid: [self.deck.pop(), self.deck.pop()] for uid in self.players}
        self.dealer_idx = len(self.players) - 1; self.active = self.players.copy()
        # 盲注位（2026-09-11 按官方规则核对修正）：
        #   3 人及以上：小盲 = 庄家左边第一位、大盲 = 庄家左边第二位；
        #   **单挑（2 人）：按钮位本身就是小盲**，另一位是大盲。
        #   原实现两人时「大盲」落在庄家自己身上（既当按钮又下大盲），
        #   且翻牌后从大盲位先动 —— 与官方「单挑翻牌后大盲（非按钮）先动」相反。
        _n = len(self.players)
        if _n == 2:
            sb_uid, bb_uid = self.players[self.dealer_idx], self.players[(self.dealer_idx + 1) % _n]
        else:
            sb_uid = self.players[(self.dealer_idx + 1) % _n]
            bb_uid = self.players[(self.dealer_idx + 2) % _n]
        self._blind(sb_uid, self.small_blind_value)
        self._blind(bb_uid, self.big_blind_value)
        # 跟注基准（2026-09-11 修正）：**短全下的盲注不降低跟注额**——
        # 大盲筹码不足时，其他人仍需按完整大盲跟注；原实现取 max(round_bets)
        # 会低于大盲值，导致全场少跟注。盲注为 0 时行为不变。
        self.current_bet = max(self.big_blind_value, max(self.round_bets.values()))
        self.phase = "preflop"
        self.actor_idx = (self.players.index(bb_uid) + 1) % len(self.active)
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
                if raise_size < self.min_raise:
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
            if extra < self.min_raise: return False, f"最低加注为 {self.min_raise}"
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
    return f"{prefix}\n发起人：{await get_name(app, game.owner_id)}\n\n已加入：\n" + "\n".join(players) + f"\n\n点击加入，发起人可立即开始。\n⏰ 满 2 人后 {game.wait_timeout} 秒自动开局，不足 2 人 {game.wait_timeout} 秒后自动解散。"


async def update_poker_waiting(game, app):
    rows = [[InlineKeyboardButton("📥 加入游戏", callback_data="texas_join")]]
    if len(game.players) >= 2: rows.append([InlineKeyboardButton("🎮 开始游戏", callback_data="texas_start")])
    rows.append([InlineKeyboardButton("❌ 终止房间", callback_data="texas_end")])
    await safe_edit(app.bot, game.chat_id, game.game_msg_id, await poker_waiting_text(game, app), reply_markup=InlineKeyboardMarkup(rows))


def _poker_quick_amounts(game, uid):
    """行动金额计算：poker_buttons 的加注/半池/全池按钮共用一份计算（防两处漂移）。
    返回 (to_call, min_raise, half, pot)。"""
    _min_raise = game.min_raise   # 排位局可能用独立的最低加注额
    half_amt = max(_min_raise, game.pot // 2)
    pot_amt = max(_min_raise, game.pot)
    to_call = max(0, game.current_bet - game.round_bets[uid])
    return to_call, _min_raise, half_amt, pot_amt


async def poker_table_text(game, app):
    phase = {"preflop":"翻牌前", "flop":"翻牌圈", "turn":"转牌圈", "river":"河牌圈"}.get(game.phase, game.phase)
    lines = [
        f"{'🏆 排位赛｜' if game.season else '🃏 积分德州'}｜{phase}",
        f"🃏 公牌：{'  '.join(card_str(card) for card in game.board) or '未发牌'}",
        f"💰 奖池 {game.pot}｜下注 {game.current_bet}",
    ]
    current = game.current()
    lines.append("━━━━━━━━━━━━━━━━━")
    if current:
        # 2026-09-11 用户要求：行动提示放到分隔线之后、玩家列表之前（分隔线 = 牌面/行动区的分界）；
        # 并与「请在N秒内行动」合并成一行（原两句重复且不显眼）
        _need = max(0, game.current_bet - game.round_bets[current])
        lines.append(f"⏳ <b>{await get_name(app, current)}</b> 行动中｜需跟 {_need}｜{game.turn_timeout} 秒未操作自动过牌/弃牌")
    # 玩家行两段式（2026-09-10 用户报「文本不对齐」）：名字长短不定，把 状态/投/余 挪到第二行
    # 统一格式后天然左对齐；名字再长也不挤压后面的字段。
    # 2026-09-11 用户要求：👉 留在行首，非行动者补 3 个半角空格占位 → 所有行序号落在同一列
    for index, uid in enumerate(game.players, 1):
        status = "❌ 弃牌" if uid in game.folded else "🔥 全下" if uid in game.all_in else "🟢 在局"
        mark = "👉 " if uid == current else "   "
        lines.append(f"{mark}{index}. {await get_name(app, uid)}")
        lines.append(f"　　{status}｜投{game.total_bet[uid]}｜余{game.chips[uid]}")
    return "\n".join(lines)


def poker_buttons(game, uid):
    acting = (uid == game.current() and uid not in game.folded and uid not in game.all_in)
    if not acting:
        return InlineKeyboardMarkup([[InlineKeyboardButton("🃏 查看手牌", callback_data="texas_hand")]])
    to_call = max(0, game.current_bet - game.round_bets[uid])
    # 2026-09-11 用户要求撤销「emoji+2字」改造：按钮恢复带金额旧样式（快捷档行已删）
    # 2026-09-11 用户要求（防误触）：过牌/跟注上移到首行右侧（高频且顺手），
    # 弃牌下移到第二行最左——与高频键拉开距离，避免手滑点错直接出局。
    act_btn = InlineKeyboardButton("✅ 过牌" if not to_call else "✅ 跟注",
                                   callback_data="texas_check" if not to_call else "texas_call")
    fold_btn = InlineKeyboardButton("❌ 弃牌", callback_data="texas_fold")
    rows = [[InlineKeyboardButton("🃏 手牌", callback_data="texas_hand"), act_btn]]
    if uid not in game.raise_locked:
        # 半池/全池快捷加注：加注金额=底池的 1/2 或 1 倍；不足最小加注时按最小加注兜底
        _tc, _min_raise, half_amt, pot_amt = _poker_quick_amounts(game, uid)
        row_act = [fold_btn]
        if game.chips[uid] >= to_call + _min_raise and half_amt > _min_raise:
            row_act.append(InlineKeyboardButton(f"🚀 加注 {_min_raise}", callback_data=f"texas_raise_{_min_raise}"))
        rows.append(row_act)
        row_p = []
        if half_amt < pot_amt and game.chips[uid] >= to_call + half_amt:
            row_p.append(InlineKeyboardButton(f"💰 半池 {half_amt}", callback_data="texas_raise_half"))
        if game.chips[uid] >= to_call + pot_amt:
            row_p.append(InlineKeyboardButton(f"💰 全池 {pot_amt}", callback_data="texas_raise_pot"))
        if row_p: rows.append(row_p)
    else:
        rows.append([fold_btn])
    if game.chips[uid] > 0:
        rows.append([InlineKeyboardButton(f"🔥 全下 {game.chips[uid]}", callback_data="texas_allin")])
    return InlineKeyboardMarkup(rows)


async def update_poker_table(game, app):
    # 游戏开始后：把等待房消息直接编辑成牌桌（不删除；操作按钮在行动消息里）
    await safe_edit(app.bot, game.chat_id, game.game_msg_id, await poker_table_text(game, app), reply_markup=None, parse_mode="HTML")


async def start_turn_timer(game, app):
    game.cancel_timer()
    uid = game.current()
    if uid is None:
        if game.phase == "showdown": await settle_poker(game, app)
        return
    # 行动消息携带完整牌桌 + 行动提示 + 操作按钮（一条消息）
    await safe_delete(app.bot, game.chat_id, game.action_msg_id)
    # 行动提示已并入牌桌文本（见 poker_table_text），此处不再追加第二句
    text = await poker_table_text(game, app)
    msg = await safe_send(app.bot, game.chat_id, text, reply_markup=poker_buttons(game, uid), parse_mode="HTML")
    game.action_msg_id = msg.message_id if msg else None

    # 真实超时任务：无需跟注自动过牌，否则自动弃牌，防止牌局卡死
    async def timeout_action():
        await asyncio.sleep(game.turn_timeout)
        if game.settled or game.phase == "showdown": return
        if game.current() != uid: return  # 该玩家已行动过
        if game.round_bets[uid] == game.current_bet:
            ok, _ = game.action(uid, "check")
            if not ok: game.action(uid, "fold")
            desc = "超时自动过牌"
        else:
            game.action(uid, "fold")
            desc = "超时自动弃牌"
        await schedule_notice_delete(app, game.chat_id,
                                     await safe_send(app.bot, game.chat_id, f"⏰ {desc}：{await get_name(app, uid)}"))
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
                if uid in game.folded: lines.append(f"　{names[uid]}：弃牌")
                else: lines.append(f"　{names[uid]}：{'  '.join(card_str(card) for card in game.hands[uid])}｜{hand_types.get(uid, '')}")
        else:
            lines.append("亮牌牌型：")
            for uid in game.players:
                if uid not in game.folded: lines.append(f"　{names[uid]}：未亮牌")
                else: lines.append(f"　{names[uid]}：弃牌")
        lines.append("")

        lines.append("派奖：")
        for uid, hand, amount, details, _ in sorted(result, key=lambda item: item[2], reverse=True):
            lines.append(f"　{names[uid]}：{hand}｜+{amount}（{'，'.join(f'{pool}+{value}' for pool, value in details)}）")
        
        # 抽水先算（官方模式），面板「盈亏」行直接带实收；资金流审查同源
        _nets = {uid: game.chips[uid] - game.initial_chips[uid] for uid in game.players} \
            if (game.mode == "official" and not game.season) else {}
        rake_per = calc_rake(_nets)[1] if _nets else {}

        lines.append("投入 / 盈亏：")
        for uid in game.players:
            net = game.chips[uid] - game.initial_chips[uid]
            if game.season:
                pass  # 排位分已在 showdown 写回 season_points，不写当日榜
            elif game.mode == "official":
                poker_profit_by_date[date][game.chat_id][uid] += net
            r_amt = rake_per.get(uid, 0)
            r_txt = f"（实收 {net - r_amt}，含抽水{r_amt}）" if r_amt else ""
            lines.append(f"　{names[uid]}：投入 {game.total_bet[uid]}｜盈亏 {net:+d}{r_txt}")
        lines.append("")

        # 资金流审查：官方模式把本局人对人净转移记账（防"故意输牌送分"）；排位分不记
        if game.mode == "official" and not game.season:
            record_game_flows(game.chat_id, _nets, "德州")
            await commit_rake(app, game.chat_id, rake_per, "德州")

        # 官方局：累计参与局数（归零赠送门槛）+ 赢分计入累计获得 + 升级通知
        if game.mode == "official" and not game.season:
            for uid in game.players:
                if uid < 0: continue
                games_played[game.chat_id][uid] += 1
                # 实际到手 = 净赢 - 本局抽水（抽水已在上面扣除），记账才与实际余额一致
                _gain = (game.chips[uid] - game.initial_chips.get(uid, 0)) - int(rake_per.get(uid, 0) or 0)
                if _gain > 0:
                    _oe = _earn_get(game.chat_id, uid)
                    _earn_add(game.chat_id, uid, _gain)
                    await _check_level_change(app, game.chat_id, uid, _oe, _earn_get(game.chat_id, uid))

        # 大奖战报：官方模式单局净赢超阈值 → 广播其他授权群（排位赛不播）
        if game.mode == "official" and not game.season:
            top_uid, top_net = None, 0
            for uid in game.players:
                _n = game.chips[uid] - game.initial_chips[uid]
                if _n > top_net: top_uid, top_net = uid, _n
            if top_uid: await broadcast_big_win(app, game.chat_id, top_uid, "🃏 德州扑克", top_net)

        # 排位赛：累计局数 + 破产应急补分（已取消淘汰；赛季已结束的进行中牌局只正常派奖、不计入、不误判破产）
        if game.season and season_active:
            for p in game.players:
                if p < 0: continue
                season_games[game.chat_id][p] += 1
            for p in game.players:
                if p < 0: continue
                if season_points[game.chat_id][p] <= 0:
                    if season_rebuy[game.chat_id][p] < sget("SEASON_REBUY_COUNT"):
                        season_rebuy[game.chat_id][p] += 1
                        season_points[game.chat_id][p] = sget("SEASON_REBUY_AMOUNT")
                        lines.append(f"⚠️ {names[p]} 破产，启用应急筹码 +{sget('SEASON_REBUY_AMOUNT')}（剩 {sget('SEASON_REBUY_COUNT') - season_rebuy[game.chat_id][p]} 次）")
            # 排位赛跨午夜补重置：本局横跨业务日结束，错过的午夜刷新在此补记当日盈亏并归位到基准分
            if game.start_date and business_date() != game.start_date:
                for uid in game.players:
                    if uid < 0: continue
                    base = _season_base(game.chat_id, uid)
                    final = season_points[game.chat_id][uid]
                    day_profit = final - base
                    if day_profit:
                        season_profit_by_date[game.start_date][game.chat_id][uid] += day_profit
                    season_points[game.chat_id][uid] = base
                    # 已取消淘汰机制：破产玩家当日剩余时间无法下注，次日 0 点重置为「起始分+兑换底分」后可继续参赛

        # 累计盈利榜单独发一条（2026-09-11 用户要求：结算正文太长像刷屏，榜单拆开发）
        _rank_lines = None
        if game.mode == "official" and not game.season:
            rank = sorted(poker_profit_by_date[date][game.chat_id].items(), key=lambda item: item[1], reverse=True)[:50]
            if rank:
                _rank_lines = ["🏆 <b>当日德州累计盈利榜</b>", "━━━━━━━━━━━━━━━━━"]
                _rank_lines.extend([f"{rank_marker(index)} {names.get(uid) or await get_name(app, uid)}：{amount:+d}" for index, (uid, amount) in enumerate(rank, 1)])
            
        delivered = await safe_send_long(app.bot, game.chat_id, "\n".join(lines), parse_mode="HTML")
        if sget("SETTLE_DELETE_SECONDS") > 0:
            schedule_delete(app, game.chat_id, delivered, sget("SETTLE_DELETE_SECONDS"))
        await send_settle_rank(app, game.chat_id, _rank_lines)
        # 牌桌卡片此前结算后一直留在群里，结束后延迟清理
        schedule_delete_ids(app, game.chat_id, game.game_msg_id, sget("PANEL_DELETE_SECONDS"))
        # 单赢场景（只剩一人未弃牌）：提供可选亮牌按钮，尊重德州 muck 规则，不强制亮牌
        if len(game.showdown_order) <= 1:
            winner = game.showdown_order[0] if game.showdown_order else None
            if winner is not None and game.hands.get(winner):
                btn = await safe_send(app.bot, game.chat_id,
                    "💡 本局单挑收池，赢家可选择亮出底牌：",
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🃏 亮牌", callback_data="texas_reveal")]]))
                schedule_notice_delete(app, game.chat_id, btn)
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
            schedule_notice_delete(app, game.chat_id, await safe_send(app.bot, game.chat_id, "⚠️ 德州已完成结算，但详细结算消息发送失败。"), kind="settle")
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
    _reveal_msg = await safe_send(context.bot, cid,
        f"🃏 <b>{name} 亮牌</b>：{hand_text}\n🃏 公牌：{board_text}（收全部底池）",
        parse_mode="HTML")
    schedule_notice_delete(context.application, cid, _reveal_msg, kind="settle")
    rid = info.get("reveal_msg_id")
    if rid:
        await safe_edit(context.bot, cid, rid, "🃏 已亮牌", reply_markup=None)
        # 亮完牌的按钮卡片同样回收（之前编辑成「已亮牌」后就永久留在群里）
        _rid_secs = int(sget("PANEL_DELETE_SECONDS") or 0)
        if _rid_secs > 0:
            schedule_delete_ids(context.application, cid, rid, _rid_secs)
    # 仅移除本条亮牌记录，其余未亮牌的单赢保留
    recent_poker_reveals[cid] = [it for it in infos if it is not info]
    if not recent_poker_reveals[cid]:
        recent_poker_reveals.pop(cid, None)
    await q.answer("已亮牌")


# ==================== 赛车 ====================
class HorseRace:
    def __init__(self, cid, owner, jackpot, mode=None, auto=False):
        self.chat_id, self.owner_id, self.jackpot = cid, owner, jackpot
        self.mode = mode or current_game_mode()
        # 开赛来源：True=定时自动开赛（可享系统加奖）；False=群友/管理员手动发起（不派奖，2026-09-11 用户要求）
        self.auto_started = bool(auto)
        self.bets, self.total_bets, self.pool = defaultdict(dict), [0] * sget("HORSE_COUNT"), 0
        self.phase, self.create_time, self.positions, self.arrivals = "betting", time.time(), [0.0] * sget("HORSE_COUNT"), []
        self.display_positions = [0] * sget("HORSE_COUNT")  # 显示格（=节奏曲线进度的整数部分，严格跟随真实进度）
        self.arrival_times, self.race_start_time = {}, None
        self.notified, self.name_cache = set(), {}
        self.game_msg_id = self.animation_msg_id = None
        self.task, self.settled, self.cancelled, self.lock = None, False, False, asyncio.Lock()
        self.final_odds = None
        self.bet_odds = defaultdict(dict)  # 每注下注瞬间锁定的赔率（uid->horse 金额加权平均）
        self.panel_cd = 0.0  # 看板重发冷却：重复发 /赛车 时避免刷屏（未超时只回一句文字）
        rates = [random.uniform(.18, .35) for _ in range(sget("HORSE_COUNT"))]
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
        avg = 1.0 / sget("HORSE_COUNT")
        raw = []
        for i in range(sget("HORSE_COUNT")):
            base = 1.0 / self.rates[i]                       # 自然公平赔率，无封顶
            if total > 0 and self.total_bets[i] > 0:
                share = self.total_bets[i] / total
                factor = (avg / share) ** 0.5                # 押注占比越高 -> 因子越小
                factor = max(0.4, min(factor, 2.5))          # 限制单匹摆动幅度，保证可读
            else:
                factor = 1.0
            raw.append(base * factor)
        # 赔率上限（经济保护）：默认 10 倍，0=无上限（旧行为）。封顶在单调约束前统一应用
        if sget("RACE_ODDS_CAP") > 0:
            raw = [min(value, sget("RACE_ODDS_CAP")) for value in raw]
        # 单调约束：按胜率升序，确保低胜率马的赔率不低于高胜率马
        order = sorted(range(sget("HORSE_COUNT")), key=lambda i: self.rates[i])
        for a, b in zip(order, order[1:]):
            if raw[a] < raw[b]:
                raw[b] = raw[a]
        # 同显示胜率（整数%）的馬，赔率必须完全一致，避免"胜率一样赔率却不同"的困惑。
        # 取组内最低赔率统一，不抬高任一匹，保证庄家不被过度赔付。
        groups = {}
        for i in range(sget("HORSE_COUNT")):
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
        if not 0 <= horse < sget("HORSE_COUNT") or amount <= 0: return False, "马号或金额无效"
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
        return InlineKeyboardMarkup([[InlineKeyboardButton(f"{sget('HORSE_EMOJI')[i]} {amount}", callback_data=f"horsebet_{i}_{amount}") for i in range(sget("HORSE_COUNT"))] for amount in sget("FIXED_BET_AMOUNTS")])

    async def view(self, app):
        """保持原版赛车下注界面的赛道、路书、胜率和投注信息结构。"""
        remain = max(0, int(sget("RACE_AUTO_START") - (time.time() - self.create_time)))
        minutes, seconds = divmod(remain, 60)
        history = "".join(sget("HORSE_EMOJI")[index] for index in race_history[self.chat_id][-10:]) or "暂无"
        stats = race_daily_stats[self.chat_id]
        total_wins = sum(stats)
        odds = self.odds()
        lines = [
            f"🏁 赛车大赛 {race_id(self.create_time)} 🏁",
            "━" * 14,
            *[f"🏁{'━' * 13}{sget('HORSE_EMOJI')[i]}" for i in range(sget("HORSE_COUNT"))],
            "━" * 14,
            "📊 路书",
            f"近10场: {history}",
            "📜 当日胜率:",
            "  " + " | ".join(f"{sget('HORSE_EMOJI')[i]} {stats[i]}胜" for i in range(sget("HORSE_COUNT"))),
            "  " + " | ".join(f"{sget('HORSE_EMOJI')[i]} {stats[i] / total_wins * 100:.0f}%" if total_wins else f"{sget('HORSE_EMOJI')[i]} 0%" for i in range(sget("HORSE_COUNT"))),
            "📊 投注情况:",
        ]
        for i, odd in enumerate(odds):
            lines.append(f"{sget('HORSE_EMOJI')[i]} {sget('HORSE_NAMES')[i]}: 胜率{self.rates[i] * 100:.0f}% | {self.total_bets[i]}积分 | 赔率 {odd:.2f}x")
        lines.append("━" * 14)
        if self.bets:
            lines.append("📋 玩家下注：")
            for uid, bets in self.bets.items():
                name = self.name_cache.get(uid) or await get_name(app, uid)
                self.name_cache[uid] = name
                lines.append(f"{name}: " + " ".join(f"{sget('HORSE_EMOJI')[h]}{amount}" for h, amount in bets.items()))
            lines.append("")
        _banner = race_subsidy_banner(self.auto_started)
        if _banner: lines.append(_banner)
        lines.extend([f"⏰ 距离开赛还有 {minutes} 分 {seconds:02d} 秒", "🔒 开赛后锁盘，赔率随注浮动、下注即锁"])
        return "\n".join(lines)

    def animation(self):
        lines = ["🏁 赛车进行中", "━" * 14]
        for i, pos in enumerate(self.display_positions):
            track_pos = max(0, min(sget("RACE_TRACK_LENGTH"), int(pos)))
            track = "🏁" + (sget("HORSE_EMOJI")[i] + "━" * sget("RACE_TRACK_LENGTH") if track_pos >= sget("RACE_TRACK_LENGTH") else "━" * (sget("RACE_TRACK_LENGTH") - track_pos - 1) + sget("HORSE_EMOJI")[i] + "━" * track_pos)
            lines.append(track)
        if self.arrivals: lines.append("✅ 到达：" + " ".join(sget("HORSE_EMOJI")[i] for i in self.arrivals))
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
                remain = max(0, int(sget("RACE_AUTO_START") - (time.time() - self.create_time)))
                
                # 只有在整秒点附近才发出推送通知，防止重复发送
                for threshold in thresholds:
                    if remain <= threshold and threshold not in self.notified:
                        self.notified.add(threshold)
                        notice = await safe_send(app.bot, self.chat_id, f"⏰ 赛车还剩 {threshold // 60} 分钟 {threshold % 60} 秒！")
                        # 之前这条提示发出后就一直留在群里，需要自动删除
                        schedule_delete(app, self.chat_id, notice, sget("RACE_NOTICE_DELETE_SECONDS"))
                
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
            remaining = list(range(sget("HORSE_COUNT")))
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
                a_cap = max(0.0, (1 - T / (sget("RACE_TRACK_LENGTH") * sget("RACE_ANIMATION_INTERVAL"))) / math.pi)
                if random.random() < 0.25:
                    a = random.uniform(0.05, 0.35) * a_cap    # 四分之一概率接近匀速，增加剧本多样性
                else:
                    a = random.uniform(0.4, 0.95) * a_cap
                sign = random.choice([-1, 1])                  # -1 先慢后快（反超），+1 先快后慢（守擂）
                self.race_tempo[horse] = (sign, a)
            while not self.cancelled and len(self.arrivals) < sget("HORSE_COUNT"):
                now = time.time()
                for i in range(sget("HORSE_COUNT")):
                    if i in self.arrival_times:
                        continue
                    duration = self.finish_durations[i]
                    progress = min(1.0, max(0.0, (now - self.race_start_time) / duration))
                    sign, amp = self.race_tempo.get(i, (0, 0.0))
                    tempo = progress + sign * amp * math.sin(progress * math.pi)
                    self.positions[i] = max(0.0, min(float(sget("RACE_TRACK_LENGTH")),
                                                     sget("RACE_TRACK_LENGTH") * tempo))
                    if progress >= 1.0:
                        self.arrival_times[i] = self.race_start_time + duration
                        self.positions[i] = float(sget("RACE_TRACK_LENGTH"))
                        self.display_positions[i] = sget("RACE_TRACK_LENGTH")
                    else:
                        # 画面格子严格跟随真实节奏进度：既不超前（不会提前压线）也不滞后（不会钉死）
                        self.display_positions[i] = max(0, min(sget("RACE_TRACK_LENGTH"), int(self.positions[i])))
                self.arrivals = sorted(self.arrival_times, key=self.arrival_times.get)
                await self._push_animation_frame(app)
                if len(self.arrivals) < sget("HORSE_COUNT"): await asyncio.sleep(sget("RACE_ANIMATION_INTERVAL"))
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
                lines.extend(f"{standings[index]} {sget('HORSE_EMOJI')[horse]} {sget('HORSE_NAMES')[horse]}" for index, horse in enumerate(self.arrivals))

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
                # 抽水先算（官方模式），结算行直接带「实收」
                rake_per = calc_rake({s[0]: s[5] for s in settlements})[1] if self.mode == "official" else {}
                # 系统加奖（2026-09-11 用户要求）：先判定额度，再按押中者注额比例拆分。
                # 无人押中 → 拆不出人 → 不发、也不消耗当日额度。
                subsidy = race_subsidy_for(self.chat_id, date, len(self.bets), self.auto_started)
                subsidy_map = race_subsidy_split(subsidy, self.bets, winner) if subsidy else {}
                if not subsidy_map: subsidy = 0
                # 阶段二：统一改写钱包（此处仅 dict 操作，不会抛异常，payouts_applied 必定置位）
                for uid, _, _, _, payout, _, _ in settlements:
                    wallet[self.chat_id][uid] += payout + subsidy_map.get(uid, 0); total_payout += payout
                if subsidy: race_subsidy_by_day[date][self.chat_id] += subsidy
                if len(race_subsidy_by_day) > 3:      # 只留最近 3 天，别让按日容器无限膨胀
                    for _d in sorted(race_subsidy_by_day.keys())[:-3]: race_subsidy_by_day.pop(_d, None)
                payouts_applied = True

                # 大奖战报：押中独赢且净赢超阈值 → 广播其他授权群
                best = max(settlements, key=lambda s: s[5]) if settlements else None
                if best and best[5] > 0:
                    detail = f"🐴 押中 {sget('HORSE_EMOJI')[winner]}{sget('HORSE_NAMES')[winner]}（赔率 {best[6]:.1f}）"
                    await broadcast_big_win(app, self.chat_id, best[0], "🏎️ 赛车大赛", best[5], detail)
                if self.mode == "official":
                    await commit_rake(app, self.chat_id, rake_per, "赛车")
                    # 累计参与局数（归零门槛）+ 赢分计入累计获得 + 升级通知
                    for uid, _nm, _stake, _bow, _pay, _net, _odd in settlements:
                        games_played[self.chat_id][uid] += 1
                        # 实际到手 = 净赢 - 本局抽水（抽水已在上面扣除）+ 系统加奖（真产出，计入累计获得）
                        _gain = _net - int(rake_per.get(uid, 0) or 0) + subsidy_map.get(uid, 0)
                        if _gain > 0:
                            _oe = _earn_get(self.chat_id, uid)
                            _earn_add(self.chat_id, uid, _gain)
                            await _check_level_change(app, self.chat_id, uid, _oe, _earn_get(self.chat_id, uid))

                available_pool = self.jackpot + self.pool
                supplement = max(0, total_payout - available_pool)
                if self.mode == "official":
                    race_jackpot[self.chat_id] = max(0, available_pool - total_payout)
                if supplement:
                    lines.extend(["", f"⚠️ 奖池不足，系统补充 {supplement} 积分"])
                elif not total_payout:
                    lines.extend(["", "🔄 无人押中，奖池滚入下一期。"])

                if subsidy:
                    lines.extend(["", f"🎁 系统加奖 {subsidy} 积分（按押中注额分配）："])
                    for _uid, _amt in sorted(subsidy_map.items(), key=lambda x: -x[1]):
                        _nm = self.name_cache.get(_uid)
                        if not _nm:
                            _nm = await get_name(app, _uid); self.name_cache[_uid] = _nm
                        lines.append(f"　{_nm}：+{_amt}")

                lines.extend(["", "💰 本局结算："])
                for _, name, stake, bet_on_winner, payout, net, bo in settlements:
                    r_amt = rake_per.get(_, 0)
                    r_txt = f"（实收 {net - r_amt}，含抽水{r_amt}）" if r_amt else ""
                    if bet_on_winner > 0:
                        lines.append(f"{name}：总投注 {stake}｜命中 {bet_on_winner}（{bo:.2f}x）｜派彩 {payout}｜净 {net:+d}{r_txt}")
                    else:
                        lines.append(f"{name}：总投注 {stake}｜未命中｜净 {net:+d}")

                # 累计盈利榜单独发一条（2026-09-11 用户要求：结算正文太长像刷屏，榜单拆开发）
                _rank_lines = None
                if self.mode == "official":
                    day_rank = sorted(total_profit_by_game(race_profit_by_date, self.chat_id).items(), key=lambda item: item[1], reverse=True)[:50]
                    if day_rank:
                        _rank_lines = ["🏆 <b>赛车累计盈利榜（总数）</b>", "━━━━━━━━━━━━━━━━━"]
                        for index, (uid, amount) in enumerate(day_rank, 1):
                            name = self.name_cache.get(uid)
                            if not name:
                                name = await get_name(app, uid)
                                self.name_cache[uid] = name
                            _rank_lines.append(f"{rank_marker(index)} {name}：{amount:+d}")
                else:
                    lines.extend(["", "🎮 娱乐局：本局不计入正式盈亏榜。"])
                
                self.phase = "finished"; save_data(); await asyncio.to_thread(force_save_now)
                # 清除退款记录
                for uid in self.bets: pending_game_bets[self.chat_id].get(uid, {}).pop("horse", None)
                delivered = await safe_send_long(app.bot, self.chat_id, "\n".join(lines), parse_mode="HTML")
                if sget("SETTLE_DELETE_SECONDS") > 0:
                    schedule_delete(app, self.chat_id, delivered, sget("SETTLE_DELETE_SECONDS"))
                await send_settle_rank(app, self.chat_id, _rank_lines)

                if delivered is None:
                    schedule_notice_delete(app, self.chat_id, await safe_send(app.bot, self.chat_id, "⚠️ 赛车已完成结算，但详细结果消息发送失败。积分与当日盈亏已保存，可使用 /cx 查看排行榜。"), kind="settle")
            except Exception:
                logger.exception("赛车结算异常，群 %s", self.chat_id)
                # 仅在尚未派彩时退款，避免已派彩玩家被双重派彩
                if not payouts_applied:
                    self.refund_all()   # 退款与清 pending 必须同生共死，否则重启会再退一次
                    if self.mode == "official": race_jackpot[self.chat_id] = self.jackpot
                    schedule_notice_delete(app, self.chat_id, await safe_send(app.bot, self.chat_id, "⚠️ 赛车结算异常，本局已退款以保护玩家积分。"), kind="settle")
                else:
                    schedule_notice_delete(app, self.chat_id, await safe_send(app.bot, self.chat_id, "⚠️ 赛车结算显示异常，派彩已保存，可使用 /cx 查看排行榜。"), kind="settle")
                save_data()
            finally:
                await safe_delete(app.bot, self.chat_id, self.animation_msg_id)
                # 下注面板此前全程只做原地编辑、从不删除，会一直堆在群里；结算后延迟清理
                schedule_delete_ids(app, self.chat_id, self.game_msg_id, sget("PANEL_DELETE_SECONDS"))
                if active_horse_races.get(self.chat_id) is self: active_horse_races.pop(self.chat_id, None)
                if self.mode == "official":
                    for uid in self.bets: await emergency_if_needed(self.chat_id, uid, app)

    def refund_all(self):
        """全部下注原路退回，并同步清除 pending_game_bets。

        退款与清 pending 必须同生共死：只退钱不清 pending 的话，进程重启时
        load_data 会按残留的 pending 再退一次 = 凭空多出一份积分。
        """
        for uid, bets in self.bets.items():
            game_chips[self.chat_id][uid] += sum(bets.values())
            pending_game_bets[self.chat_id].get(uid, {}).pop("horse", None)

    async def refund(self, app, notice):
        async with self.lock:
            if self.cancelled: return
            self.cancelled, self.phase = True, "cancelled"
            self.refund_all()
            # 奖池不再在开局时弹出，故取消/退款时无需回写（race_jackpot[cid] 始终保留原始奖池）
            save_data()
            if active_horse_races.get(self.chat_id) is self: active_horse_races.pop(self.chat_id, None)
            await safe_edit(app.bot, self.chat_id, self.game_msg_id, notice, reply_markup=None)
            # 取消/退款后的面板同样只留一小会儿，避免残留占位
            schedule_delete_ids(app, self.chat_id, self.game_msg_id, sget("PANEL_DELETE_SECONDS"))


# ---------- 权限与命令 ----------
def is_auth(cid): return cid in AUTHORIZED_GROUPS
def is_bot_admin(uid): return uid in BOT_ADMINS
async def need_auth(update, context=None):
    # 授权只针对「群聊」：私聊没有群组概念，不应被「群组未授权」拦截。
    # 私聊里真正受限的游戏/管理命令，各自还有 require_group_chat / is_bot_admin 兜底。
    _u = update.effective_user
    if _u and _u.id and _u.id not in user_first_seen:
        user_first_seen[_u.id] = time.time()  # 首次互动时间（商城兑换门槛用）
    chat = update.effective_chat
    if chat and chat.type in ("group", "supergroup"):
        if not is_auth(chat.id):
            # 新群默认不在授权名单里，而「初始积分/签到/游戏」等全部走这里拦截。
            # 管理员自己在新群里会只看到「请联系管理员」却无路可走（用户实际踩过），
            # 所以对 Bot 管理员直接把「本群怎么授权」写清楚，一步可解。
            if _u and is_bot_admin(_u.id):
                _tip = (f"❌ 本群尚未授权，群内积分/游戏等功能不会生效。\n"
                        f"你是 Bot 管理员，直接在本群发送 /授权 即可（群号 {chat.id}）。")
            else:
                _tip = "❌ 此群组未授权，请联系管理员。"
            if update.effective_message:
                if context is not None and update.message: await send_reply(update, context, _tip)
                else: await update.effective_message.reply_text(_tip)
            return False
    return True


def is_group_chat(update):
    """消息是否来自群聊/超级群（多人游戏只能在此发起，私聊开别人看不到）。"""
    chat_type = update.effective_chat.type if update.effective_chat else None
    return chat_type in ("group", "supergroup")


async def require_group_chat(update, game_name, cmd, context=None):
    """多人游戏必须在群聊发起；私聊里开只有发起人自己看得到。返回 False 时已回复提示。"""
    if not is_group_chat(update):
        await send_reply(update, context, 
            f"⚠️ {game_name}是多人游戏，请在群聊中发起（发送 /{cmd}），别人才能一起玩。私聊里开只有你自己看得到。")
        return False
    return True

async def cmd_start(update, context):
    """/start 只回一句你好（deep-link 邀请点 START 后发一屏帮助太刷屏）；完整帮助在 /help。"""
    if not await need_auth(update, context): return
    # 私聊深链：邀请 deep-link（t.me/<bot>?start=inv_<邀请人>_<群id>）等在此分流
    _args = context.args or []
    if _args:
        _a0 = _args[0]
        if _a0.startswith("redeem_"):
            await _deep_redeem_start(update, context, _a0); return
        if _a0.startswith("mall_"):
            await _deep_mall_start(update, context, _a0); return
        if _a0.startswith("sexch_"):
            await _deep_season_exchange_start(update, context, _a0); return
        if _a0.startswith("inv_"):
            await _deep_invite_start(update, context, _a0); return
    await send_reply(update, context, "👋 你好！我是娱乐机器人 🎮\n\n发 /help 查看全部功能（游戏 / 积分 / 邀请 / 数据）。")


async def cmd_help(update, context):
    """/help（帮助/菜单）：完整功能帮助；管理员追加管理命令段。"""
    if not await need_auth(update, context): return
    text = "🎮 娱乐机器人功能帮助\n\n🎲 发起游戏：\n/开始 或 /help - 查看本帮助\n/德州 - 发起德州扑克（统一积分）\n/赛车 - 发起赛车\n/21点 - 发起21点\n/炸金花 - 发起炸金花（闷牌偷鸡）\n/大话骰 - 发起大话骰（吹牛骰盅，掉骰子制）\n\n💰 积分系统：\n/签到 - 每日签到领积分\n/我的积分 - 积分/等级/签到状态\n/积分排行 - 积分排行榜\n/积分商城 - 用积分换好物\n红包 总数 份数 - 发积分红包（如：红包 1000 5）\n转赠 数量 - 把积分转给群里成员（回复消息用）\n充值 数量 - 申请购买积分（管理员确认到账）\n\n🎟️ 邀请有礼：\n/link - 领取本群专属邀请链接\n今日邀请排行 / 本月邀请排行 / 总邀请排行 - 查看邀请榜\n\n📊 数据查询：\n/盈亏 - 当日盈亏榜\n/排行 - 总积分榜\n流水 - 查自己的积分来源明细（红包/抽水/邀请奖励等；回复他人消息查对方仅限管理员）\n/结束 - 终止当前游戏\n\n🏪 称号商店：\n/商店 - 查看可兑换称号\n/兑换 称号名 - 用积分换称号"
    if is_bot_admin(update.effective_user.id):
        text += "\n\n🔧 管理命令（仅管理员）：\n/授权 - 授权当前群使用\n取消授权 - 取消群授权\n/授权列表 - 查看已授权群\n/加管理员 /减管理员 /管理员列表\n/加积分(负数即减) /赛季分\n/拉黑 /解黑 /黑名单 - 封禁违规玩家\n/列表 - 管理总览(管理员/授权群/黑名单三合一)\n/备份 /恢复\n💡 快捷加减分：在群里回复某玩家的消息，然后发「/add 数量」即可给他加/减分（负数即减），不用输ID"
    await send_reply(update, context, text)

# ---------- 21点 界面与逻辑 ----------
async def start_bj_turn_timer(game, app):
    game.cancel_timer()
    curr_uid = game.players[game.current_player_idx]
    async def timeout():
        await asyncio.sleep(sget("TURN_TIMEOUT"))
        if active_blackjack_games.get(game.chat_id) is not game: return  # 游戏已终止或被替换
        if game.phase == "playing" and game.players[game.current_player_idx] == curr_uid:
            game.next_player()
            schedule_notice_delete(app, game.chat_id,
                                   await safe_send(app.bot, game.chat_id, f"⏰ {await get_name(app, curr_uid)} 超时自动停牌。"))
            if game.phase == "dealer_turn": await update_blackjack_ui(game, app)
            else: await update_blackjack_ui(game, app); await start_bj_turn_timer(game, app)
    game.timer_task = asyncio.create_task(timeout())

async def start_bj_wait_timeout(game, app):
    """21点等待房倒计时：有人加入则自动开局，无人加入自动解散。"""
    game.cancel_wait()
    async def expire():
        _wait = sget("ROOM_WAIT_TIMEOUT")
        await asyncio.sleep(_wait)
        if game.phase != "waiting" or active_blackjack_games.get(game.chat_id) is not game:
            return
        if game.players:
            if game.start():
                await update_blackjack_ui(game, app)
                await start_bj_turn_timer(game, app)
        else:
            active_blackjack_games.pop(game.chat_id, None)
            await safe_edit(app.bot, game.chat_id, game.game_msg_id, f"⌛ 21点等待 {_wait} 秒无人加入，房间已自动解散。", reply_markup=None)
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
    text += f"\n⏰ 有人加入后 {sget('ROOM_WAIT_TIMEOUT')} 秒自动开局，无人加入自动解散。\n"
    # 按钮每行最多 2 个：Telegram 一行挤 4 个会截断成「📥 加入 (下...」（用户 2026-09-10 截图报障）
    kb = [[InlineKeyboardButton(f"📥 加入 {b}", callback_data=f"bj_join_{b}") for b in sget("BJ_JOIN_BETS")[i:i + 2]]
          for i in range(0, len(sget("BJ_JOIN_BETS")), 2)]
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
        dealer_peek = game.get_card_str(game.dealer_hand, True)
        my_hand = game.get_card_str(game.hands[curr_uid])
        my_score = game.get_score(game.hands[curr_uid])
        # 单一权威面板：牌桌+操作按钮同一条消息，原地编辑不闪跳；信息不再写两遍
        lines = ["🃏 <b>21点</b>", f"🏛 庄家：{dealer_peek}", "━━━━━━━━━━━━━━━━━"]
        # 2026-09-11 用户要求：行动行放到分隔线之后、玩家列表之前
        lines.append(f"⏳ <b>{await get_name(app, curr_uid)}</b> 行动｜我 {my_hand} ({my_score}点)")
        lines.append("")
        # 👉 留在行首，非行动者补 3 个半角空格占位 → 所有行序号落在同一列
        for i, uid in enumerate(game.players, 1):
            mark = "👉 " if uid == curr_uid else "   "
            lines.append(f"{mark}{i}. {await get_name(app, uid)} {game.get_card_str(game.hands[uid])} ({game.get_score(game.hands[uid])})")
        text = "\n".join(lines)

        kb_rows = [[
            InlineKeyboardButton("🃏 要牌", callback_data=f"bj_hit_{curr_uid}"),
            InlineKeyboardButton("✋ 停牌", callback_data=f"bj_stand_{curr_uid}")
        ]]
        wallet = game_chips
        if len(game.hands[curr_uid]) == 2 and wallet[game.chat_id][curr_uid] >= game.bets[curr_uid] and not game.is_blackjack(game.hands[curr_uid]):
            kb_rows.append([InlineKeyboardButton("💰 双倍", callback_data=f"bj_double_{curr_uid}")])
        kb = InlineKeyboardMarkup(kb_rows)

        edited = await safe_edit(app.bot, game.chat_id, game.game_msg_id, text, reply_markup=kb, parse_mode="HTML") if game.game_msg_id else None
        if edited:
            game.game_msg_id = edited.message_id
        else:
            await safe_delete(app.bot, game.chat_id, game.game_msg_id)
            msg = await safe_send(app.bot, game.chat_id, text, reply_markup=kb, parse_mode="HTML")
            if msg: game.game_msg_id = msg.message_id
        game.action_msg_id = None
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
            d_bust = d_score > 21
            text = (f"🃏 <b>21点 · 结算</b>\n━━━━━━━━━━━━━━━━━\n"
                    f"🏛 <b>庄家</b> {game.get_card_str(game.dealer_hand)} · <b>{d_score}</b>"
                    f"{' 💥 爆牌' if d_bust else ''}\n")
            date = business_date()
            wallet = game_chips

            lines = []
            # 预先获取所有名字，提高 HTML 生成速度
            player_names = {}
            for uid in game.players: player_names[uid] = await get_name(app, uid)

            # ===== 阶段一：只计算派彩，绝不动钱包（先算后付，杜绝中途异常双重退款）=====
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
                    result_str = "💥 爆牌"; payout = 0
                elif dealer_bj and not player_bj:
                    result_str = "🏛 庄家天生21"; payout = 0
                elif d_score > 21:
                    if player_bj: result_str = "🃏 Blackjack"; payout = int(bet * 2.5)
                    else: result_str = "🏛 庄家爆牌"; payout = bet * 2
                elif p_score > d_score:
                    if player_bj: result_str = "🃏 Blackjack"; payout = int(bet * 2.5)
                    else: result_str = "🎉 获胜"; payout = bet * 2
                elif p_score < d_score:
                    result_str = "💸 战败"; payout = 0
                else:
                    if player_bj and dealer_bj: result_str = "🤝 双天生21"; payout = bet
                    else: result_str = "🤝 平局"; payout = bet
                
                net = payout - bet
                hand_text = game.get_card_str(game.hands[uid])
                # 抽水在面板体现：赢家单独一行标「抽水」，不再塞进盈亏后面的括号里
                r_amt = calc_rake({uid: net})[1].get(uid, 0) if game.mode == "official" else 0
                head = f"👤 <b>{player_names[uid]}</b> {hand_text} · <b>{p_score}</b>\n"
                if r_amt:
                    lines.append(f"{head}"
                                 f"　　{result_str}｜盈亏 <b>{net:+d}</b>\n"
                                 f"　　　└ 实收 <b>{net - r_amt:+d}</b>（抽水 {r_amt}）")
                else:
                    lines.append(f"{head}"
                                 f"　　{result_str}｜盈亏 <b>{net:+d}</b>")
                payout_plan.append((uid, payout, net))
            # 抽水金额先算好（与面板一致），结算落账时一并扣
            rake_per = calc_rake({uid: net for uid, _p, net in payout_plan})[1] if game.mode == "official" else {}

            # ===== 阶段二：全部算成功后，统一改钱包 + 写盈亏 + 清退款记录 =====
            async with user_wallet_locks([uid for uid, _, _ in payout_plan]):
                for uid, payout, net in payout_plan:
                    wallet[game.chat_id][uid] += payout
                    if game.mode == "official":
                        blackjack_profit_by_date[date][game.chat_id][uid] += net
                    pending_game_bets[game.chat_id].get(uid, {}).pop("21", None)
            payments_applied = True
            save_data(); await asyncio.to_thread(force_save_now)

            # 大奖战报：官方模式玩家净赢超阈值 → 广播其他授权群
            if game.mode == "official" and payout_plan:
                best = max(payout_plan, key=lambda x: x[2])
                if best[2] > 0: await broadcast_big_win(app, game.chat_id, best[0], "♠️ 21点", best[2])
                await commit_rake(app, game.chat_id, rake_per, "21点")
                # 累计参与局数（归零门槛）+ 赢分计入累计获得 + 升级通知
                for uid, _payout, _net in payout_plan:
                    games_played[game.chat_id][uid] += 1
                    # 实际到手 = 净赢 - 本局抽水（抽水已在上面扣除）
                    _gain = _net - int(rake_per.get(uid, 0) or 0)
                    if _gain > 0:
                        _oe = _earn_get(game.chat_id, uid)
                        _earn_add(game.chat_id, uid, _gain)
                        await _check_level_change(app, game.chat_id, uid, _oe, _earn_get(game.chat_id, uid))

            # 记录庄家历史 (仅记录本局主要趋势)
            if game.mode == "official":
                # 计算本局玩家总体输赢，用于生成庄家路书图标
                total_net = sum(net for (uid, payout, net) in payout_plan)
                history_icon = "🏛" if total_net < 0 else ("🤝" if total_net == 0 else "👤")
                blackjack_history[game.chat_id] = (blackjack_history[game.chat_id] + [history_icon])[-10:]

            text += "\n\n".join(lines)
            
            # 累计盈利榜单独发一条（2026-09-11 用户要求：结算正文太长像刷屏，榜单拆开发）
            _rank_lines = None
            if game.mode == "official":
                bj_rank = sorted(total_profit_by_game(blackjack_profit_by_date, game.chat_id).items(), key=lambda item: item[1], reverse=True)[:30]
                if bj_rank:
                    _rank_lines = ["🏆 <b>21点 累计盈利榜（总数）</b>"]
                    for i, (u, a) in enumerate(bj_rank, 1):
                        name = game.name_cache.get(u) or await get_name(app, u)
                        game.name_cache[u] = name
                        _rank_lines.append(f"{rank_marker(i)} {name}：{a:+d}")
                
            await safe_delete(app.bot, game.chat_id, game.game_msg_id)
            settled_msgs = await safe_send_long(app.bot, game.chat_id, text, parse_mode="HTML")
            if sget("SETTLE_DELETE_SECONDS") > 0:
                schedule_delete(app, game.chat_id, settled_msgs, sget("SETTLE_DELETE_SECONDS"))
            await send_settle_rank(app, game.chat_id, _rank_lines)
        except Exception:
            logger.exception("21点结算显示失败")
            if not payments_applied:
                # 派彩前出错，退还投注
                wallet = game_chips
                for uid in game.players:
                    wallet[game.chat_id][uid] += game.bets[uid]
                schedule_notice_delete(app, game.chat_id, await safe_send(app.bot, game.chat_id, "⚠️ 21点结算异常，本局已退款，积分不受影响。"), kind="settle")
            else:
                schedule_notice_delete(app, game.chat_id, await safe_send(app.bot, game.chat_id, "⚠️ 21点已结算，但由于 HTML 渲染问题无法显示详细战报。积分已保存。"), kind="settle")
        finally:
            active_blackjack_games.pop(game.chat_id, None)
            save_data()







async def _game_gate(update, context, game, ranked=None):
    """4 游戏总开关/仅管理员开局（后台各游戏分组设置，保存立即生效）。返回 True=放行。

    ranked：仅德州用。True=排位德州、False=日常德州、None=不区分（走总开关）。
    德州额外受「日常/排位」两个独立开关控制，管理员可只开一种模式。
    """
    label, enabled, admin_only = {
        "texas":     ("德州扑克", sget("TEXAS_ENABLED"), sget("TEXAS_ADMIN_ONLY")),
        "blackjack": ("21点", sget("BJ_ENABLED"), sget("BJ_ADMIN_ONLY")),
        "jinhua":    ("炸金花", sget("JINHUA_ENABLED"), sget("JINHUA_ADMIN_ONLY")),
        "dice":      ("大话骰", sget("DICE_ENABLED"), sget("DICE_ADMIN_ONLY")),
        "race":      ("赛车", sget("RACE_ENABLED"), sget("RACE_ADMIN_ONLY")),
    }[game]
    if not enabled:
        await send_reply(update, context, f"❌ {label}已关闭（管理员可在后台「{label}」分组重新开启）。")
        return False
    if game == "texas" and ranked is not None:
        if ranked and not sget("RANKED_TEXAS_ENABLED"):
            await send_reply(update, context, "❌ 排位德州已关闭（管理员可在后台「德州扑克」分组开启）。")
            return False
        if not ranked and not sget("DAILY_TEXAS_ENABLED"):
            await send_reply(update, context, "❌ 日常德州已关闭（管理员可在后台「德州扑克」分组开启）。")
            return False
    if admin_only and not is_bot_admin(update.effective_user.id):
        await send_reply(update, context, f"❌ {label}仅管理员可开局。")
        return False
    return True


async def cmd_21(update, context):
    if not await need_auth(update, context): return
    if not await _game_gate(update, context, "blackjack"): return
    if not await require_group_chat(update, "21点", "21", context): return
    cid, uid = update.effective_chat.id, update.effective_user.id
    if cid in active_blackjack_games:
        g = active_blackjack_games[cid]
        if g.phase == "waiting":
            # 已有等待房：绝不发第二块面板（两块并存时旧面板按钮会指到已失效状态，点了没反应）。面板状态没变，无需编辑，只提示。
            await send_reply(update, context, "本群已有等待中的 21点，请在上面的面板加入。")
        else:
            await send_reply(update, context, "当前已有 21点 进行中。")
        return
    mode = current_game_mode()
    game = BlackjackGame(cid, uid, mode)
    active_blackjack_games[cid] = game
    # 发起人不自动入座：想玩自己点「加入」下注，不强制扣分（2026-09-08 用户要求）
    await update_blackjack_ui(game, context.application)  # 直接发送等待房界面，无"准备中"占位
    await start_bj_wait_timeout(game, context.application) # 启动等待超时

# ==================== 大话骰（吹牛·港式标准） ====================
# 2026-09-11 按《大话骰规则_港式标准.md》实现：
# 万能1 / 叫「X个1」翻倍计且1不当万能 / 首手禁叫1 / 严格越叫越大 /
# 开骰无平局（实际≥叫的→开骰者输；实际<叫的→被开者输） /
# 掉骰子多轮制（输家掉1骰、全员重摇、输家先叫、归零出局、幸存者通吃奖池）。

DICE_ANTE = 200           # 底注（开局一次性扣进奖池，弃局作废）
DICE_DICE_COUNT = 5       # 每人骰子数
DICE_WILD_ONE = 1         # 1万能牌开关（关=无万能局：1 就是普通点数，首手可叫1）
DICE_STRAIGHT_ZERO = 1    # 顺子算0个（0=关 / 1=仅两人局 / 2=所有人数；含“假顺”=用万能1补位凑成）
DICE_LEOPARD_BONUS = 1    # 豹子加成（0=关 / 1=仅两人局 / 2=所有人数）：纯豹+2、花豹+1（2026-09-11 群友口径）
DICE_DROP_DICE = 0        # 掉骰子多轮制（0=关：任何人数都一把定胜负、一局即结算；1=开：三人以上才掉骰）
DICE_THINK_SECONDS = 60   # 叫牌思考秒数（超时自动开骰/最小叫牌，防卡死）
DICE_MAX_PLAYERS = 10     # 单桌最多人数（2026-09-11 群友要求：最多 10 个人）
DICE_ENABLED, DICE_ADMIN_ONLY = 1, 0

active_dice_games = {}

_CN_NUM = {"一": 1, "二": 2, "两": 2, "三": 3, "四": 4, "五": 5, "六": 6, "七": 7, "八": 8, "九": 9, "十": 10}


def _dice_is_straight(hand, wild=True):
    """一手骰是否「顺子」：恰好 5 颗且连号 —— 12345 或 23456。

    2026-09-11 用户报障补的规则（原话：「23456不是顺子吗 顺子不是算0个吗」）：
    顺子这手**整手算 0 个**，不参与任何点数统计（开骰计数 + 亮盅展示都要体现）。
    万能开时还认「**假顺**」（2026-09-11 群友口径，张瑾一：12456 在两人局算顺子）：
    1 当替身补上空位，只要 5 颗能排成 12345 / 23456 就算 —— 如 12456（1→3）、13456（1→2）。
    掉骰制下只有满 5 颗才可能成顺（4 颗/6 颗一律不算）。
    """
    if len(hand) != 5: return False
    s = sorted(hand)
    for target in ([1, 2, 3, 4, 5], [2, 3, 4, 5, 6]):
        if s == target: return True          # 真顺（天然连号）
    if not wild: return False
    ones = hand.count(1)
    if ones == 0: return False
    rest = sorted(d for d in hand if d != 1)
    for target in ([1, 2, 3, 4, 5], [2, 3, 4, 5, 6]):
        pool = list(target)
        for d in rest:
            if d in pool: pool.remove(d)
            else: pool = None; break
        if pool is not None: return True     # 剩下的空位正好由 ones 个万能 1 补齐
    return False


def _dice_rule_on(setting_name, n_players):
    """规则生效范围开关：0=关；1=仅两人局；2=所有人数（2026-09-11 群友口径：默认只两人局）。"""
    try:
        lv = int(sget(setting_name) or 0)
    except (TypeError, ValueError):
        lv = 1
    if lv <= 0: return False
    return True if lv >= 2 else n_players <= 2


def _dice_duel_mode(game=None, n_players=None):
    """本局是否「一把定胜负」：默认任何人数都一把定胜负（掉骰子多轮制关闭）；
    掉骰开关打开时退回旧行为——三人以上掉骰多轮、只有两人局一把定胜负。

    写成模块级函数是为了兼容只提供 players 的轻量测试桩（不依赖 DiceGame.duel）。
    """
    if not sget("DICE_DROP_DICE"): return True
    if n_players is None:
        n_players = len(getattr(game, "players", None) or [])
    return n_players <= 2


def _dice_leopard_kind(hand, wild=True):
    """豹子牌型：'纯豹'（5 颗点数完全相同）/ '花豹'（带万能 1、其余同点）/ None。"""
    if len(hand) != 5: return None
    if len(set(hand)) == 1: return "纯豹"
    if not wild: return None
    others = set(d for d in hand if d != 1)
    if len(others) == 1 and 1 in hand: return "花豹"
    return None


def _dice_leopard_bonus(hand, face, wild=True):
    """豹子加成（2026-09-11 用户口径）：返回该手在叫 face 时的**额外颗数**。

    - **纯豹（真豹子）**：5 颗点数完全相同 → 该点数 +2（如 5 个 4 算 7）
    - **花豹（假豹子）**：带 1 且其余同点 → 该点数 +1（如 2 个 1 + 3 个 6 算 6）
    加成只作用于豹子自己的点数；「5 个 1」是纯豹且对**任意点数**都成立
    （它本身就是 5 个万能 1，叫什么都算 7 个）。
    """
    kind = _dice_leopard_kind(hand, wild)
    if not kind: return 0
    if kind == "纯豹":
        f = hand[0]
        return 2 if (f == 1 and wild) or f == face else 0
    others = set(d for d in hand if d != 1)
    return 1 if others.pop() == face else 0


def parse_dice_bid(text):
    """把群友的叫牌文本解析成 (数量, 点数)。不是叫牌返回 None。
    宽容识别（玩家怎么顺手怎么打）：
      6个3 / 6個3 / 6 3 / 六个三 / 六個三 / 两 个 四 / 十个2
      叫6个3 / 喊 6个3 / 报6个3 / 我出6个3 / 6个3吧
    """
    t = text.strip()
    t = re.sub(r"^\s*(?:我\s*)?(?:叫|喊|报|出|要)\s*[:：]?\s*", "", t)
    t = re.sub(r"\s*(?:吧|起|了)\s*$", "", t)
    mm = re.fullmatch(r"(\d{1,2}|[一二两三四五六七八九十]+)\s*[个個]\s*(\d|[一二三四五六]+)", t)
    if not mm:
        mm = re.fullmatch(r"(\d{1,2})\s+(\d)", t)
        if not mm: return None
    def _num(s):
        s = s.strip()
        if s.isdigit(): return int(s)
        if len(s) == 1: return _CN_NUM.get(s)
        if s == "十": return 10
        if "十" in s:
            a, _, b = s.partition("十")
            return (_CN_NUM.get(a, 1) if a else 1) * 10 + (_CN_NUM.get(b, 0) if b else 0)
        return None
    c, f = _num(mm.group(1)), _num(mm.group(2))
    if c is None or f is None or c < 1 or f < 1: return None
    return c, f


class DiceGame:
    """大话骰：每人 N 骰偷看，轮流叫「X个Y」必须越叫越大，开骰掀盅定输赢，掉骰子多轮制。

    资金模型与炸金花一致：开局底注扣进局内副本（钱包不动），结算按净差回写，
    弃局直接作废副本即等于全额退款。
    """

    def __init__(self, cid, owner, mode=None):
        self.chat_id, self.owner_id, self.mode, self.phase = cid, owner, mode or current_game_mode(), "waiting"
        self.players, self.chips, self.initial_chips, self.paid = [], {}, {}, {}
        self.dice = {}         # uid -> 剩余骰子数
        self.hands = {}        # uid -> [点数列表]（仅本局内存，绝不下发群）
        self.out = set()       # 已出局
        self.dropped = []      # 开局因底注不足被剔除的玩家（调用方提示用）
        self.pot = 0
        self.bid = None        # 当前叫牌 (count, face, uid)
        self.starter_uid = None  # 本手先叫者（上一手输家先叫）
        self.actor = None      # 当前行动者
        self.hand_no = 0
        self.game_msg_id = None
        self.turn_task = self.wait_task = None
        self.settled = False
        self.last_action = None
        self._render_lock = asyncio.Lock()

    # ---- 等待房 ----
    def add(self, uid):
        if self.phase != "waiting" or uid in self.players: return False
        if len(self.players) >= sget("DICE_MAX_PLAYERS"): return False
        if game_chips[self.chat_id][uid] < sget("MIN_ENTRY_CHIPS"): return False
        self.players.append(uid)
        return True

    # ---- 开局 ----
    def start(self):
        if len(self.players) < 2: return False
        # 底注不足者剔除（否则 paid=0 却能分奖池 = 零成本白拿），由调用方提示
        _ante = sget("DICE_ANTE")
        self.dropped = [u for u in self.players if game_chips[self.chat_id][u] < _ante]
        if self.dropped:
            self.players = [u for u in self.players if u not in self.dropped]
        if len(self.players) < 2: return False
        random.shuffle(self.players)
        self.cancel_wait(); self.out.clear(); self.settled = False
        self.pot = 0; self.paid.clear(); self.chips.clear(); self.initial_chips.clear()
        for uid in self.players:
            self.chips[uid] = game_chips[self.chat_id][uid]
            self.initial_chips[uid] = self.chips[uid]
            ante = min(sget("DICE_ANTE"), self.chips[uid])
            self.chips[uid] -= ante; self.paid[uid] = ante; self.pot += ante
            self.dice[uid] = sget("DICE_DICE_COUNT")
        self.phase = "playing"
        self.starter_uid = self.players[0]
        self._new_hand()
        return True

    # ---- 基础 ----
    def alive(self):
        return [u for u in self.players if u not in self.out]

    def total_dice(self):
        return sum(self.dice[u] for u in self.alive())

    def cancel_timer(self):
        task, self.turn_task = self.turn_task, None
        if task and task is not asyncio.current_task() and not task.done(): task.cancel()

    def cancel_wait(self):
        task, self.wait_task = self.wait_task, None
        if task and task is not asyncio.current_task() and not task.done(): task.cancel()

    # ---- 港式叫牌比较 ----
    def bid_beats(self, new, prev):
        """new 是否严格大于 prev（各为 (count, face)）。
        万能开：普通叫之间同数量可升点；跨 1 的叫牌按翻倍强度比较（X个1 = 2X 个其他点）。
        无万能局：1 是普通点数，全部走 数量优先、同数量比点数。"""
        if not sget("DICE_WILD_ONE"):
            if new[0] != prev[0]: return new[0] > prev[0]
            return new[1] > prev[1]
        if prev[1] == 1 and new[1] == 1: return new[0] > prev[0]
        if prev[1] == 1: return new[0] > prev[0] * 2
        if new[1] == 1: return new[0] * 2 > prev[0]
        if new[0] != prev[0]: return new[0] > prev[0]
        return new[1] > prev[1]

    # ---- 行动 ----
    def action(self, uid, kind, extra=None):
        if self.phase != "playing": return False, "当前不在叫牌阶段"
        if uid != self.actor: return False, "还没轮到你"
        if kind == "bid":
            c, f = extra
            if not (isinstance(c, int) and isinstance(f, int)): return False, "叫牌格式无效"
            if not (1 <= f <= 6): return False, "点数必须是 1~6"
            if c < 1 or c > self.total_dice():
                return False, f"数量要在 1~{self.total_dice()} 之间（在场骰子总数）"
            if sget("DICE_WILD_ONE") and f == 1 and self.bid is None:
                return False, "首手不能叫 1（万能 1 只能在加码中出现）"
            if self.bid and not self.bid_beats((c, f), (self.bid[0], self.bid[1])):
                return False, "叫牌必须严格大于上家（X个1＝2X个其他点）"
            self.bid = (c, f, uid)
            self._next_actor()
            return True, f"叫 {c}个{f}"
        if kind == "open":
            if not self.bid: return False, "还没有叫牌可开"
            if self.bid[2] == uid: return False, "不能开自己的叫牌"
            return True, "开骰"
        return False, "未知操作"

    def _next_actor(self, after=None):
        cur = after if after is not None else self.actor
        if cur not in self.players: return None
        idx = self.players.index(cur)
        for off in range(1, len(self.players) + 1):
            u = self.players[(idx + off) % len(self.players)]
            if u not in self.out:
                self.actor = u
                return u
        return None

    def _next_alive_after(self, uid):
        idx = self.players.index(uid) if uid in self.players else -1
        for off in range(1, len(self.players) + 1):
            u = self.players[(idx + off) % len(self.players)]
            if u not in self.out: return u
        return uid

    def _new_hand(self):
        """掉骰子制：全员重摇，本手先叫者开局（输家先叫）。"""
        self.hand_no += 1
        for uid in self.alive():
            self.hands[uid] = sorted(random.randint(1, 6) for _ in range(self.dice[uid]))
        self.bid = None
        self.actor = self.starter_uid

    # ---- 开骰结算 ----
    def resolve_open(self, opener):
        """返回 (实际数量, 输家, 纯点数个数, 万能1个数)。
        被叫点是 2~6 且万能开：该点数 + 全部1 都计入；被叫点是 1：只数 1 本身。
        两条规则按人数生效（默认**只两人局**，2026-09-11 群友口径「多人的没有顺子，没有豹子」）：
        - **顺子整手算 0 个**（DICE_STRAIGHT_ZERO，含 1 补位的假顺）
          ——2026-09-11 用户报障，此前把顺子里的点数照算，导致结算反了。
        - **豹子加成**（DICE_LEOPARD_BONUS）：纯豹 +2、花豹 +1。
        实际 ≥ 叫的 → 开骰者输；实际 < 叫的 → 被开者输（无平局）。"""
        count, face, bidder = self.bid
        wild = sget("DICE_WILD_ONE")
        _n = len(self.players)
        straight_on = _dice_rule_on("DICE_STRAIGHT_ZERO", _n)
        leopard_on = _dice_rule_on("DICE_LEOPARD_BONUS", _n)
        n_face = n_one = _bonus = 0
        for u in self.alive():
            hand = self.hands[u]
            if straight_on and _dice_is_straight(hand, wild):
                continue          # 顺子整手作废，一颗都不算
            n_face += sum(1 for d in hand if d == face)
            if wild and face != 1:
                n_one += sum(1 for d in hand if d == 1)
            if leopard_on:
                _bonus += _dice_leopard_bonus(hand, face, wild)
        actual = n_face + n_one + _bonus
        loser = opener if actual >= count else bidder
        return actual, loser, n_face, n_one

    def duel(self):
        """本局是否「一把定胜负」（默认任何人数都一把定胜负，见 _dice_duel_mode）。"""
        return _dice_duel_mode(n_players=len(self.players))

    def apply_loss(self, loser):
        """输家掉一颗骰子；归零出局；幸存者重摇、输家先叫；只剩 1 人 → 终局。

        **一把定胜负**（2026-09-11 群友要求「不用少一颗」「一局结束就结算」）：
        输家直接出局、**本局立即结算**，不玩掉骰多轮（三人以上同样生效）；
        奖池由其余存活者平分（见 settle_dice），两人局即退化成「幸存者通吃」。
        """
        if self.duel():
            self.dice[loser] = 0
            self.out.add(loser)
            eliminated = True
        else:
            self.dice[loser] = max(0, self.dice[loser] - 1)
            eliminated = self.dice[loser] <= 0
            if eliminated: self.out.add(loser)
        self.bid = None
        self.starter_uid = loser if loser not in self.out else self._next_alive_after(loser)
        if self.duel() or len(self.alive()) <= 1:
            self.phase = "showdown"
            self.actor = None
        else:
            self._new_hand()
        return eliminated


def dice_min_raise(game):
    """按钮「➕ 加码」的目标叫牌：优先同点数量+1 → 同数量升点 → 全场最小合法叫。无则 None。
    注意面数含 1：叫「X个1」之后同点加码到 (X+1)个1 是合法的（4个1 > 3个1）；
    只有「首手」在万能开时禁叫 1（由 action() 与 not game.bid 分支保证）。"""
    wild = sget("DICE_WILD_ONE")
    faces = list(range(1, 7))
    total = game.total_dice()
    if not game.bid:
        return 1, 2 if wild else 1
    pc, pf, _ = game.bid
    if pc + 1 <= total and game.bid_beats((pc + 1, pf), (pc, pf)):
        return pc + 1, pf
    if pf < 6 and game.bid_beats((pc, pf + 1), (pc, pf)):
        return pc, pf + 1
    for f in faces:
        for c in range(1, total + 1):
            if game.bid_beats((c, f), (pc, pf)):
                return c, f
    return None


async def dice_waiting_text(game, app):
    players = [f"{i}. {await get_name(app, uid)}" for i, uid in enumerate(game.players, 1)]
    _n = len(game.players)
    # 一把定胜负是默认（2026-09-11 群友要求：不用少一颗、一局结束就结算）
    rule = ("一把定胜负，开骰即结算（奖池由其余人平分）。" if _dice_duel_mode(game)
            else "输家掉一颗骰子，掉光出局。")
    wild_rule = "1 是万能牌。" if sget("DICE_WILD_ONE") else ""
    # 顺子/豹子默认只两人局生效（群友口径：多人的没有顺子，没有豹子）
    straight_rule = "顺子（含 1 补位的假顺）一手全算 0 个。" if _dice_rule_on("DICE_STRAIGHT_ZERO", _n) else ""
    leopard_rule = "豹子加成：纯豹 +2、花豹 +1。" if _dice_rule_on("DICE_LEOPARD_BONUS", _n) else ""
    extra = (wild_rule + straight_rule + leopard_rule)
    return (f"🎲 新一局大话骰（吹牛）\n发起人：{await get_name(app, game.owner_id)}\n\n已加入：\n" + "\n".join(players)
            + f"\n\n每人 {sget('DICE_DICE_COUNT')} 颗骰子偷看自己的，轮流叫「X个Y」越叫越大，开骰掀盅，{rule}\n"
            + (extra + "\n" if extra else "")
            + f"⏰ 满 2 人后 {sget('ROOM_WAIT_TIMEOUT')} 秒自动开局，不足 2 人自动解散。底注 {sget('DICE_ANTE')}。")


async def update_dice_waiting(game, app):
    await safe_edit(app.bot, game.chat_id, game.game_msg_id, await dice_waiting_text(game, app),
                    reply_markup=dice_buttons(game, game.owner_id))


async def _dice_del_bid_msg(context, cid, message):
    """删掉玩家发在群里的叫牌/开骰文本，保持群聊清爽（2026-09-11 用户要求）。

    bot 非管理员 / 无删除权限时删不掉 → 静默失败，绝不影响牌局主流程。
    """
    try:
        await message.delete()
    except Exception:
        try:
            await context.bot.delete_message(cid, message.message_id)
        except Exception:
            pass


def dice_buttons(game, uid):
    """等待房：加入/开始/终止；牌局中：行动玩家加码|开骰，其余玩家仅私看自己的骰子（2026-09-11 用户要求）。"""
    if game.phase == "waiting":
        rows = [[InlineKeyboardButton("📥 加入游戏", callback_data="dice_join")]]
        if len(game.players) >= 2: rows.append([InlineKeyboardButton("🎮 开始游戏", callback_data="dice_start")])
        rows.append([InlineKeyboardButton("❌ 终止房间", callback_data="dice_end")])
        return InlineKeyboardMarkup(rows)
    if uid in game.out:
        return InlineKeyboardMarkup([[InlineKeyboardButton("🔄 刷新界面", callback_data="dice_refresh")]])
    if uid != game.actor or game.phase != "playing":
        return InlineKeyboardMarkup([[InlineKeyboardButton("🎲 看牌", callback_data="dice_see")]])
    row1 = [InlineKeyboardButton("🎲 看牌", callback_data="dice_see")]
    # 无合法加码（数量点数双顶满）时隐藏「加码」，避免用户点了才被拒
    if dice_min_raise(game):
        row1.append(InlineKeyboardButton("➕ 加一个", callback_data="dice_raise"))
    rows = [row1]
    row2 = []
    if game.bid:
        row2.append(InlineKeyboardButton("🎯 开骰", callback_data="dice_open"))
    row2.append(InlineKeyboardButton("🔄 刷新", callback_data="dice_refresh"))
    rows.append(row2)
    return InlineKeyboardMarkup(rows)


async def dice_table_text(game, app):
    wild = sget("DICE_WILD_ONE")
    _n = len(game.players)
    _rules = ("｜1=万能" if wild else "｜无万能局")
    if _dice_rule_on("DICE_STRAIGHT_ZERO", _n): _rules += "｜顺子=0"
    if _dice_rule_on("DICE_LEOPARD_BONUS", _n): _rules += "｜豹子+2/+1"
    if _dice_duel_mode(game): _rules += "｜一把定胜负"
    lines = [f"🎲 大话骰（吹牛）｜第 {game.hand_no} 手",
             f"💰 奖池 {game.pot}｜底注 {sget('DICE_ANTE')}｜在场骰子 {game.total_dice()} 颗" + _rules]
    if game.last_action:
        lines.append(f"🔔 上一手：{game.last_action}")
    if game.bid:
        bc, bf, bidder = game.bid
        lines.append(f"🎙 当前叫牌：{bc}个{bf}（{await get_name(app, bidder)}）")
    cur = game.actor if game.phase == "playing" else None
    lines.append("━━━━━━━━━━━━━━━━━")
    if cur:
        # 2026-09-11 用户要求：行动提示放到分隔线之后、玩家列表之前；并与超时提示合并为一行
        lines.append(f"⏳ <b>{await get_name(app, cur)}</b> 行动中（加码或开骰）｜{sget('DICE_THINK_SECONDS')} 秒未操作自动开骰")
    # 两段式玩家行（§4.14 铁律：名字一行、数据一行全角缩进，手机端不挤）
    # 2026-09-11 用户要求：👉 留在行首，非行动者补 3 个半角空格占位 → 序号落在同一列
    for index, uid in enumerate(game.players, 1):
        mark = "👉 " if uid == cur else "   "
        lines.append(f"{mark}{index}. {await get_name(app, uid)}")
        if uid in game.out:
            lines.append("　　💀 已出局")
        else:
            lines.append(f"　　🎲{game.dice[uid]}颗 🟢 余{game.chips[uid]}")
    lines.append("💡 群里打「6个3」叫牌｜「➕ 加一个」懒得算｜「🎯 开骰」掀盅｜点「🎲 看牌」弹窗看骰")
    return "\n".join(lines)


async def show_dice_action(game, app):
    cur = game.actor if game.phase == "playing" else None
    # 牌桌统一删旧发新（见 _sync_jinhua_msg），始终顶到群最底部；
    # 行动提示已并入牌桌文本（见 dice_table_text），此处不再追加第二句
    if cur:
        await _sync_jinhua_msg(game, app, await dice_table_text(game, app), dice_buttons(game, cur))
    else:
        await _sync_jinhua_msg(game, app, await dice_table_text(game, app), dice_buttons(game, game.owner_id))


async def start_dice_turn_timer(game, app):
    game.cancel_timer()
    # 先判终局：showdown 直接结算，绝不留一个带按钮但不结算的死界面（牌局卡死）
    if game.phase == "showdown":
        await settle_dice(game, app); return
    await show_dice_action(game, app)
    if game.phase != "playing": return
    uid = game.actor

    async def timeout_action():
        await asyncio.sleep(sget("DICE_THINK_SECONDS"))
        if game.settled or game.phase != "playing" or game.actor != uid: return
        _who = await get_name(app, uid)
        if game.bid:
            ok, _ = game.action(uid, "open")
            if not ok: return
            game.last_action = f"{_who} 超时自动开骰"
            # 超时是玩家掉骰子的直接原因，必须让群里知道发生了什么
            schedule_notice_delete(app, game.chat_id,
                                   await safe_send(app.bot, game.chat_id,
                                                   f"⏰ {_who} 超时未行动（{sget('DICE_THINK_SECONDS')}秒），自动开骰。"))
            await _dice_resolve_and_continue(game, app, uid)
        else:
            mr = dice_min_raise(game)
            if not mr: return
            game.action(uid, "bid", mr)
            game.last_action = f"{_who} 超时自动叫 {mr[0]}个{mr[1]}"
            schedule_notice_delete(app, game.chat_id,
                                   await safe_send(app.bot, game.chat_id,
                                                   f"⏰ {_who} 超时未叫牌（{sget('DICE_THINK_SECONDS')}秒），自动叫 {mr[0]}个{mr[1]}。"))
            await start_dice_turn_timer(game, app)
    game.turn_task = asyncio.create_task(timeout_action())


async def _dice_resolve_and_continue(game, app, opener):
    """掀盅亮牌 → 判定 → 掉骰子 → 重摇续局 / 终局结算。"""
    bc, bf, bidder = game.bid
    actual, loser, n_face, n_one = game.resolve_open(opener)
    bidder_name = await get_name(app, bidder)
    opener_name = await get_name(app, opener)
    loser_name = await get_name(app, loser)
    lines = [f"🎯 开骰！（{opener_name} 开 {bidder_name} 的 {bc}个{bf}）", "亮盅："]
    wild = sget("DICE_WILD_ONE")
    _n = len(game.players)
    _straight_on = _dice_rule_on("DICE_STRAIGHT_ZERO", _n)
    _leopard_on = _dice_rule_on("DICE_LEOPARD_BONUS", _n)
    _bonus_total = 0
    for u in game.alive():
        _hand = " ".join(map(str, game.hands[u]))
        if _straight_on and _dice_is_straight(game.hands[u], wild):
            _hand += "（顺子·算0个）"
        elif _leopard_on:
            _lb = _dice_leopard_bonus(game.hands[u], bf, wild)
            if _lb:
                _hand += f"（{_dice_leopard_kind(game.hands[u], wild)}·{bf}点+{_lb}）"
                _bonus_total += _lb
        lines.append(f"　{await get_name(app, u)}：{_hand}")
    if wild and bf != 1:
        calc = f"{bf}点×{n_face} + 万能1×{n_one} = "
    else:
        calc = ""
    if _bonus_total:
        calc += f"豹子+{_bonus_total} → "
    _duel = _dice_duel_mode(game)      # 一把定胜负：输家直接出局、本局立即结算
    _pen = "输" if _duel else "掉一颗骰子"
    tail = f"{calc}实际 {actual} 个 ≥ 叫 {bc} 个 → {bidder_name} 没吹，{loser_name}（开骰者）{_pen}" \
        if loser is opener else \
        f"{calc}实际 {actual} 个 < 叫 {bc} 个 → {bidder_name} 吹牛实锤，{_pen}"
    elim = game.apply_loss(loser)
    if game.phase == "showdown":
        _end = "本局结束！" if _duel else f"{loser_name} 出局！"
        # 终局必须亮盅：此前两人局只发判定句、不发牌面，群友无法核对「谁该输」
        # （2026-09-11 用户报障的现场就是这种「只看到一句结论、看不到骰子」）
        schedule_notice_delete(app, game.chat_id,
                               await safe_send(app.bot, game.chat_id,
                                               "\n".join(lines + [f"{tail}，{_end}"])))
        await settle_dice(game, app)
        return
    nxt_name = await get_name(app, game.starter_uid)
    tail += f"（剩 {game.dice[loser]} 颗）" if not elim else ""
    lines.append(tail)
    lines.append(f"全员重摇，{nxt_name} 先叫。")
    schedule_notice_delete(app, game.chat_id, await safe_send(app.bot, game.chat_id, "\n".join(lines)))
    await start_dice_turn_timer(game, app)


async def settle_dice(game, app):
    if game.settled: return
    game.settled = True; game.cancel_timer(); game.cancel_wait()
    try:
        async with user_wallet_locks([u for u in game.players if u >= 0]):
            survivors = game.alive()
            if survivors:
                # 一把定胜负时可能有多人存活 → 奖池平分（余数给靠前的，总额严格等于奖池）
                _base, _rest = divmod(game.pot, len(survivors))
                for _i, uid in enumerate(survivors):
                    game.chips[uid] += _base + (1 if _i < _rest else 0)
            else:
                # 极端兜底（理论不可达）：无人存活 → 底注原路退回，禁止积分凭空消失
                for uid in game.players:
                    game.chips[uid] = game.initial_chips.get(uid, game.chips[uid])
            for uid in game.players:
                game_chips[game.chat_id][uid] += game.chips[uid] - game.initial_chips.get(uid, game_chips[game.chat_id][uid])
        save_data(); await asyncio.to_thread(force_save_now)
        names = {uid: await get_name(app, uid) for uid in game.players}
        lines = ["🎲 <b>大话骰结算</b>", "━━━━━━━━━━━━━━━━━", ""]
        if survivors:
            if len(survivors) == 1:
                lines.append(f"🏆 幸存者：{names.get(survivors[0])}｜通吃奖池 {game.pot}")
            else:
                lines.append(f"🏆 幸存者 {len(survivors)} 人平分奖池 {game.pot}（每人 {game.pot // len(survivors)}）")
                lines.append("　" + "、".join(names.get(u, "") for u in survivors))
        else:
            lines.append("🏆 本局无人存活，底注已原路退回")
        lines.append("")
        lines.append("终局牌面：")
        for uid in game.players:
            st = "💀出局" if uid in game.out else f"🎲剩{game.dice[uid]}颗"
            lines.append(f"　{names[uid]}：{st}｜底注 {game.paid.get(uid, 0)}")
        # 抽水先算（官方模式）
        _nets = {uid: game.chips[uid] - game.initial_chips[uid] for uid in game.players}
        rake_per = calc_rake(_nets)[1] if game.mode == "official" else {}
        lines.append("")
        lines.append("投入 / 盈亏：")
        for uid in game.players:
            net = _nets[uid]
            r_amt = rake_per.get(uid, 0)
            r_txt = f"（实收 {net - r_amt}，含抽水{r_amt}）" if r_amt else ""
            lines.append(f"　{names[uid]}：投入 {game.paid.get(uid, 0)}｜盈亏 {net:+d}{r_txt}")
        if game.mode == "official":
            record_game_flows(game.chat_id, _nets, "大话骰")
            await commit_rake(app, game.chat_id, rake_per, "大话骰")
            for uid in game.players:
                if uid < 0: continue
                games_played[game.chat_id][uid] += 1
                _gain = _nets[uid] - int(rake_per.get(uid, 0) or 0)
                if _gain > 0:
                    _oe = _earn_get(game.chat_id, uid)
                    _earn_add(game.chat_id, uid, _gain)
                    await _check_level_change(app, game.chat_id, uid, _oe, _earn_get(game.chat_id, uid))
            _top = max(survivors, key=lambda u: _nets.get(u, 0)) if survivors else None
            if _top is not None and _nets.get(_top, 0) > 0:
                await broadcast_big_win(app, game.chat_id, _top, "🎲 大话骰", _nets[_top],
                                        f"🎲 终局剩骰：{game.dice.get(_top, 0)} 颗")
        await safe_delete(app.bot, game.chat_id, game.game_msg_id)
        delivered = await safe_send_long(app.bot, game.chat_id, "\n".join(lines), parse_mode="HTML")
        if sget("SETTLE_DELETE_SECONDS") > 0:
            schedule_delete(app, game.chat_id, delivered, sget("SETTLE_DELETE_SECONDS"))
    except Exception:
        logger.exception("大话骰结算异常")
    finally:
        if active_dice_games.get(game.chat_id) is game: active_dice_games.pop(game.chat_id, None)
        if game.mode == "official":
            for uid in game.players: await emergency_if_needed(game.chat_id, uid, app)
        save_data(); await asyncio.to_thread(force_save_now)


async def refund_dice(game, app, notice):
    """终止大话骰：底注扣在局内副本（钱包结算前不动），弃局即作废副本 = 全额退款。"""
    game.cancel_timer(); game.cancel_wait(); game.phase = "cancelled"
    if active_dice_games.get(game.chat_id) is game: active_dice_games.pop(game.chat_id, None)
    await safe_delete(app.bot, game.chat_id, game.game_msg_id)
    # 解散提示挂自动回收：此前是裸 safe_send，「房间已解散」永久堆在群里
    schedule_notice_delete(app, game.chat_id, await safe_send(app.bot, game.chat_id, notice))
    save_data()


async def start_dice_wait_timeout(game, app):
    game.cancel_wait()
    async def countdown():
        _wait = sget("ROOM_WAIT_TIMEOUT")
        await asyncio.sleep(_wait)
        if game.phase != "waiting" or active_dice_games.get(game.chat_id) is not game: return
        if len(game.players) >= 2:
            if game.start():
                await _dice_notify_dropped(game, app)
                await start_dice_turn_timer(game, app)
        else:
            await refund_dice(game, app, f"⌛ 大话骰等待 {_wait} 秒不足 2 人，房间已自动解散。")
    # 必须把任务挂到 game.wait_task 上：
    # ① 不启动 → 等待房永不解散（2026-09-11 事故）；
    # ② 不持有引用 → 任务可能被事件循环 GC 掉。
    game.wait_task = asyncio.create_task(countdown())


async def _dice_notify_dropped(game, app):
    """开局时因底注不足被剔除的玩家，群里明确告知（避免「我怎么没在局里」的困惑）。"""
    if not game.dropped: return
    _names = "、".join([await get_name(app, u) for u in game.dropped])
    schedule_notice_delete(app, game.chat_id, await safe_send(app.bot, game.chat_id,
                    f"⚠️ {_names} 积分不足 {sget('DICE_ANTE')} 底注，本局未参与（余额可先签到/兑换）。"))


async def cmd_dice(update, context):
    if not await need_auth(update, context): return
    if not await _game_gate(update, context, "dice"): return
    if not await require_group_chat(update, "大话骰", "dice", context): return
    cid, uid = update.effective_chat.id, update.effective_user.id
    game = active_dice_games.get(cid)
    if game:
        if game.phase != "waiting":
            await send_reply(update, context, "当前已有进行中的大话骰。"); return
        room_name, _ = poker_room_of(cid, uid, exclude_game=game)
        if room_name:
            await send_reply(update, context, f"⚠️ 你已在 {room_name} 房间，请先结束再加入大话骰。"); return
        if len(game.players) >= sget("DICE_MAX_PLAYERS"):
            await send_reply(update, context, "等待房间已满。"); return
        if game.add(uid):
            await update_dice_waiting(game, context.application); await send_reply(update, context, "已加入当前等待房间。")
        else: await send_reply(update, context, "你已在等待房间中。")
        return
    room_name, _ = poker_room_of(cid, uid)
    if room_name:
        await send_reply(update, context, f"⚠️ 你已在 {room_name} 房间，请先结束再开大话骰。"); return
    if game_chips[cid][uid] < sget("MIN_ENTRY_CHIPS"):
        await send_reply(update, context, f"❌ 进入大话骰至少需要 {sget('MIN_ENTRY_CHIPS')} 积分。"); return
    game = DiceGame(cid, uid, current_game_mode()); game.add(uid); active_dice_games[cid] = game
    msg = await safe_send(context.bot, cid, await dice_waiting_text(game, context.application),
                          reply_markup=dice_buttons(game, uid))
    if msg:
        game.game_msg_id = msg.message_id
        await start_dice_wait_timeout(game, context.application)





















# ==================== 通用 sendDice 游戏（足球/篮球/飞镖/保龄球） ====================

# 配置：每个游戏一个条目。bets 每项为 (key, 按钮标签, 赢的value集合, 赔率分子, 赔率分母)
























# ==================== 梭哈（Five Card Stud） ====================
# treys suit_int 是位掩码（s=1,h=2,d=4,c=8），映射为梭哈花色优先级 ♠>♥>♦>♣
























# ==================== 炸金花（三张牌，闷牌偷鸡） ====================
JINHUA_ANTE = 200        # 炸金花底注
JINHUA_BASE = 100        # 闷牌单位（看牌者跟注/加注金额为其 2 倍）
RACE_ODDS_CAP = 10.0     # 赔率上限（倍）。0=无上限。防低胜率马一把押中爆出几万分冲垮经济
JINHUA_SEEN_DOUBLE = 0   # 炸金花看牌者投注加倍开关（1=经典规则看牌×2；0=看牌闷牌同价，群反馈中途看牌被加倍劝退）
DAILY_RESET_TIME = "00:00"   # 每日重置时刻（排位分重置、德州日榜翻日等）
DAILY_RESET_ENABLED = 1      # 每日重置开关（后台「定时任务」可关；关闭期间到点跳过，重开后从下一周期生效）
LEADERBOARD_TIME = "23:50"   # 德州当日榜定时推送时刻
LEADERBOARD_ENABLED = 1      # 德州日榜推送开关
RACE_HOURLY_MINUTE = 0       # 赛车每小时自动开赛：整点后第几分钟
RACE_AUTO_ENABLED = 1        # 赛车自动开赛总开关（仍受时段/分钟与赛车游戏开关限制）
RACE_HOURLY_START = 0        # 自动开赛时段-起始点(几点,含)，如 9 = 9点起才开赛
ADMIN_REPORT_TIME = "09:00"  # 经营日报推送时刻（私聊管理员）
ADMIN_REPORT_ENABLED = 1     # 经营日报推送开关
RACE_HOURLY_END = 23         # 自动开赛时段-结束点(几点,含)，如 22 = 22点那场仍开；
                             # 起始>结束 = **跨午夜档**（如 18→2 = 18:00 到次日 02:59），2026-09-11 用户要求


def _race_hour_in_window(start, end, hour):
    """自动开赛时段判定（**支持跨午夜**，2026-09-11 用户报障）。

    群友要的档期是「18 点到凌晨 2 点」，旧实现是 `start <= h <= end`，
    起始大于结束直接恒 False → 跨夜档**根本设不出来**。
    现行语义：start <= end = 普通档（同日区间）；start > end = 跨夜档。
    例：18→2 命中 18/19/.../23/0/1/2，不命中 3~17。
    """
    start = max(0, min(23, int(start)))
    end = max(0, min(23, int(end)))
    hour = int(hour) % 24
    if start <= end:
        return start <= hour <= end
    return hour >= start or hour <= end


def _race_window_text(start, end):
    """时段的可读文案；跨夜档在终点前加「次日」（后台状态卡/页面提示共用）。"""
    start = max(0, min(23, int(start)))
    end = max(0, min(23, int(end)))
    return f"{start:02d}:00–{'次日' if start > end else ''}{end:02d}:59"


# ---------- 赛车系统加奖（2026-09-11 用户要求：群友嫌赛车没人玩，加个"白拿"钩子） ----------
RACE_SUBSIDY_ENABLED = 1      # 系统加奖开关
RACE_SUBSIDY_AMOUNT = 100     # 每场加奖金额（积分）——押中者按注额比例分，无人押中则不发、不计额度
RACE_SUBSIDY_MIN_PLAYERS = 2  # 加奖生效的最少下注人数（防单人自押自薅）
RACE_SUBSIDY_DAILY_CAP = 1000 # 每群每日加奖上限（0=不限），防连续开赛把积分放水
RACE_SUBSIDY_AUTO_ONLY = 1    # 加奖只给「定时自动开赛」的赛车（2026-09-11 用户要求：个人发起的赛车不派奖）


def race_subsidy_banner(auto_started=True):
    """赛车面板上的加奖预告（开关关 / 金额 0 / 个人发起 → 空串，不显示多余行）。"""
    if not sget("RACE_SUBSIDY_ENABLED"): return ""
    if sget("RACE_SUBSIDY_AUTO_ONLY") and not auto_started: return ""
    amt = max(0, int(sget("RACE_SUBSIDY_AMOUNT")))
    if amt <= 0: return ""
    n = max(1, int(sget("RACE_SUBSIDY_MIN_PLAYERS")))
    return f"🎁 本场系统加奖 {amt} 积分（押中者按注额分，需 ≥{n} 人下注）"


def race_subsidy_for(cid, date, n_bettors, auto_started=True):
    """本场可发的加奖金额（0 = 不发）。五道闸：开关 → 来源 → 金额 → 人数门槛 → 当日上限。"""
    if not sget("RACE_SUBSIDY_ENABLED"): return 0
    if sget("RACE_SUBSIDY_AUTO_ONLY") and not auto_started: return 0   # 个人发起的赛车不派奖
    amt = max(0, int(sget("RACE_SUBSIDY_AMOUNT")))
    if amt <= 0: return 0
    if n_bettors < max(1, int(sget("RACE_SUBSIDY_MIN_PLAYERS"))): return 0
    cap = max(0, int(sget("RACE_SUBSIDY_DAILY_CAP")))
    if cap and race_subsidy_by_day[date][cid] + amt > cap: return 0
    return amt


def race_subsidy_split(subsidy, bets, winner):
    """加奖按「押中者的注额比例」拆分，返回 {uid: 金额}。
    整数除法余数补给押注最多的那个人 —— 总额严格等于 subsidy，不许凭空多出/少了积分。"""
    if subsidy <= 0: return {}
    winners = [(uid, bets[uid].get(winner, 0)) for uid in bets if bets[uid].get(winner, 0) > 0]
    if not winners: return {}          # 无人押中 → 不发（额度也不消耗），避免白送钱给庄家
    tot = sum(b for _, b in winners)
    alloc, used = {}, 0
    for uid, b in winners:
        share = subsidy * b // tot
        alloc[uid] = share; used += share
    rest = subsidy - used
    if rest:
        top = max(winners, key=lambda x: x[1])[0]
        alloc[top] = alloc.get(top, 0) + rest
    return alloc
INHERIT_DAILY_LIMIT = 0      # 每人每日转赠总额上限（0=不限，防小号互刷）
MALL_MIN_AGE_DAYS = 0        # 商城兑换门槛：与机器人首次互动满 N 天（0=不限）
MALL_MIN_ACTIVE_DAYS = 0     # 商城兑换门槛：有游戏盈亏记录的天数 ≥N（0=不限）
FUND_FLOW_ALERT = 10000      # 资金流审查页：单对单向累计超过此值标红
BROADCAST_ENABLED = 1        # 大奖战报自动广播开关（推送到其他授权群，制造气氛）
BROADCAST_MIN_AMOUNT = 20000 # 战报阈值：单局净赢 ≥ 此值才广播
BACKUP_INTERVAL_HOURS = 24   # 自动备份间隔（小时），启动时读取
BACKUP_ENABLED = 1           # 自动备份开关（job 常驻，回调里查开关，保存即时生效）
RAKE_ENABLED = 1             # 游戏抽水总开关（官方模式结算后对赢家净赢抽成，回收销毁不回流奖池）
RAKE_PERCENT = 10            # 抽水比例（%）：赢家净赢 × 比例
RAKE_MIN_NET = 0             # 抽水门槛：单局净赢低于此值不抽（0=全抽）
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
        if game_chips[self.chat_id][uid] < sget("MIN_ENTRY_CHIPS"): return False
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
            ante = min(sget("JINHUA_ANTE"), self.chips[uid]); self.chips[uid] -= ante; self.total_bet[uid] += ante; self.pot += ante
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
        """该玩家本轮应投入的实际金额 = 闷牌单位 × (看牌 2 倍 / 闷牌 1 倍)。
        加倍开关关闭时看牌与闷牌同价。"""
        mult = 2 if (uid in self.seen and sget("JINHUA_SEEN_DOUBLE")) else 1
        return self.current_bet * mult

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
        if extra < sget("JINHUA_BASE"): return False, f"最低加注为 {sget('JINHUA_BASE')}"
        if uid in self.raise_locked: return False, "短全下后已行动玩家只能跟注或弃牌"
        # 先按校验后的值计算目标投入，余额不足直接拒绝，绝不先改 current_bet
        mult = 2 if (uid in self.seen and sget("JINHUA_SEEN_DOUBLE")) else 1
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
        mult = 2 if (uid in self.seen and sget("JINHUA_SEEN_DOUBLE")) else 1
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
            if raise_units * mult < sget("JINHUA_BASE"):
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
                penalty = min(2 * sget("JINHUA_BASE"), self.chips[uid])
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
            if kind == "fold":
                # 跟平后也必须允许弃牌止损（此前只开放开牌/加注，玩家被锁死）
                self.folded.add(uid)
                self.acted.add(uid)
                if len([p for p in self.players if p not in self.folded]) <= 1:
                    self.phase = "showdown"
                return True, "弃牌"
            if kind == "raise":
                ok, desc = self._do_raise(uid, extra)
                if not ok: return False, desc
                # 关键：open_pending 里加注后必须重新推进回合，否则 actor_idx 停在
                # 已行动的玩家上 → current() 恒为 None → 无按钮无计时器，整局冻死
                alive2 = [p for p in self.players if p not in self.folded]
                if len(alive2) <= 1: self.phase = "showdown"
                elif self._round_done(): self.phase = "open_pending"
                else: self._next()
                return True, desc
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
    return f"🌸 新一局炸金花\n发起人：{await get_name(app, game.owner_id)}\n\n已加入：\n" + "\n".join(players) + f"\n\n点击加入，发起人可立即开始。\n⏰ 满 2 人后 {sget('ROOM_WAIT_TIMEOUT')} 秒自动开局，不足 2 人 {sget('ROOM_WAIT_TIMEOUT')} 秒后自动解散。"


async def update_jinhua_waiting(game, app):
    rows = [[InlineKeyboardButton("📥 加入游戏", callback_data="jh_join")]]
    if len(game.players) >= 2: rows.append([InlineKeyboardButton("🎮 开始游戏", callback_data="jh_start")])
    rows.append([InlineKeyboardButton("❌ 终止房间", callback_data="jh_end")])
    await safe_edit(app.bot, game.chat_id, game.game_msg_id, await jinhua_waiting_text(game, app), reply_markup=InlineKeyboardMarkup(rows))


async def jinhua_table_text(game, app):
    lines = [
        "🌸 炸金花",
        f"💰 奖池 {game.pot}｜单注 {game.current_bet}" + ("（看牌者×2）" if sget("JINHUA_SEEN_DOUBLE") else ""),
    ]
    if game.last_action:
        lines.append(f"🔔 上一手：{game.last_action}")
    current = game.current() if game.phase == "betting" else None
    lines.append("━━━━━━━━━━━━━━━━━")
    if current:
        # 2026-09-11 用户要求：行动提示放到分隔线之后、玩家列表之前；并与超时提示合并为一行
        _need = max(0, game._target(current) - game.round_bets[current])
        lines.append(f"⏳ <b>{await get_name(app, current)}</b> 行动中｜需补 {_need}｜{sget('TURN_TIMEOUT')} 秒未操作自动弃牌")
    # 紧凑排版：每人 1 行；👉 留在行首，非行动者补 3 个半角空格占位 → 序号落在同一列
    for index, uid in enumerate(game.players, 1):
        status = "❌弃" if uid in game.folded else "🔥全下" if uid in game.all_in else "🟢"
        seen_mark = "👁" if uid in game.seen else "🎴"
        mark = "👉 " if uid == current else "   "
        lines.append(f"{mark}{index}. {await get_name(app, uid)} {seen_mark}{status} 投{game.total_bet[uid]} 余{game.chips[uid]}")
    return "\n".join(lines)


def jinhua_buttons(game, uid):
    """紧凑布局：非行动玩家仅「看牌」；行动玩家 4 行
    （看牌单独首行 → 弃牌|跟注|比牌 → 加注|刷新 → 全下）。
    2026-09-11 用户要求（防误触）：看牌独占首行、弃牌退到第二行最左，
    与高频的跟注/加注拉开距离。"""
    if uid not in game.folded:
        label = "🃏 手牌" if uid in game.seen else "👁 看牌"   # 统一 emoji+2字（同行等宽，2026-09-10 对齐改造）
        if uid != game.current():
            return InlineKeyboardMarkup([[InlineKeyboardButton(label, callback_data="jh_see")]])
    else:
        return InlineKeyboardMarkup([[InlineKeyboardButton("🔄 刷新界面", callback_data="jh_refresh")]])
    to_call = max(0, game._target(uid) - game.round_bets[uid])
    # 2026-09-11 用户要求撤销「emoji+2字」改造：金额回到按钮上（快捷档行已删）
    # 2026-09-11 用户要求（防误触）：看牌独占首行；弃牌退到第二行最左，跟注/比牌在其右
    rows = [[InlineKeyboardButton(label, callback_data="jh_see")]]
    row_call = [InlineKeyboardButton("❌ 弃牌", callback_data="jh_fold"),
                InlineKeyboardButton("✅ 过牌" if not to_call else "✅ 跟注", callback_data="jh_call")]
    if sum(1 for p in game.players if p not in game.folded) >= 2:
        row_call.append(InlineKeyboardButton("⚔️ 比牌", callback_data="jh_compare_menu"))
    rows.append(row_call)
    row_raise = []
    if uid not in game.raise_locked and game.chips[uid] >= to_call + sget("JINHUA_BASE"):
        row_raise.append(InlineKeyboardButton(f"🚀 加注 {sget('JINHUA_BASE')}", callback_data=f"jh_raise_{sget('JINHUA_BASE')}"))
    row_raise.append(InlineKeyboardButton("🔄 刷新", callback_data="jh_refresh"))
    rows.append(row_raise)
    if game.chips[uid] > 0:
        rows.append([InlineKeyboardButton(f"🔥 全下 {game.chips[uid]}", callback_data="jh_allin")])
    return InlineKeyboardMarkup(rows)


async def _sync_jinhua_msg(game, app, text, kb):
    """渲染唯一权威牌桌消息：**删旧发新**，全群始终只有这一条，且永远停在群最底部。

    2026-09-11 用户明确：炸金花与大话骰**统一删旧发新**。
    （早前「原地编辑」的注释把「群友反馈乱跳」归因成删旧发新——**那是误记**：
    用户当时的抱怨是界面文本与按钮乱，跟发消息方式无关。）
    原地编辑位置不动，会被后来的聊天顶上去，群友就看不到轮到谁了。
    加锁避免快速连续操作（连点/超时与点击并发）时出现两条牌桌。
    """
    async with game._render_lock:
        old_id = game.game_msg_id
        msg = await safe_send(app.bot, game.chat_id, text, reply_markup=kb, parse_mode="HTML")
        if msg:
            game.game_msg_id = msg.message_id
            if old_id and old_id != game.game_msg_id:
                await safe_delete(app.bot, game.chat_id, old_id)


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
        text = f"{await jinhua_table_text(game, app)}\n\n💡 已跟平：可 <b>弃牌</b> 止损、<b>比牌/开牌</b> 定胜负，或 <b>继续加注</b> 偷鸡。"
        kb = InlineKeyboardMarkup([
            [InlineKeyboardButton("❌ 弃牌", callback_data="jh_fold"),
             InlineKeyboardButton("⚔️ 比牌", callback_data="jh_compare_menu"),
             InlineKeyboardButton("🃏 开牌比大小", callback_data="jh_open")],
            [InlineKeyboardButton(f"🚀 继续加注 {sget('JINHUA_BASE')}", callback_data=f"jh_raise_{sget('JINHUA_BASE')}"),
             InlineKeyboardButton("🔄 刷新", callback_data="jh_refresh")],
        ])
        await _sync_jinhua_msg(game, app, text, kb)
        return
    uid = game.current()
    if uid is None:
        if game.phase == "showdown": await settle_jinhua(game, app)
        elif game.phase == "betting":
            # 自愈兜底：行动指针悬空时自动推进，任何路径都不允许牌局无声冻死
            if game._round_done():
                game.phase = "open_pending"
                await show_jinhua_action(game, app)
            else:
                nxt = game._next()
                if nxt: await start_jinhua_turn_timer(game, app)
        return
    # 行动提示已并入牌桌文本（见 jinhua_table_text），此处不再追加第二句
    await _sync_jinhua_msg(game, app, await jinhua_table_text(game, app), jinhua_buttons(game, uid))


async def start_jinhua_turn_timer(game, app):
    game.cancel_timer()
    await show_jinhua_action(game, app)
    if game.phase in ("open_pending", "showdown"):
        # open_pending 兜底：跟平阶段无"当前玩家"可计时，若全员不动（如掉线）牌局会永久卡死。
        # 挂一个看门狗：超时后仍处于 open_pending 则自动开牌结算（settle_jinhua 幂等，重复触发无害）。
        if game.phase == "open_pending":
            async def _open_pending_timeout():
                await asyncio.sleep(JINHUA_OPEN_PENDING_TIMEOUT)
                if game.settled or game.phase != "open_pending": return
                game.last_action = "跟平阶段超时，自动开牌结算"
                await settle_jinhua(game, app)
            game.turn_task = asyncio.create_task(_open_pending_timeout())
        return
    uid = game.current()

    async def timeout_action():
        await asyncio.sleep(sget("TURN_TIMEOUT"))
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
                lines.append(f"　{names[uid]}：弃牌")
            else:
                cards = "  ".join(card_str(c) for c in game.hands[uid])
                lines.append(f"　{names[uid]}：{cards}｜{hand_types.get(uid, '')}")
        lines.append("")
        lines.append("派奖：")
        for uid, hand, amount, details, _ in sorted(result, key=lambda item: item[2], reverse=True):
            if amount > 0:
                lines.append(f"　{names[uid]}：{hand}｜+{amount}（{'，'.join(f'{pool}+{value}' for pool, value in details)}）")
        # 抽水先算（官方模式），面板「盈亏」行直接带实收
        _nets = {uid: game.chips[uid] - game.initial_chips[uid] for uid in game.players} \
            if game.mode == "official" else {}
        rake_per = calc_rake(_nets)[1] if _nets else {}
        lines.append("")
        lines.append("投入 / 盈亏：")
        for uid in game.players:
            net = game.chips[uid] - game.initial_chips[uid]
            if game.mode == "official":
                jinhua_profit_by_date[date][game.chat_id][uid] += net
            r_amt = rake_per.get(uid, 0)
            r_txt = f"（实收 {net - r_amt}，含抽水{r_amt}）" if r_amt else ""
            lines.append(f"　{names[uid]}：投入 {game.total_bet[uid]}｜盈亏 {net:+d}{r_txt}")
        # 资金流审查：官方模式把本局人对人净转移记账（防"故意输牌/比牌倒赔送分"）
        if game.mode == "official":
            record_game_flows(game.chat_id, _nets, "金花")
            await commit_rake(app, game.chat_id, rake_per, "金花")
            # 累计参与局数（归零门槛）+ 赢分计入累计获得 + 升级通知
            for uid in game.players:
                if uid < 0: continue
                games_played[game.chat_id][uid] += 1
                # 实际到手 = 净赢 - 本局抽水（抽水已在上面扣除）
                _gain = (game.chips[uid] - game.initial_chips.get(uid, 0)) - int(rake_per.get(uid, 0) or 0)
                if _gain > 0:
                    _oe = _earn_get(game.chat_id, uid)
                    _earn_add(game.chat_id, uid, _gain)
                    await _check_level_change(app, game.chat_id, uid, _oe, _earn_get(game.chat_id, uid))
        # 大奖战报：官方模式单局净赢超阈值 → 广播其他授权群（豹子特别标注）
        if game.mode == "official":
            top_uid, top_net = None, 0
            for uid in game.players:
                _n = game.chips[uid] - game.initial_chips[uid]
                if _n > top_net: top_uid, top_net = uid, _n
            if top_uid and top_net > 0:
                _ht = str(hand_types.get(top_uid, ""))
                detail = f"🃏 牌型：{_ht}{' 🔥豹子！' if '豹子' in _ht else ''}"
                await broadcast_big_win(app, game.chat_id, top_uid, "♣️ 炸金花", top_net, detail)
        if getattr(game, "penalty_log", []):
            lines.extend(["", "比牌惩罚："])
            for payer, payee, amount in game.penalty_log:
                lines.extend([f"{names.get(payer, str(payer))} 倒赔 {amount} 给 {names.get(payee, str(payee))}", ""])
        # 累计盈利榜单独发一条（2026-09-11 用户要求：结算正文太长像刷屏，榜单拆开发）
        _rank_lines = None
        if game.mode == "official":
            rank = sorted(jinhua_profit_by_date[date][game.chat_id].items(), key=lambda item: item[1], reverse=True)[:50]
            if rank:
                _rank_lines = ["🏆 <b>当日炸金花累计盈利榜</b>", "━━━━━━━━━━━━━━━━━"]
                _rank_lines.extend([f"{rank_marker(index)} {names.get(uid) or await get_name(app, uid)}：{amount:+d}" for index, (uid, amount) in enumerate(rank, 1)])
        await safe_delete(app.bot, game.chat_id, game.game_msg_id)
        delivered = await safe_send_long(app.bot, game.chat_id, "\n".join(lines), parse_mode="HTML")
        if sget("SETTLE_DELETE_SECONDS") > 0:
            schedule_delete(app, game.chat_id, delivered, sget("SETTLE_DELETE_SECONDS"))
        await send_settle_rank(app, game.chat_id, _rank_lines)
        if delivered is None:
            schedule_notice_delete(app, game.chat_id, await safe_send(app.bot, game.chat_id, "⚠️ 炸金花已完成结算，但详细结算消息发送失败。"), kind="settle")
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
        _wait = sget("ROOM_WAIT_TIMEOUT")
        await asyncio.sleep(_wait)
        if game.phase != "waiting" or active_jinhua_games.get(game.chat_id) is not game:
            return
        if len(game.players) >= 2:
            if game.start():
                await update_jinhua_table(game, app)
                await start_jinhua_turn_timer(game, app)
        else:
            await refund_jinhua(game, app, f"⌛ 炸金花等待 {_wait} 秒不足 2 人，房间已自动解散。")
    game.wait_task = asyncio.create_task(countdown())


async def refund_jinhua(game, app, notice):
    game.cancel_timer(); game.cancel_wait()
    game.phase = "cancelled"
    if active_jinhua_games.get(game.chat_id) is game:
        active_jinhua_games.pop(game.chat_id, None)
    await safe_delete(app.bot, game.chat_id, game.game_msg_id)
    # 解散提示挂自动回收：此前是裸 safe_send，「已终止」永久堆在群里
    schedule_notice_delete(app, game.chat_id, await safe_send(app.bot, game.chat_id, notice))
    save_data()


async def cmd_jinhua(update, context):
    if not await need_auth(update, context): return
    if not await _game_gate(update, context, "jinhua"): return
    if not await require_group_chat(update, "炸金花", "jinhua", context): return
    cid, uid = update.effective_chat.id, update.effective_user.id
    game = active_jinhua_games.get(cid)
    room_name, _ = poker_room_of(cid, uid, exclude_game=game)
    if room_name:
        await send_reply(update, context, f"⚠️ 你已在 {room_name} 房间，请先结束再开新的扑克游戏。"); return
    mode = game.mode if game and game.phase == "waiting" else current_game_mode()
    if game_chips[cid][uid] < sget("MIN_ENTRY_CHIPS"):
        await send_reply(update, context, f"❌ 进入炸金花至少需要 {sget('MIN_ENTRY_CHIPS')} 积分。"); return
    if game:
        if game.phase != "waiting": await send_reply(update, context, "当前已有进行中的炸金花。"); return
        if game.add(uid):
            await update_jinhua_waiting(game, context.application); await send_reply(update, context, "已加入当前等待房间。")
        else: await send_reply(update, context, "你已在等待房间中。")
        return
    game = JinhuaGame(cid, uid, mode); game.add(uid); active_jinhua_games[cid] = game
    msg = await safe_send(context.bot, cid, await jinhua_waiting_text(game, context.application), reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("📥 加入游戏", callback_data="jh_join")], [InlineKeyboardButton("❌ 终止房间", callback_data="jh_end")]]))
    if msg:
        game.game_msg_id = msg.message_id
        await start_jinhua_wait_timeout(game, context.application)


# ==================== 牛牛 PVP ====================



























async def start_wait_timeout(game, app):
    """德州等待房倒计时：满 2 人自动开局，不足 2 人自动解散。

    倒计时秒数走 game.wait_timeout：排位局可用后台「排位赛」分组单独配置。
    """
    game.cancel_wait()
    async def countdown():
        _wait = game.wait_timeout
        await asyncio.sleep(_wait)
        if game.phase != "waiting" or active_poker_games.get(game.chat_id) is not game:
            return
        if len(game.players) >= 2:
            if game.start():
                await update_poker_table(game, app)
                await start_turn_timer(game, app)
        else:
            await refund_poker(game, app, f"⌛ 德州等待 {_wait} 秒不足 2 人，房间已自动解散。")
    game.wait_task = asyncio.create_task(countdown())


async def cmd_dz(update, context):
    if not await need_auth(update, context): return
    if not await _game_gate(update, context, "texas", ranked=False): return
    if not await require_group_chat(update, "德州扑克", "dz", context): return
    cid, uid = update.effective_chat.id, update.effective_user.id; game = active_poker_games.get(cid)
    room_name, _ = poker_room_of(cid, uid, exclude_game=game)
    if room_name:
        await send_reply(update, context, f"⚠️ 你已在 {room_name} 房间，请先结束再开新的扑克游戏。"); return
    mode = game.mode if game and game.phase == "waiting" else current_game_mode()
    wallet = game_chips
    if wallet[cid][uid] < sget("MIN_ENTRY_CHIPS"):
        label = "积分"
        await send_reply(update, context, f"❌ 进入德州至少需要 {sget('MIN_ENTRY_CHIPS')} {label}。"); return
    if game:
        if game.season:
            await send_reply(update, context, "当前有排位赛房间，请用 /排位 加入或开局。"); return
        if game.phase != "waiting": await send_reply(update, context, "当前已有进行中的德州扑克。"); return
        if game.add(uid):
            await update_poker_waiting(game, context.application); await send_reply(update, context, "已加入当前等待房间。")
        else: await send_reply(update, context, "你已在等待房间中。")
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
    if not forced and len(joined) < sget("SEASON_MIN_PLAYERS"):
        return False, f"需满 {sget('SEASON_MIN_PLAYERS')} 人报名才能开赛（当前 {len(joined)} 人）"
    if forced and not joined:
        return False, "尚无任何人报名，无法强制开赛"
    season_active = True
    season_id = now_bj().strftime("%Y%m%d")
    season_name = name or f"第{season_id}赛季"
    season_start_ts = int(now_bj().timestamp())
    season_end_ts = season_start_ts + sget("SEASON_DAYS") * 86400
    season_points[cid] = defaultdict(int)
    season_games[cid] = defaultdict(int)
    season_rebuy[cid] = defaultdict(int)
    for uid in joined:
        # 赛前兑换的排位分带进新赛季：基准分 = 起始分 + 该玩家已兑换分
        season_points[cid][uid] = _season_base(cid, uid)
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
        eligible = [(uid, val) for uid, val in standings if uid >= 0 and season_games[cid].get(uid, 0) >= sget("SEASON_MIN_GAMES")]
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
                schedule_notice_delete(app, g.chat_id, await safe_send(app.bot, g.chat_id, "⏰ 赛季已结束，本手牌结算不计入排位排名（仍正常派奖）。"))
            except Exception:
                pass
    season_active = False
    season_id = None
    season_name = ""
    season_start_ts = 0
    season_end_ts = 0
    season_points.clear(); season_games.clear(); season_joined.clear(); season_rebuy.clear(); season_profit_by_date.clear()
    season_exchange_bonus.clear()  # 兑换底分随赛季结束清零，下赛季重新累计
    season_lobby_msg.clear()  # 大厅看板为 UI 态，结算后清空，下赛季重新发
    save_data()


def _season_base(cid, uid):
    """当日基准分 = 起始分 + 本赛季累计兑换分。
    兑换分是「额外底分」：每日 0 点重置时保留，且不计入任何盈亏榜（否则花钱买的分会虚增名次）。"""
    return sget("SEASON_START_CHIPS") + season_exchange_bonus.get(cid, {}).get(uid, 0)


def season_daily_refresh(day_key, cids, protected=None):
    """排位赛每日归位：每人分数重置为「起始分+兑换底分」，当日盈亏（当前分-基准分）记入 day_key。

    protected = {(cid, uid)}：进行中的排位局跳过本次归位，等其结算时在 settle_poker 内补记，
    避免打断进行中的牌局。返回实际归位人数（便于日志/测试）。
    """
    protected = protected or set()
    touched = 0
    for cid in cids:
        users = season_points.get(cid)
        if not users: continue
        for uid in list(users.keys()):
            if (cid, uid) in protected: continue
            base = _season_base(cid, uid)
            day_profit = users[uid] - base
            if day_profit:
                season_profit_by_date[day_key][cid][uid] += day_profit
            users[uid] = base
            touched += 1
    return touched


def season_total_profit(cid, uid):
    """赛季总盈亏 = 各日已结算盈亏之和 + 当前未结算当日盈亏（当前分 - 基准分）。
    基准分含兑换底分，故兑换来的分不会虚增排名；仅对已报名玩家有意义。"""
    total = 0
    for d in season_profit_by_date:
        total += season_profit_by_date[d].get(cid, {}).get(uid, 0)
    pts = season_points.get(cid, {}).get(uid)
    if pts is not None:
        total += pts - _season_base(cid, uid)
    return total


async def season_standings_lines(app, cid, uid=None):
    users = season_points.get(cid, {})
    standings = sorted(users.items(), key=lambda x: (-season_total_profit(cid, x[0]), x[0]))
    remain = max(0, int((season_end_ts - now_bj().timestamp()) / 86400))
    lines = [f"🏆 第{season_id}赛季排位榜（{season_name or '排位赛'}）",
             f"⏳ 剩余约 {remain} 天｜上榜需≥{sget('SEASON_MIN_GAMES')}局", "━" * 18]
    if not standings:
        lines.append("暂无数据")
    for i, (u, val) in enumerate(standings[:50], 1):
        g = season_games[cid].get(u, 0)
        tag = "" if g >= sget("SEASON_MIN_GAMES") else f"（{g}局·未达标）"
        marker = "👑" if (i == 1 and u in user_titles and TITLE_GAMBLING_GOD in user_titles[u]) else rank_marker(i)
        bonus = season_exchange_bonus.get(cid, {}).get(u, 0)
        btag = f"｜底分{bonus}" if bonus else ""
        lines.append(f"{marker} {await get_name(app, u, cid=cid, with_title=False)}：总{season_total_profit(cid, u):+d}｜当日{val - _season_base(cid, u):+d}｜{g}局{btag}{tag}")
    # 个人排名行：请求者不在前 50 时，单独补一行真实名次，避免大群看不到自己
    if uid is not None and uid in users:
        full_rank = next((i for i, (u, _) in enumerate(standings, 1) if u == uid), None)
        if full_rank is not None and full_rank > 50:
            g = season_games[cid].get(uid, 0)
            tag = "" if g >= sget("SEASON_MIN_GAMES") else f"（{g}局·未达标）"
            lines.append(f"…（仅显示前 50，你当前第 {full_rank} 名：总{season_total_profit(cid, uid):+d}分{tag}）")
    return lines


async def season_signup(app, cid, uid):
    """报名 / 赛中补报名。处理自动开赛。返回 (ok, key)。key∈joining/started/joined_active。"""
    if season_active:
        season_joined.setdefault(cid, set()).add(uid)
        if uid not in season_points.get(cid, {}):
            season_points[cid][uid] = _season_base(cid, uid)   # 含赛前兑换的底分
            season_games[cid][uid] = 0
            season_rebuy[cid][uid] = 0
        save_data()
        return True, "joined_active"
    season_joined.setdefault(cid, set()).add(uid)
    save_data()
    n = len(season_joined[cid])
    if n >= sget("SEASON_MIN_PLAYERS"):
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
                f"当前报名：<b>{n}/{sget('SEASON_MIN_PLAYERS')}</b> 人\n"
                f"满 {sget('SEASON_MIN_PLAYERS')} 人自动开赛，每人 {sget('SEASON_START_CHIPS')} 分，周期 {sget('SEASON_DAYS')} 天。\n"
                f"已报名：{names_text}\n"
                f"点下面按钮报名，或用 /排位报名 也能一键报名。")
        _ex_row = [[InlineKeyboardButton("💱 积分兑换排位分", callback_data="season_exchange_info")]] if sget("RANKED_EXCHANGE_ENABLED") else []
        markup = InlineKeyboardMarkup([
            [InlineKeyboardButton(f"📝 报名参赛（{n}/{sget('SEASON_MIN_PLAYERS')}）", callback_data="season_signup")],
            *_ex_row,
            [InlineKeyboardButton("❌ 关闭看板", callback_data="season_lobby_close")],
        ])
    else:
        remain = max(0, int((season_end_ts - now_bj().timestamp()) / 86400))
        sn = html.escape(season_name or '排位赛')  # 防止管理员自定义赛季名含 < 或 & 触发 BadRequest
        text = (f"🏆 <b>第{season_id}赛季「{sn}」进行中</b>\n\n"
                f"⏳ 剩余约 {remain} 天｜上榜需≥{sget('SEASON_MIN_GAMES')}局\n"
                f"用 /排位 开局入座；中途想加入点下面按钮。")
        _ex_row = [[InlineKeyboardButton("💱 积分兑换排位分", callback_data="season_exchange_info")]] if sget("RANKED_EXCHANGE_ENABLED") else []
        markup = InlineKeyboardMarkup([
            [InlineKeyboardButton("📝 中途报名加入", callback_data="season_signup")],
            [InlineKeyboardButton("📊 看排位榜", callback_data="season_rank_btn")],
            *_ex_row,
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
    if not await need_auth(update, context): return
    if not await require_group_chat(update, "德州排位赛", "排位", context): return
    cid, uid = update.effective_chat.id, update.effective_user.id
    ok, key = await season_signup(context.application, cid, uid)
    await render_season_lobby(context.application, cid)
    if key == "started":
        await send_reply(update, context, f"🏆 报名满 {sget('SEASON_MIN_PLAYERS')} 人，第{season_id}赛季「{season_name or '排位赛'}」开始！每人 {sget('SEASON_START_CHIPS')} 分，周期 {sget('SEASON_DAYS')} 天。用 /排位 开局。")
    elif key == "joined_active":
        await send_reply(update, context, f"✅ 已加入进行中的赛季（需满 {sget('SEASON_MIN_GAMES')} 局才上榜）。当前分 {season_points[cid][uid]}。用 /排位 开局。")
    else:
        n = len(season_joined[cid])
        await send_reply(update, context, f"✅ 已报名本赛季排位赛（{n}/{sget('SEASON_MIN_PLAYERS')}）。满 {sget('SEASON_MIN_PLAYERS')} 人自动开赛；也可点群里的大厅看板报名。")


async def cmd_season_start(update, context):
    if not is_bot_admin(update.effective_user.id):
        await send_reply(update, context, "❌ 仅 Bot 管理员可强制开赛"); return
    if not await require_group_chat(update, "德州排位赛", "排位", context): return
    cid = update.effective_chat.id
    if season_active:
        await send_reply(update, context, "⚠️ 本赛季已在进行中。"); return
    name = " ".join(context.args) if context.args else ""
    ok, msg = await start_season(cid, name, forced=True)
    if ok:
        await send_reply(update, context, f"🏆 第{season_id}赛季「{season_name or '排位赛'}」由管理员强制开启！每人 {sget('SEASON_START_CHIPS')} 分，周期 {sget('SEASON_DAYS')} 天。用 /排位 开局。")
    else:
        await send_reply(update, context, msg)


async def cmd_season_end(update, context):
    if not is_bot_admin(update.effective_user.id):
        await send_reply(update, context, "❌ 仅 Bot 管理员可操作"); return
    if not season_active:
        await send_reply(update, context, "⚠️ 当前无进行中的赛季。"); return
    await season_settle(context.application, manual=True)
    await send_reply(update, context, "🏁 赛季已手动结算并重置。")


async def cmd_season_rank(update, context):
    if not await need_auth(update, context): return
    cid, uid = update.effective_chat.id, update.effective_user.id
    if not season_active:
        await send_reply(update, context, "⚠️ 当前无进行中的赛季排位赛。"); return
    lines = await season_standings_lines(context.application, cid, uid=uid)
    await send_reply(update, context, "\n".join(lines))


async def cmd_god(update, context):
    """查看当前赌神与历届荣誉墙。"""
    if not await need_auth(update, context): return
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
        await send_reply(update, context, text)
    except Exception:
        # 历史称号含 < & 等特殊字符导致 HTML 渲染失败时，降级为纯文本发送，避免命令“失效无响应”
        await send_reply(update, context, text, parse_mode=None)


async def cmd_god_grant(update, context):
    """管理员封赌神（全局唯一，覆盖上任）。"""
    if not is_bot_admin(update.effective_user.id):
        await send_reply(update, context, "❌ 仅 Bot 管理员可操作"); return
    if not context.args:
        await send_reply(update, context, "用法：/封赌神 <用户ID>"); return
    try:
        uid = int(context.args[0])
    except ValueError:
        await send_reply(update, context, "❌ 用户 ID 必须是数字。"); return
    for _u in list(user_titles.keys()):
        user_titles[_u].discard(TITLE_GAMBLING_GOD)
        if not user_titles[_u]:
            del user_titles[_u]
    user_titles.setdefault(uid, set()).add(TITLE_GAMBLING_GOD)
    save_data()
    await send_reply(update, context, f"👑 已将 {uid} 封为 🎰赌神（覆盖上任）。")


async def cmd_god_revoke(update, context):
    """管理员撤赌神。"""
    if not is_bot_admin(update.effective_user.id):
        await send_reply(update, context, "❌ 仅 Bot 管理员可操作"); return
    if not context.args:
        await send_reply(update, context, "用法：/撤赌神 <用户ID>"); return
    try:
        uid = int(context.args[0])
    except ValueError:
        await send_reply(update, context, "❌ 用户 ID 必须是数字。"); return
    if uid in user_titles and TITLE_GAMBLING_GOD in user_titles[uid]:
        user_titles[uid].discard(TITLE_GAMBLING_GOD)
        if title_equipped.get(uid) == TITLE_GAMBLING_GOD:
            title_equipped.pop(uid, None)
        if not user_titles[uid]:
            del user_titles[uid]
        save_data()
        await send_reply(update, context, f"🔻 已撤销 {uid} 的 🎰赌神 称号。")
    else:
        await send_reply(update, context, "ℹ️ 该用户当前没有 🎰赌神 称号。")


async def cmd_shop(update, context):
    """积分商店：列出可兑换的称号。"""
    if not await need_auth(update, context): return
    if not is_group_chat(update):
        await send_reply(update, context, "🏪 积分商店请在群聊中使用（发 /商店）。"); return
    lines = ["🏪 <b>积分商店 · 称号兑换</b>", "━" * 16]
    for t, cfg in SHOP_TITLES.items():
        cur = "积分"
        dur = "永久" if cfg["duration"] is None else f"{cfg['duration'] // 86400}天"
        lines.append(f"• {title_icon(t)}<b>{html.escape(t)}</b>：{cfg['price']} {cur}｜{dur}")
    lines.append("")
    lines.append("💡 用 /兑换 称号名 购买；/我的称号 查看，/佩戴 切换亮出的称号。")
    await send_reply(update, context, "\n".join(lines))


async def cmd_redeem(update, context):
    """兑换称号：扣统一积分 + 挂称号（永久或限时）。"""
    if not await need_auth(update, context): return
    if not is_group_chat(update):
        await send_reply(update, context, "🏪 积分商店请在群聊中使用（发 /商店）。"); return
    if not context.args:
        await send_reply(update, context, "用法：/兑换 称号名（用 /商店 查看可兑换称号）"); return
    # 容错：用户经常顺手多打「购买/一个/来一个」之类，按空格 join 后找不到。
    # 优先取第一个参数（称号意图词），join 作为兜底（SHOP_TITLES 实际全无空格）。
    title = context.args[0].strip()
    cfg = SHOP_TITLES.get(title) or SHOP_TITLES.get("".join(context.args).strip())
    if not cfg:
        await send_reply(update, context, "❌ 该称号不存在，用 /商店 查看可兑换称号。"); return
    uid = update.effective_user.id
    cid = update.effective_chat.id
    # 已持有且未过期则拒绝重复兑换
    held = user_titles.get(uid, set())
    if title in held:
        exp = title_expiry.get(uid, {}).get(title)
        if exp is None or exp > int(now_bj().timestamp()):
            await send_reply(update, context, "ℹ️ 你已持有该称号，无需重复兑换。"); return
    if player_is_busy(cid, uid):
        await send_reply(update, context, "⚠️ 你正在游戏中，请先结束当前游戏再兑换。"); return
    wallet = game_chips
    cur = "积分"
    async with wallet_locks[uid]:
        if wallet[cid][uid] < cfg["price"]:
            await send_reply(update, context, f"❌ 你的{cur}不足：需要 {cfg['price']}，当前 {wallet[cid][uid]}。"); return
        wallet[cid][uid] -= cfg["price"]
        user_titles.setdefault(uid, set()).add(title)
        if cfg["duration"] is not None:
            title_expiry.setdefault(uid, {})[title] = int(now_bj().timestamp()) + cfg["duration"]
        else:
            title_expiry.setdefault(uid, {}).pop(title, None)
        save_data()
    dur = "永久" if cfg["duration"] is None else f"{cfg['duration'] // 86400}天"
    await send_reply(update, context, f"🎉 兑换成功！获得称号 {title_icon(title)}<b>{html.escape(title)}</b>（{dur}），花费 {cfg['price']} {cur}，剩余 {wallet[cid][uid]}。", parse_mode="HTML")


async def cmd_my_titles(update, context):
    """查看我持有的所有称号。"""
    if not await need_auth(update, context): return
    uid = update.effective_user.id
    ts = user_titles.get(uid, set())
    if not ts:
        await send_reply(update, context, "你还没有任何称号，用 /商店 查看可兑换称号。")
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
    await send_reply(update, context, "\n".join(lines))


async def cmd_equip(update, context):
    """佩戴某个已持有的称号（切换昵称前缀，可覆盖默认）。"""
    if not await need_auth(update, context): return
    if not context.args:
        await send_reply(update, context, "用法：/佩戴 称号名（用 /我的称号 查看你持有的称号）")
        return
    title = "".join(context.args)
    uid = update.effective_user.id
    ts = user_titles.get(uid, set())
    if title not in ts:
        await send_reply(update, context, "❌ 你尚未持有该称号，用 /我的称号 查看。")
        return
    title_equipped[uid] = title
    save_data()
    await send_reply(update, context, f"✅ 已佩戴 <b>{html.escape(title)}</b>，将显示在昵称前。", parse_mode="HTML")


async def cmd_season_points(update, context):
    """管理员加减排位分（正为加，负为减）。"""
    if not is_bot_admin(update.effective_user.id):
        await send_reply(update, context, "❌ 仅 Bot 管理员可操作"); return
    if not await need_auth(update, context): return
    try:
        uid, amount = await _parse_target_amount(update, context)
        if amount == 0: raise ValueError
    except (ValueError, IndexError):
        await send_reply(update, context, "用法：/赛季分 用户ID 数量（正加负减），或回复玩家消息后使用 /赛季分 数量"); return
    cid = update.effective_chat.id
    if not season_active and uid not in season_points.get(cid, {}):
        await send_reply(update, context, "⚠️ 该玩家不在当前赛季，且赛季未激活。"); return
    if amount < 0 and season_points.get(cid, {}).get(uid, 0) < -amount:
        await send_reply(update, context, "❌ 该玩家排位分不足。"); return
    season_points.setdefault(cid, defaultdict(int))[uid] += amount
    season_joined.setdefault(cid, set()).add(uid)
    save_data()
    verb = "增加" if amount > 0 else "扣除"
    await send_reply(update, context, f"✅ 已为 {await get_name(context.application, uid)} {verb} {abs(amount)} 排位分，当前 {season_points[cid][uid]}。")


def _exchange_rate_text():
    """兑换比例文案：1:1 时显示「1 积分 = 1 排位分」。"""
    return f"{sget('RANKED_EXCHANGE_COST')} 积分 = {sget('RANKED_EXCHANGE_GAIN')} 排位分"


async def _season_exchange_execute(context, cid, uid, cost):
    """聊天积分 → 排位分（**唯一扣款入口**：群内命令与私聊蓝字确认共用，避免两套逻辑漂移）。
    返回 (ok, 提示文本)。比例/开关/每日上限全部读后台设置，改比例无需动代码。"""
    if not sget("RANKED_EXCHANGE_ENABLED"):
        return False, "❌ 积分兑换排位分功能未开启（管理员可在后台「排位赛」分组开启）。"
    if cost < sget("RANKED_EXCHANGE_COST"):
        return False, f"❌ 最少兑换 {sget('RANKED_EXCHANGE_COST')} 积分（当前比例 {_exchange_rate_text()}）。"
    gain = cost * sget("RANKED_EXCHANGE_GAIN") // sget("RANKED_EXCHANGE_COST")
    if gain <= 0:
        return False, f"❌ 兑换数量太小，至少能得到 1 排位分（比例 {_exchange_rate_text()}）。"
    if player_is_busy(cid, uid):
        return False, "⚠️ 你正在游戏中，请先结束再兑换排位分。"
    # 每日上限：按「消耗的聊天积分」累计，跨天自动重置（键为业务日）
    today = business_date()
    if sget("RANKED_EXCHANGE_DAILY_LIMIT") > 0:
        used = season_exchange_daily[today][cid].get(uid, 0)
        if used + cost > sget("RANKED_EXCHANGE_DAILY_LIMIT"):
            return False, (f"❌ 超出每日兑换上限：今日已兑换 {used} 积分，上限 "
                           f"{sget('RANKED_EXCHANGE_DAILY_LIMIT')}（管理员可在后台调整）。")
    async with user_wallet_locks([uid]):
        if game_chips[cid][uid] < cost:
            return False, f"❌ 聊天积分不足：需要 {cost}，当前 {game_chips[cid][uid]}。"
        game_chips[cid][uid] -= cost
        # 排位分账本：赛季未开赛也允许先兑换，开赛后报名即可带入（与 /赛季分 同一容器）
        season_points.setdefault(cid, defaultdict(int))[uid] += gain
        # 兑换分记为「额外底分」：每日重置保留、不计入盈亏榜（避免花钱买分虚增排名）
        season_exchange_bonus.setdefault(cid, defaultdict(int))[uid] += gain
        season_joined.setdefault(cid, set()).add(uid)
        if uid not in season_games.get(cid, {}):
            season_games[cid][uid] = 0
            season_rebuy[cid][uid] = 0
        if sget("RANKED_EXCHANGE_DAILY_LIMIT") > 0:
            season_exchange_daily[today][cid][uid] += cost
        ledger_add(cid, uid, 0, cost, "兑换排位分")  # 资金流台账：聊天积分回收
        save_data()
        await asyncio.to_thread(force_save_now)
    return True, (f"✅ 兑换成功：-{cost} 聊天积分 → +{gain} 排位分\n"
                  f"💰 聊天积分余额 {game_chips[cid][uid]}｜🏆 当前排位分 {season_points[cid][uid]}\n"
                  f"（比例 {_exchange_rate_text()}；兑换分算「额外底分」，每日 0 点重置后保留、不计入盈亏榜。用 /排位 开局入座）")


def _season_exchange_panel(cid, uid):
    """兑换排位分面板：正文蓝色文本超链接（与商城/兑换同款），点蓝字跳私聊确认。
    档位按后台比例生成 1×/10×/100×（去重、超上限截断）；命令 /游戏积分兑换 数量 仍可自定义直接兑换。
    返回 (text, rows)。"""
    unit_c = max(1, sget("RANKED_EXCHANGE_COST"))
    unit_g = max(1, sget("RANKED_EXCHANGE_GAIN"))
    bal = game_chips[cid][uid]
    lines = ["🏆 <b>积分兑换排位分</b>", ""]
    lines.append(f"💰 聊天积分：{bal}")
    lines.append(f"🏆 当前排位分：{season_points[cid][uid]}")
    lines.append(f"📊 兑换比例：{_exchange_rate_text()}")
    if sget("RANKED_EXCHANGE_DAILY_LIMIT") > 0:
        _used = season_exchange_daily[business_date()][cid].get(uid, 0)
        lines.append(f"📅 今日已兑换：{_used}／{sget('RANKED_EXCHANGE_DAILY_LIMIT')} 积分")
    else:
        lines.append("📅 每日不限")
    lines.append("")
    tiers = []
    for _m in (1, 10, 100):
        _c = unit_c * _m
        if _c > 100000000:
            break
        if _c not in tiers:
            tiers.append(_c)
    rows = []
    for _c in tiers:
        _g = _c * unit_g // unit_c
        url = _deep_buy_url("sexch", cid, _c)
        lines.append(f"🟡 <b>{_c} 聊天积分 → {_g} 排位分</b>")
        if url:
            lines.append(f"└ <a href='{html.escape(url, quote=True)}'>立即兑换</a>")
        else:
            # 启动早期/无 bot 用户名 → 拿不到深链，退回群内按钮直兑
            rows.append([InlineKeyboardButton(f"💱 {_c} 积分 → {_g} 排位分",
                                              callback_data=f"sexch_ask_{_c}")])
        lines.append("")
    lines.append("💡 也可发「/游戏积分兑换 数量」自定义数量直接兑换")
    return "\n".join(lines), rows


async def cmd_season_exchange(update, context):
    """聊天积分兑换排位分（比例、开关、每日上限均可在后台「排位赛」分组调整）。
    无参数 → 发蓝字面板（点链接跳私聊确认）；带数量 → 直接兑换（命令兜底，保留）。"""
    if not await need_auth(update, context): return
    if not await require_group_chat(update, "积分兑换排位分", "游戏积分兑换", context): return
    if not sget("RANKED_EXCHANGE_ENABLED"):
        await send_reply(update, context, "❌ 积分兑换排位分功能未开启（管理员可在后台「排位赛」分组开启）。"); return
    cid, uid = update.effective_chat.id, update.effective_user.id
    args = context.args or []
    if not args or not args[0].isdigit() or int(args[0]) <= 0:
        text, rows = _season_exchange_panel(cid, uid)
        msg = await safe_send(context.bot, cid, text,
                              reply_markup=(InlineKeyboardMarkup(rows) if rows else None))
        if msg and MALL_LIST_DELETE_SECONDS > 0:
            schedule_delete(context.application, cid, msg, MALL_LIST_DELETE_SECONDS)
        return
    ok, txt = await _season_exchange_execute(context, cid, uid, int(args[0]))
    await send_reply(update, context, txt)


async def cmd_season_help(update, context):
    if not await need_auth(update, context): return
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
        "<b>积分兑换排位分</b>\n"
        "• /游戏积分兑换 — 打开兑换面板，点蓝字「立即兑换」跳私聊确认（推荐）\n"
        f"• /游戏积分兑换 数量 — 自定义数量直接兑换（当前比例 {_exchange_rate_text()}）\n"
        f"• 开关：{'已开启' if sget('RANKED_EXCHANGE_ENABLED') else '已关闭'}"
        + (f"｜每人每日上限 {sget('RANKED_EXCHANGE_DAILY_LIMIT')} 积分" if sget("RANKED_EXCHANGE_DAILY_LIMIT") else "｜每日不限")
        + "（管理员可在后台「排位赛」分组调整）\n"
        "• 兑换来的分算「额外底分」：每日 0 点重置后保留，但不计入盈亏榜（不影响名次）\n\n"
        "<b>管理员专属</b>\n"
        "• /排位开赛 [赛季名] — 强制开赛（可自定义名，如 /排位开赛 赌神大战秋季赛）\n"
        "• /排位结束 — 提前结算并推最终榜\n\n"
        "<b>自动机制</b>\n"
        "• 每日 23:50 自动推一次排位榜\n"
        "• 开赛后第 7 天（到点后的首个午夜）自动结算，可能晚最多约 24 小时\n\n"
        "📌 满 20 人开赛；起始 20000 分；输光可应急补分 3×2000；满 5 局才上榜；次日 0 点重置为 20000 分（含已兑换的底分）可继续打。\n"
        "⚙️ 排位赛的入座门槛/加注额/思考时间/等待倒计时/盲注/前注可在后台「排位赛」分组单独设置，留 0 表示沿用日常德州。\n"
        "💡 以上「排位」命令均可换「赛季」前缀，含义完全相同，如 /赛季榜 /赛季报名 /赛季开赛 /赛季结束。\n"
        "⚠️ 群里若中文命令无反应，多为 BotFather 隐私模式拦截，发 /setprivacy → Disable 即可。"
    )
    await send_reply(update, context, text)


async def cmd_season_play(update, context):
    if not await need_auth(update, context): return
    if not await _game_gate(update, context, "texas", ranked=True): return
    if not await require_group_chat(update, "德州排位赛", "排位", context): return
    cid, uid = update.effective_chat.id, update.effective_user.id
    if not season_active:
        ok, key = await season_signup(context.application, cid, uid)
        if key == "started":
            await render_season_lobby(context.application, cid)  # 满 20 自动开赛：翻转看板为进行中，继续往下开房
        else:
            # UX2：/排位 静默报名不弹看板（看板仅在 /排位报名 或按钮点击时出现，减少刷屏）
            n = len(season_joined[cid])
            await send_reply(update, context, f"✅ 已报名本赛季排位赛（{n}/{sget('SEASON_MIN_PLAYERS')}）。满 {sget('SEASON_MIN_PLAYERS')} 人自动开赛；发 /排位报名 可看报名大厅。")
            return
    # 赛季进行中：开 / 入房间（赛中未报名者自动补报名）
    if uid not in season_joined.get(cid, set()):
        season_joined.setdefault(cid, set()).add(uid)
        if uid not in season_points.get(cid, {}):
            season_points[cid][uid] = _season_base(cid, uid)   # 含赛前兑换的底分
            season_games[cid][uid] = 0
            season_rebuy[cid][uid] = 0
        save_data()
    if season_points[cid][uid] <= 0:
        await send_reply(update, context, "❌ 你的排位分已用完，等待应急补分或下局。"); return
    if sget("SEASON_MIN_ENTRY_CHIPS") and season_points[cid][uid] < sget("SEASON_MIN_ENTRY_CHIPS"):
        await send_reply(update, context,
                         f"❌ 进入排位赛至少需要 {sget('SEASON_MIN_ENTRY_CHIPS')} 排位分，你当前 {season_points[cid][uid]}。\n"
                         f"可用 /游戏积分兑换 数量 把聊天积分换成排位分。"); return
    game = active_poker_games.get(cid)
    if game:
        if game.season:
            if game.phase != "waiting": await send_reply(update, context, "当前已有进行中的排位赛。"); return
            if game.add(uid):
                await update_poker_waiting(game, context.application); await send_reply(update, context, "已加入当前等待房间。")
            else: await send_reply(update, context, "你已在等待房间中。")
            return
        else:
            await send_reply(update, context, "当前有日常德州房间，请先 /结束 后再开排位赛。"); return
    game = PokerGame(cid, uid, current_game_mode(), season=True)
    if not game.add(uid):  # 排位分门槛/报名状态校验失败时不要留下空房间
        await send_reply(update, context, "❌ 无法入座排位赛（排位分不足或未报名）。"); return
    active_poker_games[cid] = game
    msg = await safe_send(context.bot, cid, await poker_waiting_text(game, context.application), reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("📥 加入游戏", callback_data="texas_join")], [InlineKeyboardButton("❌ 终止房间", callback_data="texas_end")]]))
    if msg:
        game.game_msg_id = msg.message_id
        await start_wait_timeout(game, context.application)

async def cmd_sm(update, context):
    if not await need_auth(update, context): return
    if not await _game_gate(update, context, "race"): return
    if not await require_group_chat(update, "赛车", "sc", context): return
    cid = update.effective_chat.id
    if cid in active_horse_races:
        race = active_horse_races[cid]
        # 已有赛车：直接回应当前进行中的这一局，绝不新开一局
        if getattr(race, "phase", "") == "betting":
            # 防刷屏：短时间内重复发 /赛车 只回一句文字；超过冷却才重发看板（让后进群的人能看到按钮）
            now_ts = time.time()
            if now_ts - float(getattr(race, "panel_cd", 0) or 0) < 15:
                await send_reply(update, context, "当前已有赛车进行中，直接点上方看板下注即可。")
                return
            race.panel_cd = now_ts
            msg = await safe_send(context.bot, cid, await race.view(context.application), reply_markup=race.buttons())
            if msg: race.game_msg_id = msg.message_id
        else:
            await send_reply(update, context, "当前已有赛车进行中。")
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
    # 解散提示牌桌也延迟清理，避免一堆「已解散」卡片堆在群里
    schedule_delete_ids(app, game.chat_id, game.game_msg_id, sget("PANEL_DELETE_SECONDS"))
    save_data()


async def cmd_points_flow(update, context):
    """积分流水：查每笔积分来源/去向（红包/转赠/兑换/抽水/邀请奖励/游戏送分）。回复某人消息+流水可查对方（仅管理员）。"""
    if not await need_auth(update, context): return
    uid = update.effective_user.id
    target = uid
    if update.effective_message and update.effective_message.reply_to_message:
        if not is_bot_admin(uid):
            await send_reply(update, context, "❌ 查别人的流水仅限管理员（回复对方消息发「流水」）。"); return
        target = update.effective_message.reply_to_message.from_user.id
    entries = []
    for e in ledger:
        amt = int(e.get("amt", 0) or 0)
        if e.get("frm") == target and amt:
            entries.append((e.get("ts", ""), -amt, str(e.get("typ", "")), e.get("to")))
        elif e.get("to") == target and amt:
            entries.append((e.get("ts", ""), amt, str(e.get("typ", "")), e.get("frm")))
    for e in game_flows:
        amt = int(e.get("amt", 0) or 0)
        if e.get("frm") == target and amt:
            entries.append((e.get("ts", ""), -amt, f"{e.get('typ', '')}(送分)", e.get("to")))
        elif e.get("to") == target and amt:
            entries.append((e.get("ts", ""), amt, f"{e.get('typ', '')}(收到)", e.get("frm")))
    entries.sort(key=lambda x: x[0])
    if not entries:
        await send_reply(update, context, "📒 暂无积分流水。红包/转赠/兑换/抽水/邀请奖励/游戏送分等都会记在这里；21点/赛车盈亏用「盈亏」查。"); return
    recent = entries[-15:]
    lines = [f"📒 积分流水｜{await get_name(context.application, target, cid=update.effective_chat.id)}", "━━━━━━━━━━━━━━━━━"]
    for ts, amt, typ, peer in recent:
        peer_txt = f" → 用户{peer}" if (peer and amt < 0) else (f" ← 用户{peer}" if peer else "")
        lines.append(f"{ts}｜{'+' if amt >= 0 else ''}{amt}｜{typ}{peer_txt}")
    lines.append(f"共 {len(entries)} 笔，显示最近 {len(recent)} 笔（21点/赛车每局盈亏用「盈亏」查）")
    await send_reply(update, context, "\n".join(lines))


def _invite_progress_text(uid, cid, my_name, cname):
    """合格邀请结算卡片正文（cmd_my_invite / /link / 刷新按钮共用）。
    计入=名下全部邀请；合格=达质量要求；发放=已发奖次数(≤上限)；拒绝=进群硬门槛不满足。"""
    recs = [r for r in invite_records.values()
            if r.get("inviter") == uid and (cid is None or r.get("cid") == cid)]
    counted = len(recs)
    qualified = sum(1 for r in recs if _rec_ok(r))
    rejected = sum(1 for r in recs if _rec_rejected(r))
    awarded = sum(1 for r in recs if _rec_awarded(r))
    req = []
    if sget("INVITE_QUALIFY_ENABLED"):
        if sget("INVITE_QUALIFY_MSGS") > 0:
            req.append(f"本群发言 ≥ {sget('INVITE_QUALIFY_MSGS')} 条")
        if sget("INVITE_QUALIFY_POINTS") > 0:
            req.append(f"本群净赚积分 ≥ {sget('INVITE_QUALIFY_POINTS')}")
        if sget("INVITE_QUALIFY_AVATAR"):
            req.append("进群须有头像")
        if sget("INVITE_QUALIFY_USERNAME"):
            req.append("进群须有用户名")
        req_txt = "、".join(req) if req else "无（进群即合格）"
    else:
        req_txt = "已关闭（进群即发奖）"
    L = [
        f"🎟️ <b>合格邀请结算</b> · {html.escape(cname)}",
        f"👤 邀请人：{html.escape(my_name)} <code>{uid}</code>",
        "━━━━━━━━━━━━━━",
        f"📥 已计入　<b>{counted}</b> 人",
        f"✅ 合格　　<b>{qualified}</b> 人",
        f"💰 已发放　<b>{awarded}</b> 次",
        f"🎁 奖励：每合格 1 人 +{int(sget('INVITE_REWARD'))} 积分（每人最多发 {sget('INVITE_REWARD_TIMES')} 次）",
        f"🎯 质量要求：{html.escape(req_txt)}",
        "━━━━━━━━━━━━━━",
    ]
    if rejected:
        L.append(f"🚫 拒绝 {rejected} 人（进群未满足头像/用户名，不发放）")
    return "\n".join(L)

def _invite_card_body_kb(uid, cid, cname, my_name, link, refresh_cb):
    """邀请卡片正文+按钮（群卡片/私聊推送共用）。

    安全：分享按钮走 t.me/share/url?url=<链接>，链接里的 + 在 query 中会被解码成空格
    （t.me/+hash 变 t.me/ 空格hash → 好友收到无效链接），必须整体 URL 编码（+ → %2B）。
    """
    body = _invite_progress_text(uid, cid, my_name, cname)
    rows = []
    if link:
        # 2026-09-10 用户报障「专属链接无效」：/link 发的是 deep-link，好友点开后**必须点「开始」**
        # 才会触发归因并拿到加群按钮。旧文案写「点开直接进群」，新人不点开始 → 以为链接无效。
        body += (f"\n🔗 <b>你的专属链接</b>\n<code>{link}</code>\n\n"
                 f"📌 好友点开后，<b>先点页面底部的「开始 / START」</b>，机器人会回他一个"
                 f"「加入群组」按钮，再点一下才能进群（不点开始 = 链接没反应）。\n"
                 f"📌 好友进群先记账为「待达标」，本群达标后自动发奖；也可点下方「刷新进度」立即重判。")
        rows.append([InlineKeyboardButton("打开链接", url=link),
                     InlineKeyboardButton("分享给好友", url="https://t.me/share/url?url=" + quote(link, safe=""))])
    else:
        body += "\n\n📌 发「" + str(INVITE_LINK_CMD) + "」领取本群专属链接。"
    if refresh_cb:
        rows.append([InlineKeyboardButton("🔄 刷新进度", callback_data=refresh_cb)])
    return body, (InlineKeyboardMarkup(rows) if rows else None)


async def _invite_push_card_to_private(context, uid, cid, cname):
    """邀请面板推送到用户私聊（群里发「邀请」时不再刷屏群消息）。

    返回 True=已送达私聊；False=私聊发不出去（用户没 /start 过 bot），调用方应回退群内发送。
    """
    link = (invite_links.get(cid, {}).get(uid) or {}).get("link", "")
    my_name = await get_name(context.application, uid, cid=cid)
    body, kb = _invite_card_body_kb(uid, cid, cname, my_name, link,
                                    f"invite_refresh_priv_{cid}_{uid}")
    try:
        await context.bot.send_message(uid, body, parse_mode="HTML", reply_markup=kb)
        return True
    except Exception:
        logger.info("邀请面板推送私聊失败 uid=%s（用户可能未 /start）", uid)
        return False


async def _invite_send_progress_card(update, context, uid, cid, cname, link=None, edit_msg=None):
    """发/刷新合格结算卡片。edit_msg 存在则编辑原消息（刷新按钮）。"""
    my_name = await get_name(context.application, uid, cid=cid if cid else None)
    refresh_cb = f"invite_refresh_{uid}" if cid is not None else None
    body, kb = _invite_card_body_kb(uid, cid, cname, my_name, link, refresh_cb)
    if edit_msg is not None:
        try:
            await edit_msg.edit_text(body, parse_mode="HTML", reply_markup=kb)
        except Exception:
            pass
    else:
        await send_reply(update, context, body, kb=kb, parse_mode="HTML")


async def _deep_invite_start(update, context, payload):
    """deep-link 邀请确认（t.me/<bot>?start=inv_<邀请人>_<群id>）：
    新人私聊点 START 即锁定归因（参数由 bot 自己生成，不依赖任何群事件链接字段——
    Telegram 公开群官方不保证把 invite_link 传给 bot，实测直链/申请制都丢）。
    锁定后发「加入群组」按钮（一次性申请制链接，bot 收到申请自动秒批）。"""
    try:
        uid = update.effective_user.id
        body = payload[len("inv_"):]
        inviter_s, _, cid_s = body.rpartition("_")
        inviter, cid = int(inviter_s), int(cid_s)
    except (ValueError, AttributeError):
        await send_reply(update, context, "⚠️ 邀请链接无效，请让邀请人重新发送「邀请」获取。")
        return
    if not sget("INVITE_ENABLED") or cid not in AUTHORIZED_GROUPS:
        await send_reply(update, context, "⚠️ 该邀请链接对应的群暂未开放邀请。")
        return
    if uid == inviter:
        await send_reply(update, context, "🙂 不能邀请自己哦。")
        return
    if f"{cid}:{uid}" in invite_records:
        await send_reply(update, context, "ℹ️ 你已在邀请记录中（重复进群不重复计）。")
        return
    invite_confirmed[f"{cid}:{uid}"] = inviter   # 归因锁定（落盘持久化）
    save_data()
    _inv_dbg(cid, f"[deep-link] uid={uid} 确认邀请人 {inviter}（START 参数）")
    inviter_name = await get_name(context.application, inviter, cid=cid)
    cname = chat_name_cache.get(cid) or str(cid)
    join_link, last_err = None, None
    for kw in ({"name": f"inv{uid}", "creates_join_request": True, "member_limit": 1},
               {"creates_join_request": True, "member_limit": 1},
               {"creates_join_request": True}):
        try:
            link_obj = await context.bot.create_chat_invite_link(chat_id=cid, **kw)
            join_link = link_obj.invite_link
            break
        except Exception as e:
            last_err = e
    if not join_link:
        invite_confirmed.pop(f"{cid}:{uid}", None)   # 链接都发不出，归因不落
        save_data()
        _inv_dbg(cid, f"[deep-link] 创建进群链接失败 inviter={inviter}：{last_err!r}")
        await send_reply(update, context,
                         f"❌ 生成进群链接失败：{last_err!r}\n请让管理员确认机器人是群管理员并勾选「邀请用户」权限。")
        return
    kb = InlineKeyboardMarkup([[InlineKeyboardButton("🚪 加入群组（点击自动通过）", url=join_link)]])
    await send_reply(update, context,
                     f"🎟️ 你由 <b>{inviter_name}</b> 邀请加入「{cname}」\n\n"
                     f"👇 点下方按钮进群，机器人会自动为你通过。\n"
                     f"进群后邀请即计入 <b>{inviter_name}</b> 名下。",
                     kb=kb, parse_mode="HTML")


async def cmd_my_invite(update, context):
    """我的邀请合格结算进度：已计入/合格/已发放 + 刷新。群聊=本群；私聊=全部群合计。"""
    if not await need_auth(update, context): return
    if not sget("INVITE_ENABLED"):
        await send_reply(update, context, "❌ 邀请系统未开启。"); return
    if is_group_chat(update):
        cid = update.effective_chat.id
        cname = chat_name_cache.get(cid) or (getattr(update.effective_chat, "title", "") or str(cid))
    else:
        cid, cname = None, "全部群"
    uid = update.effective_user.id
    mine = None
    if cid is not None:
        mine = (invite_links.get(cid, {}).get(uid) or {}).get("link")
        # 群里只回执一句话，完整面板推私聊（不占群消息；私聊可反复刷新）
        if await _invite_push_card_to_private(context, uid, cid, cname):
            await send_reply(update, context, "🎟️ 邀请面板已发到你的私聊，进度可随时在私聊刷新。")
            return
        await send_reply(update, context, "⚠️ 私聊推送失败（可能你还没私聊过我发 /start），先在这里看：")
    await _invite_send_progress_card(update, context, uid, cid, cname, link=mine)


async def cmd_invite_debug(update, context):
    """邀请系统体检（管理员）：bot 自查权限/事件源/数据，一条命令定位「为什么进人不加分」。"""
    if not await need_auth(update, context): return
    if not is_bot_admin(update.effective_user.id):
        await send_reply(update, context, "❌ 邀请调试仅管理员可用。"); return
    cid = update.effective_chat.id
    L = ["🔧 邀请系统体检（本群）", "━━━━━━━━━━━━━━━━━"]
    L.append(f"开关：{'开' if sget('INVITE_ENABLED') else '关'}｜归因=deep-link确认制（点专属链接→START→自动通过）；无确认申请：{'自动批(带链接+开关开)' if sget('INVITE_AUTO_APPROVE') else '管理员手动批(网页成员页)'}")
    L.append(f"本群已授权：{'是' if cid in AUTHORIZED_GROUPS else '否'}")

    # ① bot 在群里的权限 —— 邀请系统能工作的硬前提
    st = "unknown"
    try:
        me = await context.bot.get_me()
        mem = await context.bot.get_chat_member(cid, me.id)
        st = mem.status
        if st == "administrator":
            r = mem  # ChatMemberAdministrator
            L.append(f"bot 身份：✅ 管理员（can_invite_users={bool(getattr(r, 'can_invite_users', True))}，can_restrict_members={bool(getattr(r, 'can_restrict_members', False))}）")
        elif st == "member":
            L.append("bot 身份：❌ 普通成员 —— 收不到申请/进出事件，邀请系统不可能工作")
            L.append("👉 在群设置把 bot 设为管理员（需勾选「邀请用户」权限）")
        elif st == "restricted":
            L.append("bot 身份：⚠️ 受限成员（被限制），多半收不到事件")
            L.append("👉 在群设置把 bot 设为管理员")
        else:
            L.append(f"bot 身份：❌ {st}（不在群里或被踢）—— 先拉回群并设管理员")
    except Exception as exc:
        L.append(f"查询 bot 权限失败：{type(exc).__name__}（网络？）")

    # ② 归因数据现状
    links = invite_links.get(cid, {})
    L.append(f"本群专属链接：{len(links)} 条" if links else "本群专属链接：无（还没人发过「邀请」）")
    recs = {k: v for k, v in invite_records.items() if k.startswith(f"{cid}:") and not v.get("left")}
    L.append(f"本群有效邀请记录：{len(recs)} 条")
    pend = {k: v for k, v in invite_pending.items() if k.startswith(f"{cid}:")}
    L.append(f"待归因申请（等进群事件）：{len(pend)} 条")
    dbg = invite_debug.get(cid) or []
    if dbg:
        L.append("最近事件：")
        L += [f"　{d}" for d in dbg[-12:]]
    else:
        L.append("最近事件：无 —— 若 bot 是管理员且刚有人点链接进群仍无事件，把 /邀请调试 结果发管理员排查")

    # ③ 给结论
    L.append("━━━━━━━━━━━━━━━━━")
    if st == "administrator":
        L.append("✅ bot 是管理员，事件源就绪。请做一次真实测试：")
        L.append("发「邀请」→ 复制链接 → 换一个号点链接 → 应直接进群并入群加分。")
        L.append("若弹的是「申请加入」：群开着申请制，直链被转申请会丢链接、无法精确归因，去群设置关掉「需批准/申请加入」。")
        L.append("进群后仍无事件：说明进的人不是通过 bot 专属链接（直接拉人/群链接不算邀请）。")
    else:
        L.append("❌ 结论：先到群设置把 bot 设为管理员再测，否则改代码没用。")
    await send_reply(update, context, "\n".join(L))


async def cmd_invite_report(update, context):
    """手动报备入群（管理员兜底）：当 chat_join_request / chat_member / service message 三路事件都丢时用。
    用法：/报备入群 新人名字/uid → 拿 invite_pending 里本群最近一条申请链接，强制走 _invite_track_join 归因+发奖。
    不传名字：列出本群待归因申请清单（每条 [归因] 按钮）。"""
    if not await need_auth(update, context): return
    if not is_bot_admin(update.effective_user.id):
        await send_reply(update, context, "❌ 仅管理员可用。"); return
    cid = update.effective_chat.id
    pend = [(k, v) for k, v in invite_pending.items() if k.startswith(f"{cid}:")]

    if not context.args:
        if not pend:
            await send_reply(update, context, "📭 本群没有待归因申请。\n（如果刚刚有人进群且调试无事件，先让 ta 再点一次链接走申请，再发「/报备入群 名字」）")
            return
        rows = []
        L = ["<b>📋 本群待归因申请（点按钮强制归因）</b>"]
        for i, (k, link) in enumerate(pend[:20], 1):
            uid_str = k.split(":", 1)[1]
            L.append(f"{i}. <code>{uid_str}</code>　链接 …{str(link)[-12:]}")
            rows.append([InlineKeyboardButton(f"✅ 归因 #{i}", callback_data=f"invreport_{i}")])
        L.append("\n用法：/报备入群 名字/uid 直接归给最近一条")
        await send_reply(update, context, "\n".join(L), kb=InlineKeyboardMarkup(rows))
        return

    target = context.args[0].strip()
    if not pend:
        await send_reply(update, context, f"📭 本群无待归因申请，无法给「{html.escape(target)}」归因。\n让 ta 再点一次链接走申请流程，再发本命令。")
        return
    k, link = pend[-1]
    uid_ = int(k.split(":", 1)[1])
    _inv_dbg(cid, f"[手动报备] {target} → 用 invite_pending 的 {k}（链接 …{link[-12:]}）归因")
    cmu = type("CMU", (), {})()
    setattr(cmu, "invite_link", type("L", (), {"link": link})())
    name = target.lstrip("@")
    await _invite_track_join(cmu, cid, uid_, name, context)
    key = f"{cid}:{uid_}"
    rec = invite_records.get(key, {})
    if rec.get("inviter"):
        await send_reply(update, context, f"✅ 手动归因成功：<b>{html.escape(target)}</b> 算作 <code>{rec['inviter']}</code> 邀请，奖励 {rec.get('award', 0)} 分")
    else:
        await send_reply(update, context, f"⚠️ 归因未建记录，看调试：{invite_debug.get(cid, [])[-3:]}")


async def cmd_end(update, context):
    if not await need_auth(update, context): return
    cid, uid = update.effective_chat.id, update.effective_user.id
    arg = context.args[0].lower() if context.args else ""
    
    poker = active_poker_games.get(cid)
    race = active_horse_races.get(cid)
    bj = active_blackjack_games.get(cid)
    jinhua = active_jinhua_games.get(cid)
    dice = active_dice_games.get(cid)

    if not any([poker, race, bj, jinhua, dice]):
        await send_reply(update, context, "当前没有进行中的游戏。"); return

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

    if dice and (target_all or arg in ["dice", "大话骰", "大話骰", "吹牛"]):
        if is_bot_admin(uid) or uid in dice.players:
            await refund_dice(dice, context.application, "🛑 大话骰已终止，底注已退回。")
            notices.append("大话骰已退款")

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
        await send_reply(update, context, "❌ 权限不足或未找到匹配的游戏指令。用法示例：/end dz")
    else:
        save_data()
        await send_reply(update, context, "；".join(notices))
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
    _dg = active_dice_games.get(cid)
    if _dg and _dg.phase != "waiting" and uid in _dg.players:
        return True
    return False


def poker_room_of(cid, uid, exclude_game=None):
    """玩家所在的游戏房间（德州/炸金花/大话骰，含等待房）。exclude_game 用于排除当前房间。
    返回 (游戏名, 游戏对象)，不在任何房间则返回 (None, None)。"""
    for name, g in (("德州", active_poker_games.get(cid)),
                    ("炸金花", active_jinhua_games.get(cid)),
                    ("大话骰", active_dice_games.get(cid))):
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
        await send_reply(update, context, "❌ 仅 Bot 管理员可操作"); return
    if not sget("ADMIN_ADJUST_ENABLED"):
        await send_reply(update, context, "❌ 管理员加减分功能已关闭（网页「积分系统 → 积分设置」可开启）。"); return
    if not await need_auth(update, context): return
    try:
        uid, amount = await _parse_target_amount(update, context)
        if amount == 0: raise ValueError
    except (ValueError, IndexError):
        await send_reply(update, context, "用法：/add 用户ID 数量（正为加，负为减），或回复玩家消息后使用 /add 数量"); return
    cid = update.effective_chat.id
    if player_is_busy(cid, uid):
        await send_reply(update, context, "该玩家正在游戏中，无法修改积分。"); return
    async with wallet_locks[uid]:
        if amount < 0 and game_chips[cid][uid] < -amount:
            await send_reply(update, context, "❌ 玩家积分不足。"); return
        old_earned = _earn_get(cid, uid)
        game_chips[cid][uid] += amount
        if amount > 0:
            _earn_add(cid, uid, amount)   # 管理员加分算「获得」；扣分不回退累计（只增不减）
        save_data()
    verb = "添加" if amount > 0 else "扣除"
    msg = _fmt_tpl("add_msg_tpl", target=await get_name(context.application, uid),
                   verb=verb, amount=abs(amount), balance=game_chips[cid][uid])
    await send_reply(update, context, msg)
    await _check_level_change(context.application, cid, uid, old_earned, _earn_get(cid, uid))



async def cmd_cx(update, context):
    if not await need_auth(update, context): return
    cid = update.effective_chat.id
    date = business_date()
    texas = poker_profit_by_date[date].get(cid, {})
    combined = {}
    for g in (blackjack_profit_by_date, race_profit_by_date, jinhua_profit_by_date):
        for uid, v in total_profit_by_game(g, cid).items():
            combined[uid] = combined.get(uid, 0) + v
    if not texas and not combined:
        reply = await send_reply(update, context, "当前业务日暂无盈亏记录。")
        if sget("REPLY_DELETE_SECONDS") > 0 and is_group_chat(update):
            schedule_delete(context.application, cid, reply, sget("REPLY_DELETE_SECONDS"))
        return
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
    msgs = await safe_send_long(context.bot, cid, "\n".join(lines))
    if sget("REPLY_DELETE_SECONDS") > 0 and is_group_chat(update):
        schedule_delete(context.application, cid, msgs, sget("REPLY_DELETE_SECONDS"))

async def cmd_ph(update, context):
    if not await need_auth(update, context): return
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
    msgs = await safe_send_long(context.bot, cid, "\n".join(lines))
    if sget("REPLY_DELETE_SECONDS") > 0 and is_group_chat(update):
        schedule_delete(context.application, cid, msgs, sget("REPLY_DELETE_SECONDS"))

async def cmd_sq(update, context):
    if not is_bot_admin(update.effective_user.id):
        await send_reply(update, context, "❌ 仅 Bot 管理员可操作"); return
    if not is_group_chat(update):
        await send_reply(update, context, "⚠️ 授权需在群聊中进行：请在目标群里发送 /授权，机器人会把该群加入授权名单。私聊里授权无意义，且会导致游戏开在私聊、别人看不到。")
        return
    cid = update.effective_chat.id
    AUTHORIZED_GROUPS.add(cid); save_data()
    if update.effective_chat.title:
        chat_name_cache[cid] = update.effective_chat.title   # 当场缓存群名，后台不再显示裸 ID
    await send_reply(update, context, f"✅ 当前群已授权：{cid}")

async def cmd_qxshouquan(update, context):
    if not is_bot_admin(update.effective_user.id): return
    try: cid = int(context.args[0])
    except (IndexError, ValueError): await send_reply(update, context, "用法：取消授权 群ID（或 /qxsh 群ID）"); return
    AUTHORIZED_GROUPS.discard(cid); save_data(); await send_reply(update, context, f"✅ 已取消授权 {cid}")

async def cmd_auth_list(update, context):
    """管理员查看所有已授权群组（列出群 ID，尽量附带群名）。"""
    if not is_bot_admin(update.effective_user.id):
        await send_reply(update, context, "❌ 仅 Bot 管理员可操作"); return
    if not AUTHORIZED_GROUPS:
        await send_reply(update, context, "📋 当前没有任何已授权群组。"); return
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
    await send_reply(update, context, "\n".join(lines))

async def cmd_ban(update, context):
    """管理员拉黑玩家（禁止使用机器人）。支持 /拉黑 用户ID 或 回复玩家消息 /拉黑"""
    if not is_bot_admin(update.effective_user.id):
        await send_reply(update, context, "❌ 仅 Bot 管理员可操作"); return
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
        await send_reply(update, context, "用法：/拉黑 用户ID，或回复玩家消息后使用 /拉黑"); return
    if is_bot_admin(target):
        await send_reply(update, context, "⚠️ 不能拉黑管理员。"); return
    if target in BLACKLISTED_USERS:
        await send_reply(update, context, "ℹ️ 该用户已在黑名单中。"); return
    # 用 ID 拉黑且尚无缓存名字时，主动 get_chat 取名缓存（失败则回退"玩家{ID}"）
    if target not in user_names:
        try:
            chat = await context.bot.get_chat(target)
            nm = getattr(chat, "first_name", None) or getattr(chat, "title", None) or (f"@{chat.username}" if getattr(chat, "username", None) else None)
            if nm: user_names[target] = nm
        except Exception:
            pass
    BLACKLISTED_USERS.add(target); save_data()
    await send_reply(update, context, f"🚫 已拉黑 {await get_name(context.application, target)}（{target}），该用户已被禁止使用机器人。")

async def cmd_unban(update, context):
    """管理员解封玩家。"""
    if not is_bot_admin(update.effective_user.id):
        await send_reply(update, context, "❌ 仅 Bot 管理员可操作"); return
    target = None
    if update.message.reply_to_message:
        target = update.message.reply_to_message.from_user.id
    else:
        try: target = int(context.args[0])
        except (IndexError, ValueError): pass
    if not target:
        await send_reply(update, context, "用法：/解黑 用户ID，或回复玩家消息后使用 /解黑"); return
    if target not in BLACKLISTED_USERS:
        await send_reply(update, context, "ℹ️ 该用户不在黑名单中。"); return
    BLACKLISTED_USERS.discard(target); save_data()
    await send_reply(update, context, f"✅ 已解封 {await get_name(context.application, target)}（{target}）。")

async def cmd_banlist(update, context):
    """管理员查看黑名单。"""
    if not is_bot_admin(update.effective_user.id):
        await send_reply(update, context, "❌ 仅 Bot 管理员可操作"); return
    if not BLACKLISTED_USERS:
        await send_reply(update, context, "📋 当前黑名单为空。"); return
    lines = [f"📋 <b>黑名单（共 {len(BLACKLISTED_USERS)} 人）</b>", "━"*14]
    for uid in sorted(BLACKLISTED_USERS):
        lines.append(f"• {await get_name(context.application, uid)}（{uid}）")
    await send_reply(update, context, "\n".join(lines))

async def cmd_list_all(update, context):
    """管理员一键查看：管理员 / 授权群 / 黑名单 三合一总览。"""
    if not is_bot_admin(update.effective_user.id):
        await send_reply(update, context, "❌ 仅 Bot 管理员可操作"); return
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

    await send_reply(update, context, "\n".join(lines))

async def cmd_addadmin(update, context):
    if not is_bot_admin(update.effective_user.id):
        await send_reply(update, context, "❌ 仅 Bot 管理员可操作"); return
    try: uid = int(context.args[0])
    except (IndexError, ValueError):
        await send_reply(update, context, "用法：/addadmin 用户ID，例如 /addadmin 123456789"); return
    if uid in BOT_ADMINS:
        await send_reply(update, context, f"ℹ️ {uid} 已经是管理员了"); return
    BOT_ADMINS.add(uid); save_data()
    await send_reply(update, context, f"✅ 已添加机器人管理员：{uid}")

async def cmd_deladmin(update, context):
    if not is_bot_admin(update.effective_user.id):
        await send_reply(update, context, "❌ 仅 Bot 管理员可操作"); return
    try: uid = int(context.args[0])
    except (IndexError, ValueError):
        await send_reply(update, context, "用法：/deladmin 用户ID，例如 /deladmin 123456789"); return
    if uid in ADMIN_USER_IDS:
        await send_reply(update, context, f"⚠️ {uid} 是种子管理员，重启后自动恢复，无法移除（如需移除请改代码 ADMIN_USER_IDS）"); return
    if uid not in BOT_ADMINS:
        await send_reply(update, context, f"ℹ️ {uid} 不是管理员"); return
    BOT_ADMINS.discard(uid); save_data()
    await send_reply(update, context, f"✅ 已移除机器人管理员：{uid}")

async def cmd_admin_list(update, context):
    if not is_bot_admin(update.effective_user.id):
        await send_reply(update, context, "❌ 仅 Bot 管理员可操作"); return
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
    await send_reply(update, context, "\n".join(lines))

async def cmd_autosm(update, context):
    if not await need_auth(update, context): return
    if not is_bot_admin(update.effective_user.id): await send_reply(update, context, "❌ 仅 Bot 管理员可操作"); return
    cid = update.effective_chat.id
    cur = hourly_race_enabled.get(cid, True)   # 授权群默认开启，此处按群覆盖
    hourly_race_enabled[cid] = not cur; save_data()
    await send_reply(update, context, f"本群整点自动赛车：{'✅ 已开启' if not cur else '❌ 已关闭（总开关和时段仍需在后台配置）'}")

async def on_button(update, context):
    _bind_update_cid(update)
    try:
        q = update.callback_query
        if not q or not q.message:
            if q: await q.answer("该操作已过期", show_alert=True)
            return
        cid, uid, data = q.message.chat.id, q.from_user.id, q.data or ""
        _remember_name(update)
        # 私聊兑换确认回调（redeem/mall ok|no_<cid>_<idx>）：在 bot 私聊里点「确认/取消」触发，
        # 聊天是私聊（cid=用户id），不能用群授权拦截；真实目标群 id 内嵌在 data 里。
        if data.startswith(("redeem_ok_", "redeem_no_", "mall_ok_", "mall_no_", "sexch_ok_", "sexch_no_")):
            if uid in BLACKLISTED_USERS and not is_bot_admin(uid):
                await q.answer("🚫 你已被禁止使用本机器人", show_alert=True); return
            await _deep_start_confirm(q, data, context)
            return
        # --- 兑换排位分：无深链兜底（_BOT_USERNAME 为空时面板给的是 callback 按钮） ---
        if data.startswith("sexch_ask_"):
            try: _sc = int(data[len("sexch_ask_"):])
            except ValueError:
                await q.answer("按钮已过期", show_alert=True); return
            _sok, _stxt = await _season_exchange_execute(context, cid, uid, _sc)
            if _sok:
                await send_reply(update, context, _stxt)
            await q.answer(_stxt.split("\n")[0][:190], show_alert=not _sok)
            return
        # --- 邀请：私聊刷新（面板推送到私聊后，私聊 chat.id 不是群 id，必须在群授权前处理） ---
        if data.startswith("invite_refresh_priv_"):
            if uid in BLACKLISTED_USERS and not is_bot_admin(uid):
                await q.answer("🚫 你已被禁止使用本机器人", show_alert=True); return
            try:
                rcid_s, _, owner_s = data[len("invite_refresh_priv_"):].rpartition("_")
                rcid, owner = int(rcid_s), int(owner_s)
            except ValueError:
                await q.answer("按钮已过期", show_alert=True); return
            if uid != owner:
                await q.answer("只能刷新自己的进度", show_alert=True); return
            new_awd = 0
            try:
                new_awd = await _invite_refresh_all(context.application, rcid, owner)
            except Exception:
                logger.exception("邀请私聊刷新异常（已吞并）")
            cname = chat_name_cache.get(rcid) or str(rcid)
            link = (invite_links.get(rcid, {}).get(owner) or {}).get("link", "")
            try:
                my_name = await get_name(context.application, owner, cid=rcid)
                body, kb = _invite_card_body_kb(owner, rcid, cname, my_name, link,
                                                f"invite_refresh_priv_{rcid}_{owner}")
                await q.message.edit_text(body, parse_mode="HTML", reply_markup=kb)
            except Exception:
                logger.exception("刷新私聊邀请卡片失败（已吞并）")
            try:
                await q.answer("已刷新" + (f"：新发放 {new_awd} 次奖励 🎉" if new_awd else "：暂无新达标"))
            except Exception:
                pass
            return
        # --- 邀请：主动问兜底按钮 inva_<cid>_<inviter>_<uid>（私聊回调，is_auth 之前处理） ---
        if data.startswith("inva_"):
            if uid in BLACKLISTED_USERS and not is_bot_admin(uid):
                await q.answer("🚫 你已被禁止使用本机器人", show_alert=True); return
            body = data[len("inva_"):]
            try:
                choice_s = ""
                if body.startswith("none_"):                 # inva_none_<cid>_<uid>：我自己进的
                    choice_s = "none"; body = body[len("none_"):]
                left, _, owner_s = body.rpartition("_")      # 末段 = 申请人 uid
                cid_s, _, inviter_s = left.partition("_")    # 首段 = 群 id（负数），中段 = 邀请人
                cid_, owner = int(cid_s), int(owner_s)
                inviter = 0 if choice_s == "none" else int(inviter_s)
            except ValueError:
                await q.answer("按钮已过期", show_alert=True); return
            rcid, uid_owner = cid_, owner
            if uid != uid_owner:
                await q.answer("只能由申请人本人确认", show_alert=True); return
            if choice_s == "none":
                await q.answer("好的，等管理员批准进群。", show_alert=False)
                return
            if inviter == uid or rcid not in AUTHORIZED_GROUPS or not sget("INVITE_ENABLED"):
                await q.answer("该邀请不可用", show_alert=True); return
            invite_confirmed[f"{rcid}:{uid}"] = inviter   # 归因锁定
            save_data()
            _inv_dbg(rcid, f"[主动问] uid={uid} 确认邀请人 {inviter} → 自动批准")
            try:
                await context.bot.approve_chat_join_request(chat_id=rcid, user_id=uid)
                await q.answer("✅ 已确认，正在为你通过进群…", show_alert=False)
            except Exception as e:
                _inv_dbg(rcid, f"[主动问] 自动批准失败 uid={uid}：{e!r}（转人工，归因已锁定）")
                await q.answer("✅ 邀请已记录，等管理员批准进群。", show_alert=False)
            return
        # --- 入群验证：按钮选答案 / 一键通过（群授权前处理，未验证者也得能点） ---
        if data.startswith("jv_"):
            parts = data[len("jv_"):].split("_")     # [群id, 用户id] 或 [群id, 用户id, 选项值]
            try:
                cid_v, uid_v = int(parts[0]), int(parts[1])
                pick = parts[2] if len(parts) > 2 else ""
            except (ValueError, IndexError):
                await q.answer("按钮已过期", show_alert=True); return
            if uid != uid_v and not is_bot_admin(uid):
                await q.answer("❌ 这不是你的验证按钮", show_alert=True); return
            rec_v = join_verify_pending.get(f"{cid_v}:{uid_v}")
            if not rec_v:
                # 修复（2026-09-09）：pending 丢失（重部署后存档未同步/记录被清）时，
                # 人可能仍处于验证禁言状态。只说「已通过验证」却不解禁 = 用户永远发不了言。
                # 这里幂等兜底解除限制（本来能发言时重复设置也无害）。
                try:
                    await context.bot.restrict_chat_member(
                        cid_v, uid_v, permissions=ChatPermissions(
                            can_send_messages=True, can_send_other_messages=True,
                            can_add_web_page_previews=True, can_send_polls=True, can_invite_users=True))
                except Exception:
                    logger.exception("入群验证：pending 缺失时解除限制失败 cid=%s uid=%s", cid_v, uid_v)
                await q.answer("✅ 你已通过验证，可以发言了", show_alert=False); return
            name_v = str(rec_v.get("name") or q.from_user.first_name or f"用户{uid_v}")
            ans_v = rec_v.get("ans")
            if ans_v is not None and not str(pick).strip():
                await q.answer("请点下方选项按钮作答", show_alert=True); return   # 按钮模式不接受无选项回调
            if pick:
                if str(pick).strip() != str(ans_v):
                    wrong_v, over_v = await _jv_wrong_hit(context, cid_v, uid_v, name_v, rec_v)
                    await q.answer("❌ 答案不对，再选一次" + (f"（已错 {wrong_v} 次）" if not over_v else ""),
                                   show_alert=not over_v)
                    return
            await _join_verify_pass(context, cid_v, uid_v, name_v,
                                    int(rec_v.get("msg_id", 0) or 0) or getattr(q.message, "message_id", 0))
            await q.answer("✅ 验证通过，可以发言了", show_alert=False)
            return
        if not is_auth(cid): await q.answer("未授权", show_alert=True); return
        if uid in BLACKLISTED_USERS and not is_bot_admin(uid): await q.answer("🚫 你已被禁止使用本机器人", show_alert=True); return
        if data == "noop": await q.answer(); return  # 占位按钮（售罄/页码），点了不报错

        # --- 邀请合格结算：刷新进度（事件驱动兜底重判） ---
        if data.startswith("invite_refresh"):
            owner = int(data.split("_")[-1]) if data.split("_")[-1].isdigit() else uid
            if uid != owner:
                await q.answer("只能刷新自己的进度", show_alert=True); return
            new_awd = 0
            try:
                new_awd = await _invite_refresh_all(context.application, cid, owner)
            except Exception:
                logger.exception("邀请进度刷新异常（已吞并）")
            cname = chat_name_cache.get(cid) or (getattr(q.message.chat, "title", "") or str(cid))
            link = (invite_links.get(cid, {}).get(owner) or {}).get("link", "")
            try:
                await _invite_send_progress_card(None, context, owner, cid, cname,
                                                 link=link, edit_msg=q.message)
            except Exception:
                logger.exception("刷新邀请卡片失败（已吞并）")
            try:
                await q.answer("已刷新" + (f"：新发放 {new_awd} 次奖励 🎉" if new_awd else "：暂无新达标"))
            except Exception:
                pass
            return
        
        # --- 强制订阅：点「我已加入」立即复检（不等 60 秒负缓存，也不用重发消息） ---
        if data == "fsub_recheck":
            _fsub_ok_cache.get(cid, {}).pop(uid, None)
            try:
                _ok, _checked = await _fsub_probe(context, uid)
            except Exception:
                logger.exception("强制订阅复检异常（已吞并）")
                _ok, _checked = False, 0
            if _ok:
                _fsub_ok_cache[cid][uid] = (time.time(), True)
                try:
                    await q.message.delete()
                except Exception:
                    pass
                await q.answer("✅ 已确认订阅，现在可以正常发言啦")
            elif _checked == 0:
                await q.answer("⚠️ 机器人读不到该频道成员（需把机器人加入频道并设为管理员），已暂时放行", show_alert=True)
            else:
                await q.answer("❌ 还没检测到订阅，请先点上面的按钮加入频道", show_alert=True)
            return

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
                card = game.hit(uid)
                if card is None:  # 超时/并发竞态下已不是该玩家回合（stale 按钮），不能让 get_card_str 崩溃
                    await q.answer("不是你的回合", show_alert=True); return
                await q.answer(f"你抽到了 {game.get_card_str([card])}")
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
            if data == "season_exchange_info":
                # 大厅按钮：只回提示，不直接扣分（避免误触扣款，兑换走 /游戏积分兑换 数量）
                if not sget("RANKED_EXCHANGE_ENABLED"):
                    await q.answer("积分兑换排位分功能未开启", show_alert=True); return
                await q.answer(f"发「/游戏积分兑换 数量」即可兑换\n当前比例 {_exchange_rate_text()}"
                               + (f"\n每人每日上限 {sget('RANKED_EXCHANGE_DAILY_LIMIT')} 积分" if sget("RANKED_EXCHANGE_DAILY_LIMIT") else ""),
                               show_alert=True)
                return
            if data == "season_lobby_close":
                mid = season_lobby_msg.pop(cid, None)
                if mid: await safe_delete(context.bot, cid, mid)
                await q.answer("已关闭看板"); return
            if data == "season_rank_btn":
                if not season_active:
                    await q.answer("当前无进行中的赛季", show_alert=True); return
                lines = await season_standings_lines(context.application, cid, uid=uid)
                await send_reply(update, context, "\n".join(lines))
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
                                season_points[cid][uid] = _season_base(cid, uid)   # 含赛前兑换的底分
                                season_games[cid][uid] = 0
                                season_rebuy[cid][uid] = 0
                            save_data()
                        if season_points[cid][uid] <= 0:
                            await q.answer("排位分不足，无法加入", show_alert=True); return
                        if sget("SEASON_MIN_ENTRY_CHIPS") and season_points[cid][uid] < sget("SEASON_MIN_ENTRY_CHIPS"):
                            await q.answer(f"进入排位赛至少需要 {sget('SEASON_MIN_ENTRY_CHIPS')} 排位分，你当前 {season_points[cid][uid]}",
                                           show_alert=True); return
                    else:
                        wallet = game_chips
                        if wallet[cid][uid] < sget("MIN_ENTRY_CHIPS"):
                            await q.answer(f"进入德州至少需要 {sget('MIN_ENTRY_CHIPS')} 积分", show_alert=True); return
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
            if data == "texas_raise_half": action, extra = "raise", max(game.min_raise, game.pot // 2)
            elif data == "texas_raise_pot": action, extra = "raise", max(game.min_raise, game.pot)
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
        # --- 大话骰：等待房 + 牌局操作（加入/开始/终止/私看骰子/加码/开骰/刷新） ---
        if data.startswith("dice_"):
            game = active_dice_games.get(cid)
            if not game: await q.answer("大话骰游戏已结束", show_alert=True); return
            if data == "dice_refresh":
                game.cancel_timer()
                if game.phase == "waiting": await update_dice_waiting(game, context.application)
                else: await start_dice_turn_timer(game, context.application)
                await q.answer("已刷新界面")
                return
            if data == "dice_end":
                if not is_bot_admin(uid) and uid not in game.players:
                    await q.answer("权限不足", show_alert=True); return
                await refund_dice(game, context.application, "🛑 大话骰已终止，底注已退回。")
                await q.answer("本局已终止")
                return
            if game.phase == "waiting":
                if data == "dice_join":
                    _room, _ = poker_room_of(cid, uid, exclude_game=game)
                    if _room:
                        await q.answer(f"你已在 {_room} 房间，请先结束再加入", show_alert=True); return
                    if len(game.players) >= sget("DICE_MAX_PLAYERS"):
                        await q.answer("房间已满", show_alert=True); return
                    if game_chips[cid][uid] < sget("MIN_ENTRY_CHIPS"):
                        await q.answer(f"进入大话骰至少需要 {sget('MIN_ENTRY_CHIPS')} 积分", show_alert=True); return
                    if game.add(uid):
                        await q.answer("已加入"); await update_dice_waiting(game, context.application)
                    else: await q.answer("你已在等待房间中。", show_alert=True)
                elif data == "dice_start":
                    if uid != game.owner_id:
                        await q.answer("只有发起人可开始游戏（满 2 人会倒计时自动开始）", show_alert=True); return
                    if len(game.players) < 2:
                        await q.answer("至少要 2 人才能开始", show_alert=True); return
                    if game.start():
                        game.cancel_wait()
                        await _dice_notify_dropped(game, context.application)
                        await q.answer("游戏开始")
                        await start_dice_turn_timer(game, context.application)
                    else:
                        await q.answer("开局失败：至少 2 人且余额够底注", show_alert=True)
                else: await q.answer("无法执行此操作", show_alert=True)
                return
            if data == "dice_see":
                if uid not in game.hands:
                    await q.answer("还没开局，没有骰子", show_alert=True); return
                if uid in game.out:
                    await q.answer("你已出局，没有骰子了", show_alert=True); return
                ds = " ".join(map(str, game.hands[uid]))
                # 顺子/豹子要当场告诉玩家，否则他会照着自己骰子叫，开骰必翻车
                _dn, _dw = len(game.players), sget("DICE_WILD_ONE")
                if _dice_rule_on("DICE_STRAIGHT_ZERO", _dn) and _dice_is_straight(game.hands[uid], _dw):
                    ds += "（顺子·本手算0个，别照它叫牌）"
                elif _dice_rule_on("DICE_LEOPARD_BONUS", _dn):
                    _lk = _dice_leopard_kind(game.hands[uid], _dw)
                    if _lk: ds += f"（{_lk}·叫本点数算 +{2 if _lk == '纯豹' else 1}）"
                bid_txt = f"{game.bid[0]}个{game.bid[1]}" if game.bid else "待开叫（你是先叫方）"
                # 2026-09-11 用户要求：直接弹窗，不走私聊（弹窗只有点击者本人可见，不泄露骰子）
                await q.answer(f"🎲 你的骰子（仅你可见）：{ds}\n🎙 当前叫牌：{bid_txt}", show_alert=True)
                return
            if data == "dice_raise":
                if uid != game.actor or game.phase != "playing":
                    await q.answer("还没轮到你", show_alert=True); return
                mr = dice_min_raise(game)
                if not mr:
                    await q.answer("没有更大的叫法了，只能开骰", show_alert=True); return
                ok, desc = game.action(uid, "bid", mr)
                if not ok: await q.answer(desc, show_alert=True); return
                await q.answer(f"已叫 {mr[0]}个{mr[1]}")
                game.last_action = f"{await get_name(context.application, uid)} 加码叫 {mr[0]}个{mr[1]}"
                await start_dice_turn_timer(game, context.application)
                return
            if data == "dice_open":
                if uid != game.actor or game.phase != "playing":
                    await q.answer("还没轮到你", show_alert=True); return
                ok, desc = game.action(uid, "open")
                if not ok: await q.answer(desc, show_alert=True); return
                await q.answer("开骰！")
                game.last_action = f"{await get_name(context.application, uid)} 开骰"
                await _dice_resolve_and_continue(game, context.application, uid)
                return
            await q.answer("未知操作", show_alert=True)
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
                await start_jinhua_turn_timer(game, context.application)  # 内部含 open_pending 看门狗
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
                await schedule_notice_delete(context.application, cid,
                                             await safe_send(context.bot, cid, ann))
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
                    if game_chips[cid][uid] < sget("MIN_ENTRY_CHIPS"):
                        await q.answer(f"进入炸金花至少需要 {sget('MIN_ENTRY_CHIPS')} 积分", show_alert=True); return
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
                    await start_jinhua_turn_timer(game, context.application)  # open_pending 后挂超时看门狗
                else:
                    await q.answer("未知操作", show_alert=True)
                return
            # 下注阶段：当前玩家操作；跟平阶段（open_pending）允许任意存活玩家弃牌止损
            if data == "jh_fold" and game.phase == "open_pending":
                if uid in game.folded:
                    await q.answer("你已弃牌", show_alert=True); return
                ok, desc = game.action(uid, "fold")
                if not ok: await q.answer(desc, show_alert=True); return
                await q.answer(desc)
                game.last_action = f"{await get_name(context.application, uid)} 弃牌"
                if game.phase == "showdown": await settle_jinhua(game, context.application)
                else: await start_jinhua_turn_timer(game, context.application)  # 弃牌后仍在 open_pending 则挂看门狗
                return
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
            elif game.phase == "open_pending": await start_jinhua_turn_timer(game, context.application)  # 挂超时看门狗
            else: await start_jinhua_turn_timer(game, context.application)
            return
        # --- 积分商城：点蓝色按钮直接兑换 / 翻页 / 商品详情 ---
        if data.startswith("mall_buy_") or data.startswith("mall_show_") or data.startswith("mall_page_"):
            cid, uid = q.message.chat.id, q.from_user.id
            if data.startswith("mall_show_"):
                # 商品详情：弹出商品信息，1 秒后回到原列表
                try: idx = int(data[len("mall_show_"):])
                except ValueError: await q.answer(); return
                items = [x for x in sget("MALL_ITEMS") if x.get("on", True)]
                if not (1 <= idx <= len(items)): await q.answer("商品已下架", show_alert=True); return
                it = items[idx - 1]
                stk = it.get("stock")
                stk_txt = "不限量" if not isinstance(stk, int) else (f"剩 {stk}" if stk > 0 else "已售罄")
                await q.answer(f"#{idx} {it['name']}\n价格 {_mall_price(it)} 分｜{stk_txt}\n点 ✅ 立即兑换 直接购买", show_alert=True)
                return
            if data.startswith("mall_buy_"):
                try: idx = int(data[len("mall_buy_"):])
                except ValueError: await q.answer(); return
                if not sget("MALL_ENABLED"): await q.answer("商城未开启", show_alert=True); return
                items = [x for x in sget("MALL_ITEMS") if x.get("on", True)]
                if not (1 <= idx <= len(items)): await q.answer("商品已下架", show_alert=True); return
                it = items[idx - 1]
                stk = it.get("stock")
                if isinstance(stk, int) and stk <= 0: await q.answer("已售罄", show_alert=True); return
                err = await _redeem_execute(context, cid, uid, it)
                if err: await q.answer(err, show_alert=True)
                else: await q.answer("🎉 兑换成功")
                return
            if data.startswith("mall_page_"):
                try: page = int(data[len("mall_page_"):])
                except ValueError: await q.answer(); return
                # 在原按钮消息就地刷新为新页：正文小卡 + 按钮一起重建（_mall_panel 保证与首屏一致）
                items = [x for x in sget("MALL_ITEMS") if x.get("on", True)]
                if not items:
                    await q.answer("商城已空"); return
                text, rows = _mall_panel(page, items, q.message.chat.id)
                try:
                    await q.message.edit_text(text, parse_mode="HTML",
                                               reply_markup=InlineKeyboardMarkup(rows) if rows else None)
                except Exception:
                    pass
                pages = max(1, (len(items) + sget("MALL_PAGE_SIZE") - 1) // sget("MALL_PAGE_SIZE"))
                await q.answer(f"已切到 {page}/{pages} 页")
                return
        # --- 积分兑换：点蓝色商品按钮直接兑换 ---
        if data.startswith("redeem_show_"):
            try: idx = int(data[len("redeem_show_"):])
            except ValueError: await q.answer(); return
            items = [x for x in redeem_goods if x.get("on", True)]
            if not (1 <= idx <= len(items)): await q.answer("商品已下架", show_alert=True); return
            x = items[idx - 1]
            left = int(x.get("left", 0) or 0)
            await q.answer(f"#{idx} {x['name']}\n价格 {int(x.get('price', 0) or 0)} 分｜剩余 {'不限' if left <= 0 else left}\n点 ✅ 立即兑换 直接兑换", show_alert=True)
            return
        if data.startswith("redeem_buy_"):
            try: idx = int(data[len("redeem_buy_"):])
            except ValueError:
                await q.answer("无效商品", show_alert=True); return
            await _redeem_buy_cb(q, idx, context)
            return
        if data.startswith("invreport_"):
            try: idx = int(data[len("invreport_"):])
            except ValueError: await q.answer(); return
            cid, uid = q.message.chat.id, q.from_user.id
            if not is_bot_admin(uid): await q.answer("仅管理员", show_alert=True); return
            pend = [(k, v) for k, v in invite_pending.items() if k.startswith(f"{cid}:")]
            if not (1 <= idx <= len(pend)): await q.answer("已失效", show_alert=True); return
            k, link = pend[idx - 1]
            uid_ = int(k.split(":", 1)[1])
            cmu = type("CMU", (), {})()
            setattr(cmu, "invite_link", type("L", (), {"link": link})())
            await _invite_track_join(cmu, cid, uid_, "报备入群", context)
            rec = invite_records.get(f"{cid}:{uid_}", {})
            await q.answer(f"✅ 已归因 奖励 {rec.get('award', 0)} 分" if rec.get('inviter') else "⚠️ 未建记录", show_alert=True)
            return
        if data.startswith("rp_grab_"):
            p = rp_packets.get(data[8:])
            if not p:
                await q.answer("红包已结束或过期", show_alert=True); return
            await _rp_grab(p, data[8:], uid, context, q)
            return
        if data.startswith("guessbet_"):
            try: _, side, amount = data.split("_"); amount = int(amount)
            except ValueError:
                await q.answer("无效数据", show_alert=True); return
            await _guess_bet(cid, uid, context, side, amount, q)
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
            race.name_cache[uid] = await get_name(context.application, uid); await q.answer(desc); await action_notice(cid, context.application, uid, f"下注 {amount} 于 {sget('HORSE_EMOJI')[horse]}")
            await safe_edit(context.bot, cid, race.game_msg_id, await race.view(context.application), reply_markup=race.buttons())
            return

    except Exception:
        logger.exception("按钮处理异常")
        try:
            await update.callback_query.answer("操作异常，请重试", show_alert=True)
        except Exception:
            pass


def _antispam_norm(text):
    """内容归一化：去空白 + 小写，同文异构（加空格/大小写变化）视为同一内容。"""
    return re.sub(r"\s+", "", (text or "")).lower()

def _antispam_check(cid, uid, text):
    """记录并判定刷屏特征。返回 'repeat' / 'timer' / None。

    - repeat：复读机——窗口内同人同内容达到 ANTISPAM_REPEAT_N 条
    - timer：定时器——同内容累计 ANTISPAM_TIMER_N 条，且相邻间隔近似相等
      （TG 定时消息发出后与普通消息无差别，固定节奏是其唯一可抓特征）
    """
    now = time.time()
    key = (cid, uid, _antispam_norm(text))
    hist = antispam_hist.setdefault(key, [])
    hist.append(now)
    if len(hist) > 12: del hist[:-12]
    recent = [t for t in hist if now - t <= sget("ANTISPAM_WINDOW")]
    if len(recent) >= sget("ANTISPAM_REPEAT_N"):
        return "repeat"
    if len(hist) >= sget("ANTISPAM_TIMER_N"):
        ivs = [b - a for a, b in zip(hist, hist[1:])][-(sget("ANTISPAM_TIMER_N") - 1):]
        mean = sum(ivs) / len(ivs)
        if mean >= 30 and all(abs(iv - mean) <= mean * sget("ANTISPAM_TIMER_TOL") / 100 for iv in ivs):
            return "timer"
    return None

def _antispam_prune(offs, window=None):
    """累犯计数只保留时间窗内的命中（就地清理并返回）。

    不清理的话 antispam_offense 只增不减，禁言时长 = 基础 × 2^(n-1)，
    老用户隔几个月再犯一次就是几十小时，等同永久禁言，内存也只涨不降。
    """
    w = ANTISPAM_OFFENSE_WINDOW if window is None else window
    try: w = float(w)
    except (TypeError, ValueError): return offs
    if w and w > 0:
        cut = time.time() - w
        offs[:] = [t for t in offs if t >= cut]
    return offs

async def _antispam_hit(update, context, cid, uid, reason):
    """命中处理：撤删本条 → 清该用户统计防连环触发 → 禁言（累犯翻倍）→ 群内通告。"""
    message = update.effective_message
    try: await message.delete()
    except TelegramError: pass
    for k in [k for k in antispam_hist if k[0] == cid and k[1] == uid]:
        antispam_hist.pop(k, None)
    offs = antispam_offense.setdefault((cid, uid), [])
    offs.append(time.time())
    _antispam_prune(offs)   # 只保留时间窗内的命中，否则累犯计数只增不减 → 2^(n-1) 变事实永久禁言
    n = len(offs)
    mute = sget("ANTISPAM_MUTE_SECONDS") * (2 ** (n - 1)) if sget("ANTISPAM_MUTE_ESCALATE") else sget("ANTISPAM_MUTE_SECONDS")
    muted = False
    if mute > 0:
        try:
            await context.bot.restrict_chat_member(
                cid, uid, permissions=ChatPermissions(can_send_messages=False),
                until_date=datetime.now(timezone.utc) + timedelta(seconds=mute))
            muted = True
        except TelegramError: pass
    name = user_names.get(uid) or str(uid)
    why = "复读刷屏" if reason == "repeat" else "定时器式连发"
    tip = f"🔨 检测到{why}：{name} 的消息已自动撤删"
    if muted:
        mins = max(1, mute // 60)
        tip += f"，禁言 {mins} 分钟" + ("（累犯加倍）" if n > 1 and sget("ANTISPAM_MUTE_ESCALATE") else "")
    elif sget("ANTISPAM_MUTE_SECONDS") > 0:
        tip += "（我需要管理员禁言权限才能禁言）"
    try:
        m = await context.bot.send_message(cid, tip)
        if sget("ANTISPAM_NOTICE_SECONDS") > 0:
            schedule_delete(context.application, cid, m, sget("ANTISPAM_NOTICE_SECONDS"))
    except TelegramError: pass

def _autodel_text_hit(message, text):
    """自动删除规则（文本类）：返回规则名或 None。开关即法律，网页「自动删除」页可改。"""
    if _multi_has(sget("AUTODEL_TEXT_RULES"), "link") and text and ("http://" in text or "https://" in text or "t.me/" in text
            or any(getattr(e, "type", None) in ("url", "text_link") for e in (message.entities or []))):
        # 域名白名单：名单内（含子域名）的链接放行，不再一律删
        if sget("LINK_WHITELIST_ENABLED") and _link_whitelisted(text):
            pass
        else:
            return "link"
    if _multi_has(sget("AUTODEL_TEXT_RULES"), "long") and text and len(text) > max(50, int(sget("AUTODEL_LONG_LEN"))):
        return "long"
    if _multi_has(sget("AUTODEL_TEXT_RULES"), "premium_emoji") and any(
            getattr(e, "type", None) == "custom_emoji" for e in (message.entities or [])):
        return "premium_emoji"
    return None

# 进群判定：目标状态白名单。**必须含 restricted** —— 群若开启「新成员默认限制」，
# Telegram 推的入群事件 new.status 就是 restricted；只认 member 会把这类新人整条跳过
# （不发验证、不记 member_joined_at → 观察期/强制订阅「只拦新人」也一起失效）。
_JOIN_IN_CHAT = ("member", "restricted", "administrator", "creator")


def _is_join_transition(new, old):
    """是否属于「进入群聊」的状态变更（进群判定唯一入口）。

    - new 在 _JOIN_IN_CHAT 且 old 是 left/kicked → 进群。
    - **restricted → member 不算进群**：那是 bot 自己解除限制触发的状态变更，
      若算进群会再次发验证 → 解限/发验证互相触发，死循环。
    """
    ns = str(getattr(new, "status", "") or "")
    os_ = str(getattr(old, "status", "") or "")
    if ns not in _JOIN_IN_CHAT:
        return False
    return os_ in ("left", "kicked")


def _is_service_message(message):
    """判断是否为系统消息（入退群/改名/换头像/删头像/置顶/建群/迁移等）。
    系统消息的 effective_user 经常为 None（建群/迁移尤其），单独判定便于豁免 user 检查。
    用 getattr 兜底空值，兼容测试 mock（生产 PTB Message 这些字段全有）。"""
    if message is None:
        return False
    for attr in ("new_chat_members", "left_chat_member", "new_chat_title",
                 "new_chat_photo", "delete_chat_photo", "pinned_message",
                 "group_chat_created", "supergroup_chat_created",
                 "migrate_to_chat_id", "migrate_from_chat_id"):
        if getattr(message, attr, None):
            return True
    return False

def _autodel_media_hit(message):
    """自动删除规则（媒体类）：返回规则名或 None。"""
    if message is None:
        return None
    if _is_service_message(message):
        return "service" if _multi_has(sget("AUTODEL_MEDIA_TYPES"), "service") else None
    if message.sticker is not None:
        return "sticker" if _multi_has(sget("AUTODEL_MEDIA_TYPES"), "sticker") else None
    if message.animation is not None:
        return "gif" if _multi_has(sget("AUTODEL_MEDIA_TYPES"), "gif") else None
    if message.voice is not None or message.video_note is not None:
        return "voice" if _multi_has(sget("AUTODEL_MEDIA_TYPES"), "voice") else None
    if message.contact is not None:
        return "contact" if _multi_has(sget("AUTODEL_MEDIA_TYPES"), "contact") else None
    if message.document is not None:
        name = (message.document.file_name or "").lower()
        mt = message.document.mime_type or ""
        if _multi_has(sget("AUTODEL_MEDIA_TYPES"), "archive") and (mt in ("application/zip", "application/x-rar-compressed",
                                       "application/x-7z-compressed", "application/gzip", "application/x-tar")
                or name.endswith((".zip", ".rar", ".7z", ".tar", ".gz"))):
            return "archive"
        if _multi_has(sget("AUTODEL_MEDIA_TYPES"), "executable") and (mt in ("application/x-msdownload", "application/vnd.android.package-archive",
                                          "application/x-dosexec")
                or name.endswith((".exe", ".msi", ".bat", ".cmd", ".scr", ".apk", ".com"))):
            return "executable"
        return "document" if _multi_has(sget("AUTODEL_MEDIA_TYPES"), "document") else None
    if message.photo:
        return "photo" if _multi_has(sget("AUTODEL_MEDIA_TYPES"), "photo") else None
    if message.video is not None:
        return "video" if _multi_has(sget("AUTODEL_MEDIA_TYPES"), "video") else None
    return None

async def _autodel_enforce(update, context):
    """自动删除规则执行：命中即静默撤删。返回 True 表示已删（调用方应停止后续处理）。
    系统消息（建群/迁移等）effective_user 经常为 None，单独走路径不要求 user 在场；非系统消息仍按原规则：管理员/机器人豁免。"""
    user, message = update.effective_user, update.effective_message
    if not message or not is_group_chat(update):
        return False
    is_svc = _is_service_message(message)
    if not is_svc:
        if not user or user.is_bot:
            return False
        if is_bot_admin(user.id):
            return False
    hit = _autodel_text_hit(message, message.text or message.caption or "") or _autodel_media_hit(message)
    if hit:
        if hit == "link" and not is_svc and user:
            _invite_flag_ad(update.effective_chat.id, user.id, "发链接/广告")  # 风控连坐
        delay = int(sget("AUTODEL_MEDIA_SECONDS") if is_svc or hit in (
            "photo", "video", "sticker", "gif", "voice", "contact", "document", "archive", "executable", "service"
        ) else sget("AUTODEL_TEXT_SECONDS"))
        if delay > 0:
            # 延迟删除：命中后 N 秒再撤（0=立即删），给管理员留查看时间
            schedule_delete(context.application, update.effective_chat.id, message, delay)
        else:
            try:
                await message.delete()
            except TelegramError:
                pass
        return True
    return False

# ==================== 群管中心：敏感词 / 域名白名单 / 入群验证 / 观察期巡检 ====================
_URL_HOST_RE = re.compile(r"(?:https?://)?([a-z0-9][a-z0-9\-]*(?:\.[a-z0-9\-]+)+)(?:[:/]|\s|$)", re.I)

def _link_domains():
    """白名单域名（归一：去协议、去路径、去点前缀、小写）。"""
    out = []
    for d in (sget("LINK_WHITELIST") or []):
        d = str(d).strip().lower()
        if not d:
            continue
        d = re.sub(r"^https?://", "", d).split("/")[0].lstrip(".")
        if d:
            out.append(d)
    return out

def _link_whitelisted(text):
    """文本里出现的每一个域名都在白名单里才放行；解析不出域名或有域名不在名单 → 不放行。"""
    hosts = [h.lower().rstrip(".") for h in _URL_HOST_RE.findall(str(text or ""))]
    if not hosts:
        return False
    domains = _link_domains()
    if not domains:
        return False
    for h in hosts:
        if not any(h == d or h.endswith("." + d) for d in domains):
            return False
    return True

def _sensitive_hit(text):
    """敏感词判定：明文按子串（忽略大小写），/xxx/ 形式按正则。返回命中的词条或 None。"""
    t = str(text or "")
    if not t or not sget("SENSITIVE_WORDS"):
        return None
    for w in sget("SENSITIVE_WORDS"):
        w = str(w).strip()
        if not w:
            continue
        if len(w) > 2 and w.startswith("/") and w.endswith("/"):
            try:
                if re.search(w[1:-1], t, re.I):
                    return w
            except re.error:
                logger.warning("敏感词正则非法，已跳过：%s", w)
                continue
        elif w.lower() in t.lower():
            return w
    return None


async def _observe_enforce(update, context):
    """新成员观察期：入群未满观察时长的成员发言即删并禁言至期满。返回 True=已拦截。

    文本与媒体消息共用（此前只在 on_text 拦截 → 观察期内发个表情包就能照常发言）。
    """
    if not (sget("OBSERVE_ENABLED") and sget("OBSERVE_SECONDS") > 0):
        return False
    user, message = update.effective_user, update.effective_message
    if not message or not user or user.is_bot:
        return False
    if not is_group_chat(update) or is_bot_admin(user.id):
        return False
    cid = update.effective_chat.id
    _jt = member_joined_at.get(cid, {}).get(user.id, 0)
    _elapsed = time.time() - _jt if _jt else 1e9
    if _elapsed >= sget("OBSERVE_SECONDS"):
        return False
    try:
        await context.bot.delete_message(chat_id=cid, message_id=message.message_id)
        await context.bot.restrict_chat_member(
            cid, user.id, permissions=ChatPermissions(can_send_messages=False),
            until_date=datetime.now(timezone.utc) + timedelta(seconds=sget("OBSERVE_SECONDS") - _elapsed + 1))
    except TelegramError:
        pass
    return True


async def _sensitive_enforce(update, context):
    """敏感词过滤（文本与媒体 caption 共用）：命中即删，可按档禁言/踢出。返回 True=已拦截。

    此前只有 on_text 调用、且只看 message.text → 图片/贴纸/视频的 caption 里的敏感词
    永远不会被查（用户报障「敏感词设了不删」的一半根因）。
    删除失败（bot 无删除权限）不再静默：私聊管理员告警，否则管理员只看到「设了没反应」。
    """
    if not sget("SENSITIVE_ENABLED"):
        return False
    user, message = update.effective_user, update.effective_message
    if not message or not user or user.is_bot:
        return False
    if not is_group_chat(update) or is_bot_admin(user.id):
        return False
    cid = update.effective_chat.id
    text = getattr(message, "text", None) or getattr(message, "caption", None) or ""
    if not _sensitive_hit(text):
        return False
    try:
        await context.bot.delete_message(chat_id=cid, message_id=message.message_id)
    except Exception as e:
        logger.warning("敏感词消息删除失败 cid=%s mid=%s：%r", cid, message.message_id, e)
        try:
            await context.bot.send_message(
                ADMIN_USER_ID,
                f"⚠️ 敏感词消息删除失败（请确认机器人有删除消息权限）：\n"
                f"群 <code>{cid}</code> · 消息 <code>{message.message_id}</code> · 错误 <code>{html.escape(repr(e))}</code>",
                parse_mode="HTML")
        except Exception:
            pass
    if sget("SENSITIVE_ACTION"):
        await _mod_punish(context, cid, user.id, sget("SENSITIVE_ACTION"), sget("SENSITIVE_MUTE_SECONDS"),
                          user.first_name or f"用户{user.id}", "敏感词")
    _invite_flag_ad(cid, user.id, "敏感词")   # 风控连坐：被邀请人发广告 → 邀请人不再计合格
    return True

async def _mod_punish(context, cid, uid, action, mute_seconds, name, reason):
    """群管统一处罚：1=禁言 2=踢出（踢出用 ban+立即 unban，成员可自行回来）。异常全吞。"""
    try:
        if action == 1:
            await context.bot.restrict_chat_member(
                cid, uid, permissions=ChatPermissions(can_send_messages=False),
                until_date=datetime.now(timezone.utc) + timedelta(seconds=max(30, int(mute_seconds))))
        elif action == 2:
            await context.bot.ban_chat_member(cid, uid)
            await context.bot.unban_chat_member(cid, uid)
        elif action == 3:
            await context.bot.ban_chat_member(cid, uid)   # 封禁：只 ban 不解封
    except Exception:
        logger.exception("群管处罚失败 cid=%s uid=%s action=%s（已吞并）", cid, uid, action)


_FSUB_RE_URL = re.compile(r"(?:t\.me/|telegram\.me/)(?:s/)?([A-Za-z0-9_]{4,})")
_FSUB_RE_HANDLE = re.compile(r"@?([A-Za-z0-9_]{4,})")


def _fsub_parse(ch):
    """把网页「须订阅的频道」里填的内容统一解析成 get_chat_member 能用的 key。

    支持：@用户名 / 裸用户名 / t.me/用户名 / https://t.me/用户名 / -100xxx 频道 id。
    ⚠️ 私有邀请链接（t.me/+hash、t.me/joinchat/xxx）Bot API **查不了成员状态**，返回 None；
    调用方必须跳过该频道，绝不能把它当作「未订阅」——这正是 2026-09-10 用户报的
    「群友订阅成功却还是被删消息」的根因（当时填的是完整链接，int() 抛异常被吞）。
    """
    s = str(ch or "").strip()
    if not s:
        return None
    if "t.me/+" in s or "joinchat/" in s:
        return None                      # 私有邀请链接：无法查询
    if re.fullmatch(r"-?\d+", s):        # 纯数字 / -100xxx 频道 id
        try:
            return int(s)
        except Exception:
            return None
    m = _FSUB_RE_URL.search(s)           # 链接形式
    if m:
        return "@" + m.group(1)
    m = _FSUB_RE_HANDLE.fullmatch(s)     # @用户名 或裸用户名
    if m:
        return "@" + m.group(1)
    return None


async def _fsub_links(context):
    """把 FORCE_SUB_CHANNELS 转成 [(显示名, 链接)]：@用户名→公开 t.me 链接；数字 id→get_chat 邀请链接（缓存）。"""
    out = []
    for ch in sget("FORCE_SUB_CHANNELS"):
        raw = str(ch or "").strip()
        if not raw:
            continue
        if raw.startswith("@"):
            out.append((raw, f"https://t.me/{raw.lstrip('@')}"))
        elif "t.me/" in raw:
            _u = raw.split("t.me/")[-1].strip("/")
            out.append((f"@{_u}" if not _u.startswith("+") else "频道", f"https://t.me/{_u}"))
        else:
            try:
                if raw in _fsub_invite_cache:
                    out.append((f"频道 {raw}", _fsub_invite_cache[raw]))
                    continue
                chat = await context.bot.get_chat(int(raw))
                url = getattr(chat, "invite_link", None) or (f"https://t.me/{chat.username}" if getattr(chat, "username", "") else "")
                if url:
                    _fsub_invite_cache[raw] = url
                    out.append((getattr(chat, "title", None) or f"频道 {raw}", url))
            except Exception:
                continue
    return out


async def _fsub_probe(context, user_id):
    """查询 user_id 是否订阅了任一 FORCE_SUB_CHANNELS。

    返回 (ok, checked)：
      ok=True  → 至少一个频道确认已订阅；
      checked=0 → 一个频道都没查成功（配置是私有链接 / bot 不在频道 / 非管理员 / 网络异常），
                  调用方应 fail-open 放行，避免误删已订阅的群友。
    """
    checked = 0
    for ch in sget("FORCE_SUB_CHANNELS"):
        key = _fsub_parse(ch)
        if key is None:
            logger.warning("强制订阅：频道配置 %r 无法解析（私有邀请链接 Bot 查不了成员，"
                           "请改填 -100xxx 频道 id 或 @用户名）", ch)
            continue
        try:
            _m = await context.bot.get_chat_member(key, user_id)
        except Exception as e:
            logger.warning("强制订阅：查询频道 %s 成员状态失败（需把机器人加入该频道并设为管理员）：%s", key, e)
            continue
        checked += 1
        if (getattr(_m, "status", "left") in ("member", "administrator", "creator", "restricted")
                or getattr(_m, "is_member", False)):
            return True, checked
    return False, checked


async def _forcesub_enforce(update, context):
    """强制订阅频道：未订阅任一频道的成员发言即删+提示（带订阅按钮）。

    返回 True=已拦截（消息已处理，调用方直接 return）。管理员/群管/Bot 管理员豁免；
    已订阅判定缓存 30 分钟、未订阅缓存 60 秒（订阅后一分钟内自动放行），避免每条消息打 API。

    ⚠️ fail-open（2026-09-10 修）：只有 API **明确返回**未订阅才删消息；频道配置解析不出、
    查询抛异常（bot 不在频道 / 非管理员 / 网络抖动）一律放行——宁可漏拦也不误删已订阅的群友。
    """
    if not sget("FORCE_SUB_ENABLED") or not sget("FORCE_SUB_CHANNELS"):
        return False
    message, user = update.effective_message, update.effective_user
    if not message or not user or user.is_bot or not is_group_chat(update) or is_bot_admin(user.id):
        return False
    cid = update.effective_chat.id
    try:
        if (await _group_admins_get_async(cid)).get(user.id):
            return False
    except Exception:
        pass
    if sget("FORCE_SUB_ONLY_NEW"):
        _jt = member_joined_at.get(cid, {}).get(user.id, 0)
        if not _jt or time.time() - _jt > 600:
            return False
    now = time.time()
    _hit = _fsub_ok_cache.get(cid, {}).get(user.id)
    ok = None
    if _hit:
        _age = now - _hit[0]
        if _hit[1] and _age < 1800:
            return False                 # 已订阅（30 分钟缓存）→ 直接放行
        if not _hit[1] and _age < 60:
            ok = False                   # 未订阅（60 秒负缓存）→ 不重复打 API
    if ok is None:
        ok, _checked = await _fsub_probe(context, user.id)
        if not ok and _checked == 0:
            # 一个频道都没查成功 → 配置/权限问题，放行避免误删（fail-open）
            _fsub_ok_cache[cid][user.id] = (now, True)
            return False
        _fsub_ok_cache[cid][user.id] = (now, ok)
        if ok:
            return False
    # 未订阅：删消息 + 发提示（订阅其一即可；提示可自动删除）
    try:
        await context.bot.delete_message(chat_id=cid, message_id=message.message_id)
    except Exception:
        pass
    _prev = _fsub_ok_cache[cid].get(f"warned:{user.id}")
    if not (_prev and now - _prev < 60):   # 60 秒内只发一次提示，不刷屏
        try:
            links = await _fsub_links(context)
            # 频道名做成可点蓝字（HTML 文本超链接）：点一下 Telegram 直接跳频道
            _ch_html = "、".join(f"<a href='{html.escape(u, quote=True)}'>{html.escape(str(l))}</a>"
                                 for l, u in links if u)
            if not _ch_html:
                _ch_html = "、".join(html.escape(str(c)) for c in sget("FORCE_SUB_CHANNELS"))
            txt = _fmt_tpl("force_sub_warn_tpl",
                           name=html.escape(user_names.get(user.id) or user.first_name or f"用户{user.id}"),
                           channels=_ch_html,
                           seconds=sget("FORCE_SUB_WARN_SECONDS"))
            _rows = [[InlineKeyboardButton(f"📢 加入 {l}", url=u)] for l, u in links if u]
            _rows.append([InlineKeyboardButton("✅ 我已加入", callback_data="fsub_recheck")])
            sent = await context.bot.send_message(cid, txt, parse_mode="HTML",
                                                  reply_markup=InlineKeyboardMarkup(_rows))
            _fsub_ok_cache[cid][f"warned:{user.id}"] = now
            if sget("FORCE_SUB_WARN_SECONDS") > 0:
                # 走统一队列：持 task 引用 + 持久化 + 60s 兜底，裸 create_task 会被 GC 导致永不删除
                schedule_delete_ids(context.application, cid, sent.message_id,
                                    int(sget("FORCE_SUB_WARN_SECONDS")))
        except Exception:
            logger.exception("强制订阅提示发送失败 cid=%s（已吞并）", cid)
    return True


def _captcha_render(a, b):
    """画一张 a+b 算术验证码 PNG（带噪点/干扰线）；未装 Pillow 返回 None（调用方降级为文本算式）。"""
    try:
        from PIL import Image, ImageDraw, ImageFont
    except Exception:
        return None
    try:
        img = Image.new("RGB", (340, 120), (246, 247, 251))
        d = ImageDraw.Draw(img)
        for _ in range(80):   # 噪点：防机器直读像素
            x, y = random.randint(0, 339), random.randint(0, 119)
            g = random.randint(140, 210)
            d.point((x, y), fill=(g, g, min(255, g + 20)))
        for _ in range(3):    # 干扰线
            x1, y1 = random.randint(0, 339), random.randint(0, 119)
            x2, y2 = random.randint(0, 339), random.randint(0, 119)
            d.line((x1, y1, x2, y2), fill=(185, 185, 205), width=1)
        font = None
        for fp in ("arial.ttf", "DejaVuSans.ttf"):
            try:
                font = ImageFont.truetype(fp, 52); break
            except Exception:
                continue
        if font is None:
            font = ImageFont.load_default()
        d.text((26, 30), f"{a} + {b} = ?", fill=(28, 28, 58), font=font)
        bio = io.BytesIO()
        img.save(bio, "PNG")
        return bio.getvalue()
    except Exception:
        logger.exception("验证码图片生成失败（降级文本算式）")
        return None

def _jv_options(a, b, n=5):
    """按钮验证候选答案：正确答案 + (n-1) 个干扰项，随机顺序、互不重复、非负。"""
    ans = a + b
    opts = {ans}
    for _ in range(400):
        if len(opts) >= n:
            break
        v = ans + random.choice((-5, -4, -3, -2, -1, 1, 2, 3, 4, 5, 6, -6))
        if v >= 0:
            opts.add(v)
    v = 0
    while len(opts) < n:      # 极端兜底：补足数量
        if v not in opts:
            opts.add(v)
        v += 1
    opts = list(opts)
    random.shuffle(opts)
    return opts


async def _join_verify_start(context, cid, uid, name):
    """入群验证：mode=0 按钮选答案（默认）/ 1 图片算术打字回复 / 2 一键通过。

    0/2 先限制发言（防打字绕过），点按钮解锁；1 不限制（否则没法回复答案），
    答题期间发言全部被 _join_verify_handle_text 消费，答对/超时由巡检兜底。

    去重：超级群同一次进群会同时收到 chat_member 与 NEW_CHAT_MEMBERS 两个事件源，
    两个 handler 都在 group 2（不同类型互不排斥）→ 这里必须只发一条验证消息。
    """
    key = f"{cid}:{uid}"
    old = join_verify_pending.get(key)
    if old:
        if int(old.get("msg_id", 0) or 0):
            return                       # 已登记且验证消息已发出 → 第二个事件源直接跳过
        join_verify_pending.pop(key, None)   # 上一条验证消息没发出去（异常）→ 允许补发
    mode = int(sget("JOIN_VERIFY_MODE"))
    if mode != 1:
        try:
            await context.bot.restrict_chat_member(
                cid, uid, permissions=ChatPermissions(can_send_messages=False))
        except Exception:
            logger.exception("入群验证：限制发言失败 cid=%s uid=%s（继续发验证消息）", cid, uid)
    txt = (str(sget("JOIN_VERIFY_MSG")).replace("{name}", html.escape(str(name)))
           .replace("{seconds}", str(int(sget("JOIN_VERIFY_SECONDS")))))
    mid, png, a, b, opts = 0, None, 0, 0, []
    if mode == 0:
        a, b = random.randint(1, 9), random.randint(1, 9)
        opts = _jv_options(a, b)
        txt += f"\n\n🧮 验证问题：{a} + {b} = ?\n点下方正确答案按钮完成验证。"
    elif mode == 1:
        a, b = random.randint(2, 9), random.randint(2, 9)
        png = _captcha_render(a, b)
        txt += "\n\n🧮 验证问题：" + (f"看图作答（{a} + {b} = ?）" if png is None else "请直接回复图中算式的结果（只发数字）")
    try:
        if png is not None:
            try:
                msg = await context.bot.send_photo(cid, photo=png, caption=txt)
            except Exception:
                # 图片发不出去（群限制发图/权限异常）→ 降级文字题目，别让新人卡在看不见的验证里
                logger.exception("入群验证：验证码图片发送失败，降级文字题目 cid=%s uid=%s", cid, uid)
                msg = await context.bot.send_message(cid, txt + "\n（请直接回复算式结果，只发数字）")
        else:
            if mode == 0:
                kb = InlineKeyboardMarkup([[InlineKeyboardButton(str(o), callback_data=f"jv_{cid}_{uid}_{o}")
                                            for o in opts]])
            elif mode == 2:
                kb = InlineKeyboardMarkup([[InlineKeyboardButton(
                    "✅ 点击完成验证", callback_data=f"jv_{cid}_{uid}")]])
            else:
                kb = None
            msg = await context.bot.send_message(cid, txt, reply_markup=kb)
        mid = getattr(msg, "message_id", 0) or 0
    except Exception:
        logger.exception("入群验证：发送验证消息失败 cid=%s uid=%s", cid, uid)
    if not mid:
        # 验证消息没发出去 → 不登记。否则用户看不到题目却会被超时禁言/踢出（静默处罚）。
        logger.warning("入群验证：验证消息未能发出，跳过登记 cid=%s uid=%s", cid, uid)
        if mode != 1:
            # 修复（2026-09-09）：上面已经禁言了，消息却发不出去 → 必须撤销禁言，
            # 否则新人既看不到题目、又永远发不了言（用户报障「发不了言、找不到验证」）。
            try:
                await context.bot.restrict_chat_member(
                    cid, uid, permissions=ChatPermissions(
                        can_send_messages=True, can_send_other_messages=True,
                        can_add_web_page_previews=True, can_send_polls=True, can_invite_users=True))
                logger.info("入群验证：已撤销禁言 cid=%s uid=%s", cid, uid)
            except Exception:
                logger.exception("入群验证：撤销禁言失败 cid=%s uid=%s", cid, uid)
        return
    rec = {"ts": time.time(), "msg_id": mid, "name": str(name), "mode": mode}
    if mode in (0, 1):
        rec.update({"a": a, "b": b, "wrong": 0})
        if mode == 0:
            rec["ans"] = a + b
    join_verify_pending[key] = rec

async def _jv_wrong_hit(context, cid, uid, name, rec):
    """记一次验证答错；达到上限按超时档处理。返回 (累计错次, 是否已达上限)。

    修复（2026-09-09 用户报障「新人被永久禁言、找不到验证」）：
    此前达上限一律 pop 掉 pending + 按档处罚。action=0/1（提醒/禁言）时人还在群里，
    pending 一清 → 再点正确答案只会收到「✅ 你已通过验证」而**不会解除禁言**，
    巡检也扫不到 → **永久禁言**（真实配置 max_wrong=1，点错一次即触发）。
    现在：action 0/1 保留 pending（禁言不影响点按钮，仍可自救），action 2/3 才清（人已离群）。
    重复答错不重复刷群消息（用 over_notified 标记），避免刷屏。
    """
    rec["wrong"] = int(rec.get("wrong", 0) or 0) + 1
    if int(sget("JOIN_VERIFY_MAX_WRONG")) > 0 and rec["wrong"] >= int(sget("JOIN_VERIFY_MAX_WRONG")):
        if sget("JOIN_VERIFY_ACTION") >= 2:
            join_verify_pending.pop(f"{cid}:{uid}", None)   # 踢出/封禁：人已离群，清记录
        else:
            rec["over"] = True          # 保留 pending，允许继续点按钮自救
        if rec.get("over_notified"):
            return rec["wrong"], True   # 已提醒过，不重复刷屏
        rec["over_notified"] = True
        if sget("JOIN_VERIFY_ACTION") == 0:
            try:
                await context.bot.send_message(
                    cid, f"❌ {html.escape(str(name))} 答错 {rec['wrong']} 次未通过验证，"
                         f"请管理员留意（可继续点按钮作答）。")
            except Exception:
                pass
        else:
            await _mod_punish(context, cid, uid, sget("JOIN_VERIFY_ACTION"), sget("SENSITIVE_MUTE_SECONDS"), name, "验证答错超限")
            try:
                await context.bot.send_message(
                    cid, f"❌ {html.escape(str(name))} 验证答错超限，已"
                         f"{'禁言' if sget('JOIN_VERIFY_ACTION') == 1 else '移出群' if sget('JOIN_VERIFY_ACTION') == 2 else '封禁'}。"
                         + ("（仍可点下方正确答案通过验证）" if sget("JOIN_VERIFY_ACTION") == 1 else ""))
            except Exception:
                pass
        return rec["wrong"], True
    return rec["wrong"], False

async def _join_verify_handle_text(context, cid, uid, text):
    """入群验证（图片算术 mode=1）：待验证成员的发言优先当答案处理。返回 True=消息已消费，不再进命令/游戏逻辑。"""
    rec = join_verify_pending.get(f"{cid}:{uid}")
    if not rec or int(rec.get("mode", 0) or 0) != 1:
        return False
    name = str(rec.get("name") or f"用户{uid}")
    ans = str(text or "").strip()
    if ans.isdigit() and int(ans) == int(rec.get("a", 0)) + int(rec.get("b", 0)):
        await _join_verify_pass(context, cid, uid, name, int(rec.get("msg_id", 0) or 0))
        return True
    wrong, over = await _jv_wrong_hit(context, cid, uid, name, rec)
    if not over:
        try:
            await context.bot.send_message(cid, f"❌ 答案不对，请再试一次（已错 {wrong} 次）。")
        except Exception:
            pass
    return True

_gate_kicked_ts = {}   # "cid:uid" -> 上次硬门槛踢人的时间戳（双事件源去重，运行时态）


async def _join_gate_check(context, cid, member, name):
    """进群硬门槛：用户名 / Premium / 简介，任一不满足 → 直接移出（不进验证流程）。全关或放行返回 True。"""
    if not (sget("JOIN_GATE_USERNAME") or sget("JOIN_GATE_PREMIUM") or sget("JOIN_GATE_BIO")):
        return True
    reasons = []
    if sget("JOIN_GATE_USERNAME") and not getattr(member, "username", None):
        reasons.append("无用户名")
    if sget("JOIN_GATE_PREMIUM") and not getattr(member, "is_premium", False):
        reasons.append("非Premium")
    if sget("JOIN_GATE_BIO"):
        bio_ok = None   # None=查询失败（不拦，宁放过不误杀） True=有简介 False=无简介
        try:
            ch = await context.bot.get_chat(member.id)
            bio_ok = bool(str(getattr(ch, "bio", "") or "").strip())
        except Exception:
            logger.exception("进群门槛：查简介失败 uid=%s（宁放过不误杀）", member.id)
        if bio_ok is False:
            reasons.append("无简介")
    if not reasons:
        return True
    # 双事件源去重：同一次进群 chat_member + 服务消息各调一次，不去重会重复 ban + 提示发 2 条（2026-09-10 复扫发现）
    _gk = f"{cid}:{member.id}"
    _now = time.time()
    if float(_gate_kicked_ts.get(_gk, 0) or 0) and _now - float(_gate_kicked_ts[_gk]) < 60:
        return False
    _gate_kicked_ts[_gk] = _now
    try:
        await context.bot.ban_chat_member(cid, member.id)
        await context.bot.unban_chat_member(cid, member.id)   # 踢出（可自行再进，先过门槛再说）
    except Exception:
        logger.exception("进群门槛踢出失败 cid=%s uid=%s", cid, member.id)
    try:
        await context.bot.send_message(
            cid, f"🚪 {html.escape(str(name))} 未满足进群要求（{'、'.join(reasons)}），已移出。")
    except Exception:
        pass
    return False

async def _join_verify_pass(context, cid, uid, name, msg_id=0):
    """验证通过：解除限制 → 删掉验证消息 → 发通过提示。"""
    key = f"{cid}:{uid}"
    join_verify_pending.pop(key, None)
    try:
        await context.bot.restrict_chat_member(
            cid, uid,
            permissions=ChatPermissions(can_send_messages=True, can_send_other_messages=True,
                                        can_add_web_page_previews=True, can_send_polls=True,
                                        can_invite_users=True))
    except Exception:
        logger.exception("入群验证：解除限制失败 cid=%s uid=%s", cid, uid)
    if msg_id:
        try:
            await context.bot.delete_message(cid, msg_id)
        except Exception:
            pass
    try:
        await context.bot.send_message(cid, str(sget("JOIN_VERIFY_OK_MSG")).replace("{name}", html.escape(str(name))))
    except Exception:
        pass

async def join_verify_sweep(context):
    """入群验证超时巡检（每 60 秒）：超时未通过 → 按配置提醒/禁言/踢出/封禁，并清掉验证消息。

    不因 JOIN_VERIFY_ENABLED=0 早退：突袭人墙期间强制登记的待验证（以及关开关瞬间的存量）
    也要正常结算，否则人被永久禁言。新登记入口才受开关控制。
    """
    # 不按全局开关早退：人墙可能只在个别群生效（群级覆盖），到期都必须解除
    for _cid in list(raid_until):
        try:
            _CUR_CID.set(_safe_cid(_cid))
            await _raid_recover(context, _cid)
        except Exception:
            logger.exception("防突袭恢复检查异常（已吞并）")
    now = time.time()
    for key in list(join_verify_pending):
        rec = join_verify_pending.get(key) or {}
        try:
            cid_s, _, uid_s = str(key).partition(":")
            cid, uid = int(cid_s), int(uid_s)
        except ValueError:
            join_verify_pending.pop(key, None); continue
        _CUR_CID.set(_safe_cid(cid))   # 这条待验证记录属于该群 → 阈值/动作按该群配置解析
        if now - float(rec.get("ts", now)) < int(sget("JOIN_VERIFY_SECONDS")):
            continue
        join_verify_pending.pop(key, None)
        name = rec.get("name") or f"用户{uid}"
        if sget("JOIN_VERIFY_ACTION") == 0:
            # 修复（2026-09-09）：action=0「只提醒」时，_join_verify_start 给的禁言没人解
            # → 新人被永久禁言（用户报障「发不了言」）。只提醒档必须解除禁言。
            try:
                await context.bot.restrict_chat_member(
                    cid, uid, permissions=ChatPermissions(
                        can_send_messages=True, can_send_other_messages=True,
                        can_add_web_page_previews=True, can_send_polls=True, can_invite_users=True))
            except Exception:
                logger.exception("入群验证：超时(action=0)解除限制失败 cid=%s uid=%s", cid, uid)
            try:
                await context.bot.send_message(
                    cid, f"⏰ {html.escape(str(name))} 入群后未在 {int(sget('JOIN_VERIFY_SECONDS'))} 秒内完成验证，"
                         f"已自动放行，请管理员留意。")
            except Exception:
                pass
        else:
            await _mod_punish(context, cid, uid, sget("JOIN_VERIFY_ACTION"), sget("SENSITIVE_MUTE_SECONDS"), name, "入群验证超时")
            try:
                await context.bot.send_message(
                    cid, f"⏰ {html.escape(str(name))} 入群验证超时，已{'禁言' if sget('JOIN_VERIFY_ACTION') == 1 else '移出群'}。")
            except Exception:
                pass
        if rec.get("msg_id"):
            try:
                await context.bot.delete_message(cid, int(rec["msg_id"]))
            except Exception:
                pass

def _raid_active(cid):
    """突袭人墙是否生效中（人墙期间新人一律强制走验证禁言流程）。"""
    return bool(sget("RAID_ENABLED")) and float(raid_until.get(cid, 0) or 0) > time.time()

async def _raid_recover(context, cid):
    """人墙到期自动解除（有人进群/巡检触发时惰性检查）。"""
    until = float(raid_until.get(cid, 0) or 0)
    if until and time.time() >= until:
        raid_until.pop(cid, None)
        try:
            await context.bot.send_message(cid, "✅ 突袭警戒解除，入群恢复正常。")
        except Exception:
            pass

async def _raid_on_join(context, cid, uid=0):
    """防突袭：滑窗计数进群人数；超阈值 → 临时人墙（期间新人强制验证禁言），到期自动解除。

    去重：同一次进群会同时到 chat_member 与服务消息两个事件源，若按事件计数，阈值实际被腰斩。
    uid 相同且在窗口内的重复上报只计一次。
    """
    if not sget("RAID_ENABLED"):
        return
    try:
        await _raid_recover(context, cid)
    except Exception:
        logger.exception("防突袭恢复检查异常（已吞并）")
    now = time.time()
    if uid:
        ckey = f"{cid}:{uid}"
        last = float(raid_counted.get(ckey, 0) or 0)
        if last and now - last < max(30, int(sget("RAID_WINDOW"))):
            return          # 同一个人同一次进群的第二个事件源，不重复计数
        raid_counted[ckey] = now
        if len(raid_counted) > 2000:
            for k in [k for k, t in raid_counted.items() if now - float(t) > 3600]:
                raid_counted.pop(k, None)
    arr = [t for t in raid_joins.get(cid, []) if now - float(t) < int(sget("RAID_WINDOW"))]
    arr.append(now)
    raid_joins[cid] = arr[-300:]
    if len(arr) >= max(2, int(sget("RAID_THRESHOLD"))) and not raid_until.get(cid):
        raid_until[cid] = now + max(60, int(sget("RAID_COOLDOWN")))
        try:
            await context.bot.send_message(
                cid, f"🚨 检测到疑似突袭（{int(sget('RAID_WINDOW'))} 秒内 {len(arr)} 人进群），"
                     f"已临时开启人墙：新人进群需先完成验证，{int(sget('RAID_COOLDOWN'))} 秒后自动恢复。")
        except Exception:
            pass
        try:
            await context.bot.send_message(
                ADMIN_USER_ID, f"🚨 防突袭：群 <code>{cid}</code> {int(sget('RAID_WINDOW'))} 秒内 {len(arr)} 人进群，已临时人墙。")
        except Exception:
            pass

async def lurker_sweep(context):
    """潜水号清理（每 6 小时）：入群超 LURKER_DAYS 天且累计发言少于 LURKER_MSGS 条 → 按档处理。

    处理过/已豁免的人记 lurker_checked 不反复骚扰；管理员豁免。
    """
    for cid, joined in list(member_joined_at.items()):
        if not group_get(cid, "lurker_enabled"):
            continue          # 该群没开潜水清理（群级可覆盖全局开关）
        _CUR_CID.set(_safe_cid(cid))   # 天数/条数等阈值按该群配置解析
        hits = []
        for uid, jt in list(joined.items()):
            key = f"{cid}:{uid}"
            if key in lurker_checked:
                continue
            if not jt or time.time() - float(jt) < max(1, int(sget("LURKER_DAYS"))) * 86400:
                continue
            lurker_checked.add(key)   # 不论结果只处理一次（活跃者以后也不会变潜水：发言数只增不减）
            if is_bot_admin(uid):
                continue
            prof = member_profiles.get(cid, {}).get(uid, {}) or {}
            if int(prof.get("msgs", 0) or 0) >= int(sget("LURKER_MSGS")):
                continue
            hits.append((uid, str(prof.get("name") or f"用户{uid}")))
        if not hits:
            continue
        if sget("LURKER_ACTION") == 0:
            try:
                await context.bot.send_message(
                    ADMIN_USER_ID,
                    f"💤 潜水巡查：群 <code>{cid}</code> 发现 {len(hits)} 个潜水号"
                    f"（入群超 {int(sget('LURKER_DAYS'))} 天、发言少于 {int(sget('LURKER_MSGS'))} 条）：\n"
                    + "\n".join(f"· {html.escape(nm)}（{u_}）" for u_, nm in hits[:20])
                    + "\n可在「群管中心」改为自动禁言/踢出。")
            except Exception:
                pass
        else:
            for u_, nm in hits:
                await _mod_punish(context, cid, u_, sget("LURKER_ACTION"), sget("SENSITIVE_MUTE_SECONDS"), nm, "潜水清理")
            try:
                await context.bot.send_message(
                    ADMIN_USER_ID,
                    f"💤 潜水巡查：群 <code>{cid}</code> 已按配置"
                    f"{'禁言' if sget('LURKER_ACTION') == 1 else '踢出'} {len(hits)} 个潜水号。")
            except Exception:
                pass

async def announce_sweep(context):
    """定时群公告（每 60 秒）：北京时间到 ANNOUNCE_TIME 后向全部授权群推一条，一天只发一次。"""
    if not sget("ANNOUNCE_ENABLED"):
        return
    global announce_last_date
    try:
        hh, mm = (int(x) for x in str(sget("ANNOUNCE_TIME")).strip().split(":")[:2])
        if not (0 <= hh <= 23 and 0 <= mm <= 59):
            return
    except Exception:
        return
    now = now_bj()
    target = now.replace(hour=hh, minute=mm, second=0, microsecond=0)
    if now < target or announce_last_date == now.strftime("%Y-%m-%d"):
        return
    txt = str(sget("ANNOUNCE_TEXT") or "").strip()
    if not txt:
        return
    announce_last_date = now.strftime("%Y-%m-%d")   # 先记再发：丢一条公告好过刷屏重发
    save_data()
    n = 0
    for cid in sorted(AUTHORIZED_GROUPS):
        try:
            await context.bot.send_message(cid, txt.replace("{date}", announce_last_date))
            n += 1
        except Exception:
            logger.exception("定时公告推送失败 cid=%s", cid)
    try:
        await context.bot.send_message(
            ADMIN_USER_ID, f"📣 定时群公告已推送到 {n}/{len(AUTHORIZED_GROUPS)} 个群。")
    except Exception:
        pass

async def observe_check_sweep(context):
    """观察期到期巡检：观察期走完的人复核一次，发言不达标（可选：无头像）→ 提醒/禁言/踢出。

    只在 OBSERVE_CHECK_ENABLED 打开时干活；处理过的人记进 observe_checked，不会反复骚扰。
    """
    now = time.time()
    for cid, joined in list(member_joined_at.items()):
        if not group_get(cid, "observe_check_enabled") or group_get(cid, "observe_seconds") <= 0:
            continue          # 该群没开观察期复核（群级可覆盖全局开关）
        _CUR_CID.set(_safe_cid(cid))   # 观察时长/达标条数/动作按该群配置解析
        for uid, jt in list(joined.items()):
            key = f"{cid}:{uid}"
            if key in observe_checked:
                continue
            if not jt or now - float(jt) < sget("OBSERVE_SECONDS"):
                continue
            observe_checked.add(key)          # 先标记，避免异常导致反复处理
            if is_bot_admin(uid):
                continue
            prof = member_profiles.get(cid, {}).get(uid, {}) or {}
            name = prof.get("name") or f"用户{uid}"
            msgs = int(prof.get("msgs", 0) or 0)
            if msgs >= sget("OBSERVE_CHECK_MSGS"):
                continue
            if sget("OBSERVE_CHECK_AVATAR") and msgs == 0:
                try:
                    ch = await context.bot.get_chat(uid)
                    if getattr(ch, "photo", None):
                        continue            # 有头像就不算小号
                except Exception:
                    pass
            if sget("OBSERVE_CHECK_ACTION") == 0:
                try:
                    await context.bot.send_message(
                        ADMIN_USER_ID,
                        f"🔎 观察期巡检：群 <code>{cid}</code> 的 {html.escape(str(name))}（{uid}）"
                        f"观察期已满但本群发言仅 {msgs} 条，请留意（可在「群管中心」配置为自动禁言/移出）。")
                except Exception:
                    pass
            else:
                await _mod_punish(context, cid, uid, sget("OBSERVE_CHECK_ACTION"), sget("SENSITIVE_MUTE_SECONDS"), name, "观察期巡检")
                try:
                    await context.bot.send_message(
                        ADMIN_USER_ID,
                        f"🔎 观察期巡检：{html.escape(str(name))}（{uid}）已"
                        f"{'禁言' if sget('OBSERVE_CHECK_ACTION') == 1 else '移出群'}。")
                except Exception:
                    pass

async def on_media(update, context):
    """自动删除规则中心：非文本消息（图/视频/贴纸/文件/联系人/系统消息等）按开关静默撤删。"""
    _bind_update_cid(update)
    try:
        # 黑名单拦截：命令/文本/回调入口都拦了，媒体消息此前漏了 → 拉黑形同虚设
        u = update.effective_user
        if u and not u.is_bot and u.id in BLACKLISTED_USERS and not is_bot_admin(u.id):
            try: await update.effective_message.delete()
            except Exception: pass
            return
        # 强制订阅：媒体消息（表情包/图片/视频等）也必须拦——此前只在 on_text 拦截，
        # 未订阅的新人发个表情包就能照常聊天（用户报障「只删文字，不删表情包那些」）
        if await _forcesub_enforce(update, context):
            return
        # 观察期：媒体消息同样要拦（同一条漏口，一并收口）
        if await _observe_enforce(update, context):
            return
        if await _autodel_enforce(update, context):
            return
        # 等级消息管控：超出当前等级权限的消息类型撤删（双路径，见 on_media）
        if await _level_msg_enforce(update, context):
            return
        # 敏感词：媒体消息的 caption 同样要查（此前只查文本 → 表情包/图片配文里的敏感词漏网）
        if await _sensitive_enforce(update, context):
            return
    except Exception:
        logger.exception("自动删除(媒体)异常（已吞并）")

async def on_text(update, context):
    # 外层 try 包命令分发；开头校验单独内层 try（消息结构异常属噪音，静默忽略）
    _bind_update_cid(update)
    try:
        # 开头校验：无效消息静默跳过，不打扰用户
        try:
            message, user = update.effective_message, update.effective_user
            if not message or not message.text or not user or user.is_bot: return
            if message.date and (datetime.now(timezone.utc) - message.date).total_seconds() > sget("STALE_TEXT_COMMAND_SECONDS"):
                return
            cid, text = update.effective_chat.id, message.text.strip()
            _remember_name(update)
        except Exception:
            return
        # 拉黑拦截：被封禁用户（非管理员）禁止使用全部功能，连帮助都看不到
        if update.effective_user.id in BLACKLISTED_USERS and not is_bot_admin(update.effective_user.id):
            await send_reply(update, context, "🚫 你已被禁止使用本机器人，如有疑问请联系管理员。"); return

        # 强制订阅频道（默认关；管理员豁免）：未订阅者发言即删+提示，订阅后一分钟内自动放行
        if await _forcesub_enforce(update, context):
            return

        # 新成员观察期：入群未满观察时长的成员发言即删，并禁言至观察期结束（管理员豁免）
        if await _observe_enforce(update, context):
            return

        # 自动删除规则中心：链接/超长/会员表情（媒体消息走 on_media；管理员豁免）
        if await _autodel_enforce(update, context):
            return

        # 等级消息管控：当前等级不允许的消息类型（如 L1 发图）撤删 + 违规计数
        if await _level_msg_enforce(update, context):
            return

        # 敏感词过滤（默认关；管理员豁免）：命中即删，可叠加禁言/踢出
        if await _sensitive_enforce(update, context):
            return

        # 入群验证答题：放在过滤之后 —— 图片模式待验证者不禁言，若这里先消费掉发言，
        # 敏感词/订阅/观察期等规则对「正在验证的人」全部失效（用户报截图中的人连发违禁词未被处理）。
        try:
            if await _join_verify_handle_text(context, cid, user.id, text):
                return
        except Exception:
            logger.exception("入群验证答题处理异常（已吞并）")

        # 定时刷屏识别：复读机 + 定时器特征（管理员豁免；内容太短不参与统计防误伤闲聊）
        if (sget("ANTISPAM_ENABLED") and is_group_chat(update) and not is_bot_admin(user.id)
                and len(re.sub(r"\s+", "", text)) >= ANTISPAM_MIN_LEN):
            try:
                _reason = _antispam_check(cid, user.id, text)
                if _reason:
                    await _antispam_hit(update, context, cid, user.id, _reason)
                    return
            except Exception:
                logger.exception("定时刷屏识别异常（已吞并）")

        # 抽奖触发词：公告宣传的关键词直接参与（支持每个活动自带关键词；修复此前自定义词没反应）
        if is_group_chat(update) and text.strip():
            _alo = _lottery_active(cid)
            if _alo and text.strip() in {sget("LOTTERY_KEYWORD"), (_alo.get("keyword") or "").strip()}:
                await _dispatch_alias("抽奖", [], update, context)
                return

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
            _first_speak = not prof          # 首次发言（档案为空）
            if _first_speak:
                prof.update({"name": user_names.get(user.id, f"用户{user.id}"), "first": now_bj().strftime("%Y-%m-%d %H:%M"), "msgs": 0})
            prof["last"] = now_bj().strftime("%Y-%m-%d %H:%M")
            prof["msgs"] = prof.get("msgs", 0) + 1
            # 新人欢迎奖励：首次发言时发放（用户规则「新人完成入群审核 +200」）
            if _first_speak and not is_bot_admin(user.id):
                _npts, _old = _grant_newbie_reward(cid, user.id,
                                                   user_names.get(user.id) or user.first_name or "")
                if _npts:
                    _app = context.application
                    # 持有引用：裸 create_task 的任务可能被事件循环 GC 掉，升级公告会悄悄丢失
                    background_tasks.add(asyncio.create_task(_check_level_change(
                        _app, cid, user.id, _old, _earn_get(cid, user.id))))
        except Exception:
            logger.exception("成员档案记录异常（已吞并）")
        # 合格邀请结算（事件驱动）：被邀请人在本群发言后即时判定是否达标（发奖/待达标）
        try:
            if sget("INVITE_ENABLED") and is_group_chat(update):
                await _invite_ping_qualify(context.application, cid, user.id)
        except Exception:
            logger.exception("邀请达标判定异常（已吞并）")
        
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
            if not found: await send_reply(update, context, "💡 当前没有任何正在进行的游戏。")
            return

        # 21点文字加入
        blackjack = active_blackjack_games.get(cid)
        bj_match = re.fullmatch(r"(?:下注|下|押|买)?(?:21点|21)\s*(\d+)", text)
        if bj_match and blackjack:
            if blackjack.phase != "waiting":
                await send_reply(update, context, "❌ 21点已经开始，请等待下一局。"); return
            amount = int(bj_match.group(1))
            if amount < sget("BJ_MIN_BET"):
                await send_reply(update, context, f"❌ 21点最低下注 {sget('BJ_MIN_BET')} 积分。"); return
            wallet = game_chips
            async with wallet_locks[user.id]:
                if wallet[cid][user.id] < amount:
                    await send_reply(update, context, f"❌ 积分不足，你只有 {wallet[cid][user.id]}。"); return
                if blackjack.add_player(user.id, amount):
                    wallet[cid][user.id] -= amount
                else:
                    await send_reply(update, context, "❌ 你已在局中或无法加入。"); return
            await action_notice(cid, context.application, user.id, f"加入了 21点，下注 {amount}")
            await update_blackjack_ui(blackjack, context.application)
            return

        # 赛车与德州传统匹配
        match = re.fullmatch(r"下注\s+(\d+)\s+(\d+)", text); race = active_horse_races.get(cid)
        if match and race:
            horse, amount = int(match.group(1))-1, int(match.group(2))
            ok, desc = await race.bet(user.id, horse, amount)
            if not ok: await send_reply(update, context, f"❌ {desc}"); return
            race.name_cache[user.id] = await get_name(context.application, user.id)
            await action_notice(cid, context.application, user.id, f"下注 {amount} 于 {sget('HORSE_EMOJI')[horse]}")
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
                if not ok: await send_reply(update, context, f"❌ {desc}"); return
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
                if not ok: await send_reply(update, context, f"❌ {desc}"); return
                await action_notice(cid, context.application, user.id, desc)
                if game.phase == "showdown": await settle(game, context.application)
                else: await update(game, context.application); await start_timer(game, context.application)
                return

        # 大话骰：群里直接打「6个3」「6 3」「六個三」叫牌（也认「叫6个3」）；
        # 打「开」「开骰」「开牌」「不信」「掀」＝开骰
        #（仅轮到你时消费消息；不是你的回合/不是叫牌则照常走聊天积分等后续逻辑）
        _dg = active_dice_games.get(cid)
        if _dg and _dg.phase == "playing":
            if re.fullmatch(r"开骰?|开牌|开他|开盅|掀盅?|不信|不開|不开", text.replace(" ", "")):
                if user.id == _dg.actor and _dg.bid:
                    ok, _d = _dg.action(user.id, "open")
                    if ok:
                        _dg.last_action = f"{await get_name(context.application, user.id)} 开骰"
                        await _dice_del_bid_msg(context, cid, message)   # 删掉玩家发的「开骰」文本
                        await _dice_resolve_and_continue(_dg, context.application, user.id)
                        return
                elif user.id in _dg.players and not _dg.bid:
                    await send_reply(update, context, "❌ 你是先叫方，起手必须先叫牌（如「3个4」）。")
                    return
            else:
                _bid = parse_dice_bid(text)
                if _bid is not None:
                    if user.id != _dg.actor:
                        # 只有本局玩家提示「没轮到」，路人发「6 3」这类消息不受打扰
                        if user.id in _dg.players:
                            await send_reply(update, context, "❌ 还没轮到你叫牌。")
                        return
                    ok, desc = _dg.action(user.id, "bid", _bid)
                    if not ok:
                        await send_reply(update, context, f"❌ {desc}"); return
                    _dg.last_action = f"{await get_name(context.application, user.id)} 叫 {_bid[0]}个{_bid[1]}"
                    await _dice_del_bid_msg(context, cid, message)   # 删掉玩家发的叫牌文本，保持群聊清爽
                    await start_dice_turn_timer(_dg, context.application)
                    return
    except Exception:
        logger.exception("文本指令处理异常")
        # 命令分发异常不再静默：给用户明确反馈，便于排查而非毫无反应
        try:
            await send_reply(update, context, "⚠️ 指令处理出错，请联系管理员。")
        except Exception:
            pass


# ---------- 积分系统（统一钱包） ----------
# 累计获得账本：所有「真产出」入口调用 _earn_add 记账；等级按累计获得算，
# 因此花积分兑换实物/商城消费不会掉级（此前按余额算，消费即降级 = 反激励）。
def _earn_add(cid, uid, amount):
    """记一笔「累计获得」。amount<=0 忽略；异常全吞（记账失败绝不影响主流程）。"""
    try:
        amount = int(amount or 0)
        if amount > 0:
            total_earned[cid][uid] = int(total_earned[cid][uid] or 0) + amount
    except Exception:
        logger.exception("累计获得记账异常 cid=%s uid=%s（已吞并）", cid, uid)

def _earn_get(cid, uid):
    """取「累计获得」。老玩家账本为空时用「当前余额」兜底，避免升级后一夜掉级。"""
    try:
        got = int(total_earned[cid][uid] or 0)
    except Exception:
        got = 0
    if got > 0:
        return got
    try:
        return max(0, int(game_chips[cid][uid] or 0))
    except Exception:
        return 0

def _normalize_levels():
    """等级表结构归一（2026-09-09 用户需求）：旧存档 {name,value} → 补齐 perms/on。

    兼容原则：**旧数据默认全放行**（perms=LEVEL_PERM_DEFAULT, on=1），
    否则升级后老用户会突然被拦（历史无权限概念，不能追溯处罚）。
    幂等：可重复调用。
    """
    for it in sget("POINT_LEVELS"):
        if not isinstance(it, dict):
            continue
        if "perms" not in it or not isinstance(it.get("perms"), str):
            # 旧存档缺字段 → 兼容放行（不能追溯处罚老用户）
            it["perms"] = LEVEL_PERM_DEFAULT
        else:
            # 空串是用户在网页上显式「一个都不勾」= 全部禁止，必须保留（不能补默认）
            picked = {p.strip() for p in it["perms"].split(",") if p.strip()}
            it["perms"] = ",".join(k for k, _v in LEVEL_PERM_OPTIONS if k in picked)
        if "on" not in it:
            it["on"] = 1
        else:
            it["on"] = 1 if str(it.get("on")).strip().lower() in ("1", "true", "on", "yes", "是") else 0


def _set_level_enabled(v):
    """开关积分等级系统（测试与网页共用入口）。"""
    global LEVEL_ENABLED
    LEVEL_ENABLED = 1 if str(v).strip().lower() in ("1", "true", "on", "yes", "是") else 0
    return LEVEL_ENABLED


def _level_perms(cid, uid):
    """取该用户当前等级允许的消息类型集合。未达最低等级/表为空 → 返回全部（放行）。"""
    if not sget("POINT_LEVELS"):
        return set(k for k, _v in LEVEL_PERM_OPTIONS)
    cur = _level_item(cid, uid)
    if cur is None:
        return set(k for k, _v in LEVEL_PERM_OPTIONS)   # 未达最低等级：放行，不惩罚新人
    raw = str(cur.get("perms") if cur.get("perms") is not None else LEVEL_PERM_DEFAULT)
    return {p.strip() for p in raw.split(",") if p.strip()}


def _level_allows(cid, uid, kind):
    """该用户当前等级是否允许发送某类消息。总开关关/表空/未达最低等级 → 一律放行。"""
    if not sget("LEVEL_ENABLED") or not sget("LEVEL_MSG_GUARD_ENABLED"):
        return True
    if not sget("POINT_LEVELS"):
        return True
    return str(kind) in _level_perms(cid, uid)


def _msg_kind(message, text=""):
    """判定一条消息的类型（用于等级权限校验）。返回 LEVEL_PERM_OPTIONS 的键。

    优先级：转发 > 贴纸 > 图片 > 视频 > 音频 > 链接 > 编辑 > 文字。
    转发优先于内容类型：用户要的是「能不能转发」这一维度的管控。
    """
    if message is None:
        return "text"
    if getattr(message, "forward_origin", None) or getattr(message, "forward_from", None) \
            or getattr(message, "forward_from_chat", None) or getattr(message, "forward_sender_name", None):
        return "forward"
    if getattr(message, "sticker", None) is not None:
        return "sticker"
    if getattr(message, "photo", None) is not None:
        return "photo"
    if getattr(message, "video", None) is not None or getattr(message, "video_note", None) is not None:
        return "video"
    if getattr(message, "audio", None) is not None or getattr(message, "voice", None) is not None:
        return "audio"
    t = str(text or "")
    if ("http://" in t or "https://" in t or "t.me/" in t
            or any(getattr(e, "type", None) in ("url", "text_link") for e in (getattr(message, "entities", None) or []))):
        return "link"
    if getattr(message, "edit_date", None):
        return "edit"
    return "text"


def _level_msg_hit(cid, uid, message, text=""):
    """等级消息管控判定。返回被拦截的消息类型键，放行返回 None。"""
    if not sget("LEVEL_ENABLED") or not sget("LEVEL_MSG_GUARD_ENABLED"):
        return None
    if not sget("POINT_LEVELS"):
        return None
    if is_bot_admin(uid):
        return None
    kind = _msg_kind(message, text)
    if _level_allows(cid, uid, kind):
        return None
    return kind


def _level_violation_hit(cid, uid):
    """记一次等级消息违规，返回 (窗口内次数, 是否达惩罚阈值)。

    窗口与阈值来自网页配置（LEVEL_MSG_WINDOW / LEVEL_MSG_MAX_HITS）。
    达阈值后清空窗口，避免「到阈值后每发一条都触发一次惩罚」。
    """
    now = time.time()
    win = max(1, int(sget("LEVEL_MSG_WINDOW")))
    lst = [t for t in (level_msg_violations.get((cid, uid)) or []) if now - t <= win]
    lst.append(now)
    level_msg_violations[(cid, uid)] = lst[-50:]
    n = len(lst)
    if n >= max(1, int(sget("LEVEL_MSG_MAX_HITS"))):
        level_msg_violations.pop((cid, uid), None)
        return n, True
    return n, False


async def _level_msg_enforce(update, context):
    """等级消息管控执行：超出等级权限的消息撤删 + 违规计数 + 达阈值惩罚。

    返回 True 表示已处理（调用方应停止后续处理）。
    双路径接入：on_text 与 on_media 都要调（媒体消息走 on_media）。
    """
    try:
        if not sget("LEVEL_ENABLED") or not sget("LEVEL_MSG_GUARD_ENABLED"):
            return False
        user, message = update.effective_user, update.effective_message
        if not message or not user or user.is_bot or not is_group_chat(update):
            return False
        if is_bot_admin(user.id):
            return False
        cid = update.effective_chat.id
        if cid not in AUTHORIZED_GROUPS:
            return False
        text = message.text or message.caption or ""
        kind = _level_msg_hit(cid, user.id, message, text)
        if not kind:
            return False
        try:
            await message.delete()
        except Exception:
            # 生产上是 TelegramError（无删除权限等）；测试桩/异常结构也不许中断管控流程
            try:
                await context.bot.delete_message(cid, message.message_id)
            except Exception:
                pass
        name = user.first_name or user_names.get(user.id) or f"用户{user.id}"
        lv = _level_of(cid, user.id)[0] or "无"
        n, over = _level_violation_hit(cid, user.id)
        if over and int(sget("LEVEL_MSG_PUNISH")):
            secs = int(sget("LEVEL_MSG_MUTE_SECONDS"))
            if int(sget("LEVEL_MSG_PUNISH")) == 1:
                if secs <= 0:
                    return True          # 0=不禁言（只删消息 + 已发提示）
                if secs < 30:
                    # 用户口径：小于 30 秒 = 永久禁言。_mod_punish 有 max(30,..) 下限，
                    # 无法表达「永久」，这里直接 restrict 且不带 until_date。
                    try:
                        await context.bot.restrict_chat_member(
                            cid, user.id, permissions=ChatPermissions(can_send_messages=False))
                    except Exception:
                        logger.exception("等级消息管控：永久禁言失败 cid=%s uid=%s（已吞并）", cid, user.id)
                    mute_txt = _fmt_tpl("level_msg_mute_tpl", name=html.escape(str(name)), seconds="永久")
                else:
                    await _mod_punish(context, cid, user.id, 1, secs, name, "等级消息越权")
                    mute_txt = _fmt_tpl("level_msg_mute_tpl", name=html.escape(str(name)), seconds=str(secs))
                try:
                    await context.bot.send_message(cid, mute_txt)
                except Exception:
                    pass
            else:
                await _mod_punish(context, cid, user.id, 2, 0, name, "等级消息越权")
            return True
        # 未达惩罚阈值：发一次违规提示（按 REPLY_DELETE_SECONDS 自动回收，防刷屏）
        try:
            tip = await context.bot.send_message(
                cid, _fmt_tpl("level_msg_warn_tpl", name=html.escape(str(name)),
                              level=html.escape(str(lv)),
                              kind=html.escape(str(LEVEL_PERM_NAMES.get(kind, kind))),
                              count=str(n), limit=str(int(sget("LEVEL_MSG_MAX_HITS")))))
            if sget("REPLY_DELETE_SECONDS") > 0:
                schedule_delete(context.application, cid, tip, sget("REPLY_DELETE_SECONDS"))
        except Exception:
            pass
        return True
    except Exception:
        logger.exception("等级消息管控异常（已吞并）")
        return False


def _level_base(cid, uid):
    """等级判定基数。降级开关开 → 当前余额；否则 → 累计获得（消费不掉级）。"""
    if sget("LEVEL_ALLOW_DEMOTE"):
        try:
            return max(0, int(game_chips[cid][uid] or 0))
        except Exception:
            return 0
    return _earn_get(cid, uid)


def _level_item(cid, uid):
    """返回该用户当前命中的等级 dict（跳过停用等级）；未达最低等级返回 None。"""
    base = _level_base(cid, uid)
    cur = None
    for it in sget("POINT_LEVELS"):
        if not int(it.get("on", 1) or 0):
            continue   # 停用等级不参与判定（与 _get_level 口径一致）
        if base >= int(it.get("value", 0) or 0):
            cur = it
    return cur


def _level_of(cid, uid):
    """返回 (等级名, 用于判定的数值)。等级判定唯一口径。"""
    base = _level_base(cid, uid)
    return _get_level(base), base

def _get_level(balance):
    """按积分等级表返回当前等级名，表为空返回空串。停用的等级不参与判定。"""
    lv = ""
    for item in sget("POINT_LEVELS"):
        if not int(item.get("on", 1) or 0):
            continue
        if balance >= int(item.get("value", 0) or 0):
            lv = item["name"]
    return lv

def _level_rank(lv_name):
    """等级名 -> 在等级表中的序号（升序），未找到返回 -1。"""
    for i, item in enumerate(sget("POINT_LEVELS")):
        if item["name"] == lv_name:
            return i
    return -1

async def _level_sync_member_tag(app, cid, uid, level_name=None):
    """积分称号同步成员标签（用户截图「积分称号同步成员标签开关」）。

    用 Telegram 原生 set_chat_member_tag 把当前等级名写成成员标签（群昵称后的标识）。
    失败静默：非管理员/权限不足/群不支持 都不影响主流程（等级系统照常工作）。
    """
    try:
        if not sget("LEVEL_SYNC_TAG"):
            return False
        lv = level_name if level_name is not None else _level_of(cid, uid)[0]
        if not lv:
            return False
        await app.bot.set_chat_member_tag(cid, uid, lv[:16])
        return True
    except Exception:
        logger.debug("同步成员标签失败（已忽略）：cid=%s uid=%s", cid, uid, exc_info=True)
        return False


async def _check_level_change(app, cid, uid, old_earned, new_earned, balance=None):
    """「累计获得」变动后检查**升级**并发群内通知（LEVEL_NOTIFY_ENABLED 控制）。

    old_earned/new_earned 是**累计获得**（不是余额）——花积分不会掉级，所以消费点
    不该再调本函数（此前兑换/商城误传余额，导致花分就发降级公告）。
    本函数**只发升级公告**，减少/异常输入一律静默（降级走 _check_level_drop_on_spend）。

    接入点：签到 / 管理员加分 / 转赠收款 / 红包领取 / 邀请奖励 / 竞猜派彩 / 游戏结算 / 归零赠送。
    聊天积分小额高频，刻意不接（避免刷屏）。
    """
    try:
        if not sget("POINT_LEVELS"):
            return
        old_v, new_v = int(old_earned or 0), int(new_earned or 0)
        if new_v <= old_v:
            return   # 只可能升不可能降（累计账本只增）；减少=异常输入，不公告
        old_lv, new_lv = _get_level(old_v), _get_level(new_v)
        if old_lv == new_lv:
            return
        await _level_sync_member_tag(app, cid, uid, new_lv)   # 称号同步标签（开关控制）
        if not sget("LEVEL_NOTIFY_ENABLED"):
            return
        name = await get_name(app, uid, cid=cid)
        show_bal = game_chips[cid][uid] if balance is None else balance
        await send_settle(app, cid, _fmt_tpl("level_up_msg_tpl", name=name, level=new_lv, balance=show_bal))
    except Exception:
        logger.exception("等级变动通知失败（已忽略）")


async def _check_level_drop_on_spend(app, cid, uid, before_balance):
    """扣分后检查是否因余额下降而**降级**并发通知。

    仅在 LEVEL_ALLOW_DEMOTE（积分不足是否允许降级）开启时生效——默认关闭时
    等级按累计获得判定，花分不掉级，本函数直接返回（零开销）。
    在扣分点调用，传扣分前的余额。
    """
    try:
        if not sget("LEVEL_ALLOW_DEMOTE") or not sget("POINT_LEVELS"):
            return
        old_v = max(0, int(before_balance or 0))
        new_v = max(0, int(game_chips[cid][uid] or 0))
        if new_v >= old_v:
            return
        old_lv, new_lv = _get_level(old_v), _get_level(new_v)
        if old_lv == new_lv:
            return
        await _level_sync_member_tag(app, cid, uid, new_lv)
        if not sget("LEVEL_DOWN_NOTIFY_ENABLED"):
            return
        name = await get_name(app, uid, cid=cid)
        await send_settle(app, cid, _fmt_tpl("level_down_msg_tpl", name=name,
                                             level=new_lv or "无", balance=new_v))
    except Exception:
        logger.exception("扣分降级检查失败（已忽略）")

def _mall_price(item):
    """商品价格兼容新旧结构（旧 {"name","value"} / 新 {"name","price",...}）。"""
    try:
        return int(item.get("price", item.get("value", 0)) or 0)
    except (TypeError, ValueError):
        return 0

async def cmd_my_level(update, context):
    """查询我的积分等级与距下一级的差距。"""
    if not await need_auth(update, context): return
    cid, uid = update.effective_chat.id, update.effective_user.id
    if not sget("POINT_LEVELS"):
        await send_reply(update, context, _fmt_tpl("level_query_none_tpl")); return
    bal = game_chips[cid][uid]
    lv, base = _level_of(cid, uid)
    next_lv, next_val = "", None
    for item in sget("POINT_LEVELS"):
        if not int(item.get("on", 1) or 0):
            continue
        if int(item.get("value", 0) or 0) > base and (next_val is None or item["value"] < next_val):
            next_lv, next_val = item["name"], int(item["value"])
    nxt = f"\n⬆️ 下一等级：{next_lv}（还差 {next_val - base} 积分）" if next_lv else "\n🏆 你已是最高等级！"
    base_line = ("📈 累计获得：{v}（等级按此计算，消费不降级）".format(v=base)
                 if not sget("LEVEL_ALLOW_DEMOTE") else "📈 等级按当前积分计算（积分不足会降级）")
    await send_reply(update, context,
                     _fmt_tpl("level_query_msg_tpl", name=await get_name(context.application, uid),
                              level=lv or "无", balance=bal, earned=base,
                              base_line=base_line, next_line=nxt))

def _chat_is_effective(cid, uid, text, min_len=None):
    """有效发言判定（2026-09-09 用户规则）：正常话题/有内容的讨论才算有效。

    三条否决（任一命中即不计分）：
      ① 过短：去掉空白后长度 < min_len（仅「每N字符」旧规则模式检查；
              规则表模式由用户自己配条件，不额外卡长度）
      ② 纯符号/表情：把标点、emoji、空白全部剔除后什么都不剩
              （如「😂😂😂」「。。。」「!!!!」「👍👍。。。」）→ 无信息量，不计分
      ③ 无意义：整条消息只由黑名单词/标点/表情构成（如「哈哈」「哦哦」「收到」）
      ④ 灌水：窗口内同一内容已发 CHAT_DUP_N 条（复读机）
    纯表情包/图片本身走 on_media，不经过本函数（天然不计分）。
    """
    t = str(text or "").strip()
    if not t:
        return False
    if min_len is not None and len(re.sub(r"\s+", "", t)) < max(1, int(min_len)):
        return False
    # ② 纯符号/表情：剔除标点、符号、emoji、空白后若无任何中文/字母/数字 → 无信息量
    #    无条件生效（规则表模式也不能给纯表情/纯符号送分）
    if not re.sub(r"[\s\W_]+", "", t, flags=re.UNICODE):
        return False
    # ③ 无意义词：把黑名单词与常见标点/空白全部剔除后，若什么都不剩 → 纯无意义
    if sget("CHAT_JUNK_WORDS"):
        _r = t
        for w in sget("CHAT_JUNK_WORDS"):
            w = str(w).strip()
            if w:
                _r = _r.replace(w, "")
        _r = re.sub(r"[\s\W_]+", "", _r, flags=re.UNICODE)
        if not _r:
            return False
    # ④ 重复灌水：本函数独立记录（不复用 antispam_hist——那个受 ANTISPAM_ENABLED 开关
    #    与 ANTISPAM_MIN_LEN 长度门槛控制，关掉刷屏识别后重复检测会静默失效）
    _n = int(sget("CHAT_DUP_N"))
    if _n > 0:
        _key = (cid, uid, _antispam_norm(t))
        _now = time.time()
        _win = max(10, int(sget("CHAT_DUP_WINDOW")))
        _hist = [x for x in (chat_dup_hist.get(_key) or []) if _now - x <= _win]
        _dup = len(_hist) >= _n          # 先判定：本条之前的条数已达阈值 → 本条不计分
        _hist.append(_now)
        chat_dup_hist[_key] = _hist[-20:]
        if _dup:
            return False
    return True


def _award_chat_points(cid, uid, text):
    """聊天积分：优先走网页配置的规则表（阿福式：文字/长度条件 → 分值，命中即停）；
    规则表为空或全停时回退旧逻辑（每 N 字符记 X 分）。均受每日上限约束。

    2026-09-09：加「有效发言」前置判定——无意义词/重复灌水一律不计分；
    长度门槛只在旧规则模式生效（规则表模式由用户配置的条件决定，不额外卡长度）。
    """
    if not sget("CHAT_ENABLED"):
        return
    t = text.strip()
    enabled = [r for r in chat_rules if r.get("on")]
    if not _chat_is_effective(cid, uid, t, min_len=None if enabled else sget("CHAT_MIN_LEN")):
        return
    if enabled:
        gain = 0
        for r in enabled:
            m = str(r.get("match", "")).strip()
            if not m or m in t:                      # 空 match=任意消息兜底；其余=包含即命中
                gain = int(r.get("points", 0) or 0)
                break
            if m.startswith("len>="):
                try:
                    if len(t) >= int(m[5:]):
                        gain = int(r.get("points", 0) or 0)
                        break
                except ValueError:
                    pass
        else:
            return                                   # 有启用规则但一条都没命中 → 不加分
    else:
        if sget("CHAT_REWARD") <= 0 or sget("CHAT_CHARS_PER") <= 0:
            return
        n = len(t)
        if n < sget("CHAT_CHARS_PER"):
            return
        gain = (n // sget("CHAT_CHARS_PER")) * sget("CHAT_REWARD")
    if gain <= 0:
        return
    date = now_bj().strftime("%Y-%m-%d")
    today = chat_today[date][cid]
    earned = today.get(uid, 0)
    if sget("CHAT_DAILY_CAP") > 0:
        gain = min(gain, sget("CHAT_DAILY_CAP") - earned)
        if gain <= 0:
            return
    today[uid] = earned + gain
    game_chips[cid][uid] += gain
    _earn_add(cid, uid, gain)   # 聊天积分计入累计获得（等级口径），但不发升级通知（高频防刷屏）

async def cmd_sign(update, context):
    if not await need_auth(update, context): return
    if not sget("SIGN_ENABLED"):
        await send_reply(update, context, "ℹ️ 签到功能未开启。"); return
    if not is_group_chat(update):
        await send_reply(update, context, "⚠️ 签到请在群聊中进行。"); return
    cid, uid = update.effective_chat.id, update.effective_user.id
    today = now_bj().strftime("%Y-%m-%d")
    yesterday = (now_bj() - timedelta(days=1)).strftime("%Y-%m-%d")
    info = sign_data[cid][uid]
    if info.get("last") == today:
        await send_reply(update, context, f"✅ 今天已经签过啦（连续 {info.get('streak', 0)} 天）。"); return
    streak = info.get("streak", 0) + 1 if info.get("last") == yesterday else 1
    reward = sget("SIGN_BASE_REWARD") + (sget("SIGN_STREAK_BONUS") if streak % 7 == 0 else 0)
    async with wallet_locks[uid]:
        old_earned = _earn_get(cid, uid)
        game_chips[cid][uid] += reward
        _earn_add(cid, uid, reward)
        sign_data[cid][uid] = {"last": today, "streak": streak}
        save_data()
    bonus = "（含连续7天额外奖励）" if streak % 7 == 0 else ""
    msg = _fmt_tpl("sign_msg_tpl", name=await get_name(context.application, uid),
                   streak=streak, reward=reward, bonus=bonus, balance=game_chips[cid][uid])
    await send_reply(update, context, msg)
    await _check_level_change(context.application, cid, uid, old_earned, _earn_get(cid, uid))
    # 合格邀请结算（事件驱动）：被邀请人签到加分后也即时判定是否达标
    try:
        if sget("INVITE_ENABLED"):
            await _invite_ping_qualify(context.application, cid, uid)
    except Exception:
        logger.exception("邀请达标判定异常（已吞并）")

async def cmd_sign_rank(update, context):
    if not await need_auth(update, context): return
    cid = update.effective_chat.id
    users = [(uid, v.get("streak", 0)) for uid, v in sign_data.get(cid, {}).items() if v.get("streak", 0) > 0]
    if not users:
        await send_reply(update, context, "本群还没有签到记录，发「签到」抢头名！"); return
    lines = ["📅 连续签到排行", "━" * 14]
    for i, (uid, s) in enumerate(sorted(users, key=lambda x: (-x[1], x[0]))[:20], 1):
        lines.append(f"{rank_marker(i)} {await get_name(context.application, uid, cid=cid)}：连续 {s} 天")
    await send_reply(update, context, "\n".join(lines))

async def cmd_my_points(update, context):
    if not await need_auth(update, context): return
    cid, uid = update.effective_chat.id, update.effective_user.id
    balance = game_chips[cid][uid]
    date = now_bj().strftime("%Y-%m-%d")
    today_chat = chat_today.get(date, {}).get(cid, {}).get(uid, 0)
    streak = sign_data.get(cid, {}).get(uid, {}).get("streak", 0)
    signed = "✅ 已签" if sign_data.get(cid, {}).get(uid, {}).get("last") == date else "❌ 未签"
    lv, earned = _level_of(cid, uid)   # 等级按累计获得，与「我的等级」口径一致
    lv_line = f"🎖 等级：{lv}\n" if lv else ""
    msg = _fmt_tpl("query_msg_tpl", name=await get_name(context.application, uid),
                   balance=balance, level_line=lv_line, signed=signed, streak=streak, today_chat=today_chat)
    reply = await send_reply(update, context, msg)
    return reply

async def cmd_points_rank(update, context):
    if not await need_auth(update, context): return
    cid = update.effective_chat.id
    lines = ["💰 积分排行榜", "━" * 14]
    for i, (uid, value) in enumerate(sorted(game_chips[cid].items(), key=lambda x: x[1], reverse=True)[:20], 1):
        lv = _level_of(cid, uid)[0]   # 等级按累计获得（与我的等级一致）
        tag = f"｜{lv}" if lv else ""
        lines.append(f"{rank_marker(i)} {await get_name(context.application, uid, cid=cid)}：{value}{tag}")
    msgs = await safe_send_long(context.bot, cid, "\n".join(lines))
    if sget("REPLY_DELETE_SECONDS") > 0 and is_group_chat(update):
        schedule_delete(context.application, cid, msgs, sget("REPLY_DELETE_SECONDS"))

def _parse_dt_bj(spec):
    """'YYYY-MM-DD HH:MM' 或 'YYYY-MM-DD'（北京时间）→ aware datetime；空/非法返回 None。"""
    spec = (spec or "").strip()
    if not spec: return None
    for fmt in ("%Y-%m-%d %H:%M", "%Y-%m-%d"):
        try: return datetime.strptime(spec, fmt).replace(tzinfo=BEIJING_TZ)
        except ValueError: continue
    return None

def _redeem_gate():
    """兑换时间窗检查：返回拒绝文案或 None（可兑换）。"""
    now = now_bj()
    start, end = _parse_dt_bj(sget("REDEEM_START")), _parse_dt_bj(sget("REDEEM_END"))
    if start and now < start:
        return f"⏳ 兑换活动尚未开始（{sget('REDEEM_START')} 起）。"
    if end and now > end:
        return "🔚 兑换活动已结束。"
    return None

async def _redeem_execute(context, cid, uid, item):
    """执行兑换（命令与按钮回调共用）：限购→扣费→自动下架→台账→群通知+私聊通知。
    返回 None=成功；字符串=拒绝原因。"""
    if sget("REDEEM_MAX_PER_USER") > 0 and redeem_counts.get(uid, 0) >= sget("REDEEM_MAX_PER_USER"):
        return f"❌ 每人限兑 {sget('REDEEM_MAX_PER_USER')} 次，你已用完额度。"
    price = int(item.get("price", 0) or 0)
    left = int(item.get("left", 0) or 0)
    async with wallet_locks[uid]:
        if game_chips[cid][uid] < price:
            return f"❌ 积分不足：需要 {price}，当前 {game_chips[cid][uid]}。"
        game_chips[cid][uid] -= price
        if left > 0:
            item["left"] = left - 1
            if item["left"] <= 0:
                item["on"] = False  # 兑完自动下架
        item["redeemed"] = int(item.get("redeemed", 0) or 0) + 1
        redeem_counts[uid] = redeem_counts.get(uid, 0) + 1
        ledger_add(cid, uid, 0, price, "兑换")  # 资金流台账：玩家→系统
        order_no = f"DH-{secrets.token_hex(4)}"  # 防伪单号：群通知/私聊/管理员对账三处一致
        order_ts = now_bj().strftime("%Y-%m-%d %H:%M")
        redeem_orders.append({"no": order_no, "ts": order_ts, "cid": cid, "uid": uid,
                              "item": item["name"], "price": price, "bal": game_chips[cid][uid]})
        del redeem_orders[:-500]  # 只留最近 500 条，防膨胀
        save_data()
    uname = await get_name(context.application, uid)
    # 群通知不带防伪单号（群友能看到别人的单号就失去核验意义）；单号只发用户私聊+管理员对账
    await send_settle(context.application, cid, _fmt_tpl("redeem_msg_ok_group",
        name=uname, goodsName=item["name"], pointNum=price,
        balance=game_chips[cid][uid]))
    # 消费点不再检查等级：等级按「累计获得」算，花分不掉级（此前误传余额 → 花分即降级公告）
    try:
        await context.bot.send_message(uid, _fmt_tpl("redeem_msg_ok_dm", goodsName=item["name"], pointNum=price)
                                       + f"\n🔎 防伪单号 {order_no}（管理员发货凭此号核对）")
    except TelegramError:
        pass  # 未私聊过 bot 的用户收不到 DM；单号仍在管理员对账+后台兑换订单页可查
    try:
        await context.bot.send_message(ADMIN_USER_ID,
            f"🧾 积分兑换订单｜单号 {order_no}\n群：{chat_name_cache.get(cid, cid)}\n"
            f"用户：{uname}（{uid}）\n商品：{item['name']}（{price} 积分）\n时间：{order_ts}")
    except Exception:
        logger.exception("兑换订单通知管理员失败")
    return None

async def _redeem_buy_cb(q, idx, context):
    """蓝色按钮点一下直接兑换：idx=上架商品编号（与列表消息一致）。"""
    cid, uid = q.message.chat.id, q.from_user.id
    gate = _redeem_gate()
    if gate:        await q.answer(gate, show_alert=True); return
    items = [x for x in redeem_goods if x.get("on", True)
             and (not x.get("target_groups") or cid in x["target_groups"])]
    if not (1 <= idx <= len(items)):
        await q.answer("❌ 商品不存在或已下架，重新发「%s」看最新列表" % REDEEM_CMD, show_alert=True); return
    err = await _redeem_execute(context, cid, uid, items[idx - 1])
    if err:
        await q.answer(err, show_alert=True)
    else:
        await q.answer("🎉 兑换成功！")


def _redeem_items_for(cid):
    """本群可见的兑换商品（上架 + target_groups 命中本群）。"""
    return [x for x in redeem_goods if x.get("on", True)
            and (not x.get("target_groups") or cid in x["target_groups"])]


def _mall_items_on():
    return [x for x in sget("MALL_ITEMS") if x.get("on", True)]


def _deep_buy_url(kind, cid, idx):
    """竞品式兑换按钮：https://t.me/<bot>?start=<kind>_<cid>_<idx>，点了跳转 bot 私聊。
    _BOT_USERNAME 为空（启动早期/测试桩）时返回 None → 调用方退回群内 callback 直兑。"""
    if not _BOT_USERNAME:
        return None
    return f"https://t.me/{_BOT_USERNAME}?start={kind}_{cid}_{idx}"


async def _redeem_dm_ok(context, cid, uid, idx):
    """私聊「是否兑换 → 确认」：二次校验（时间窗/商品/余额）后执行兑换。
    返回 (ok, 提示文本)。群通知+私聊单号+管理员对账全部走 _redeem_execute。"""
    if not is_auth(cid):
        return False, "❌ 该群未授权使用本机器人。"
    gate = _redeem_gate()
    if gate:
        return False, gate
    items = _redeem_items_for(cid)
    if not (1 <= idx <= len(items)):
        return False, "❌ 商品不存在或已下架，请回群重新打开列表。"
    err = await _redeem_execute(context, cid, uid, items[idx - 1])
    if err:
        return False, err
    return True, f"🎉 兑换成功：{items[idx - 1]['name']}"


async def _mall_dm_ok(context, cid, uid, idx):
    """私聊「是否兑换 → 确认」：商城商品二次校验后执行购买（与群内购买同口径：库存/门槛/扣款/台账/管理员）。"""
    if not is_auth(cid):
        return False, "❌ 该群未授权使用本机器人。"
    if not sget("MALL_ENABLED"):
        return False, "ℹ️ 积分商城未开启。"
    items = _mall_items_on()
    if not (1 <= idx <= len(items)):
        return False, "❌ 商品不存在或已下架，请回群重新打开列表。"
    item = items[idx - 1]
    stk = item.get("stock")
    if isinstance(stk, int) and stk <= 0:
        return False, "❌ 该商品已售罄。"
    price = _mall_price(item)
    if sget("MALL_MIN_AGE_DAYS") > 0:  # 兑换门槛1：与 bot 首次互动满 N 天
        seen = user_first_seen.get(uid)
        days = (now_bj().timestamp() - seen) / 86400 if seen else 0.0
        if days < sget("MALL_MIN_AGE_DAYS"):
            return False, f"❌ 兑换门槛：使用满 {sget('MALL_MIN_AGE_DAYS')} 天才能兑换（当前 {days:.0f} 天）。"
    if sget("MALL_MIN_ACTIVE_DAYS") > 0:  # 兑换门槛2：有游戏盈亏记录的天数 ≥N
        active_days = set()
        for prof in (poker_profit_by_date, race_profit_by_date, blackjack_profit_by_date, jinhua_profit_by_date):
            for d, chats in prof.items():
                if uid in (chats.get(cid) or {}): active_days.add(d)
        if len(active_days) < sget("MALL_MIN_ACTIVE_DAYS"):
            return False, f"❌ 兑换门槛：累计 {sget('MALL_MIN_ACTIVE_DAYS')} 天参与游戏才能兑换（当前 {len(active_days)} 天）。"
    async with wallet_locks[uid]:
        if game_chips[cid][uid] < price:
            return False, f"❌ 积分不足：需要 {price}，当前 {game_chips[cid][uid]}。"
        game_chips[cid][uid] -= price
        if isinstance(stk, int):
            item["stock"] = stk - 1
        mall_orders.append({"ts": now_bj().strftime("%Y-%m-%d %H:%M"), "cid": cid, "uid": uid,
                            "name": await get_name(context.application, uid), "item": item["name"], "price": price})
        save_data()
    await send_settle(context.application, cid, _fmt_tpl("mall_msg_buy",
        name=await get_name(context.application, uid), item=item["name"], price=price, balance=game_chips[cid][uid]))
    # 消费点不再检查等级：等级按「累计获得」算，花分不掉级（此前误传余额 → 花分即降级公告）
    try:
        await context.bot.send_message(ADMIN_USER_ID,
            f"🛒 积分商城订单\n群：{chat_name_cache.get(cid, cid)}\n"
            f"玩家：{await get_name(context.application, uid)}（{uid}）\n商品：{item['name']}（{price} 积分）")
    except Exception:
        logger.exception("商城订单通知管理员失败")
    return True, f"🎉 兑换成功：{item['name']}"


def _parse_dm_redeem_data(data):
    """私聊确认回调数据 redeem_ok_<cid>_<idx> / redeem_no_<cid>_<idx> / mall_*。
    返回 (kind, action, cid, idx)；cid 为负数时整段不含下划线，可直接按 '_' 切。"""
    try:
        kind, action, cid_s, idx_s = data.split("_", 3)
        return kind, action, int(cid_s), int(idx_s)
    except (ValueError, AttributeError):
        return None, None, None, None


async def _deep_start_confirm(q, data, context):
    """群内点「立即兑换」蓝色文字 → 跳转 bot 私聊 → 机器人显示 是否兑换/积分不足。
    本函数处理私聊里确认/取消按钮回调（callback_data=redeem_ok_*/redeem_no_*/mall_*/sexch_*）。"""
    kind, action, cid, idx = _parse_dm_redeem_data(data)
    uid = q.from_user.id
    if kind not in ("redeem", "mall", "sexch") or action not in ("ok", "no") or cid is None:
        await q.answer("无效操作", show_alert=True); return
    if uid in BLACKLISTED_USERS and not is_bot_admin(uid):
        await q.answer("🚫 你已被禁止使用本机器人", show_alert=True); return
    if action == "no":
        try: await q.message.edit_text("🚫 已取消兑换。")
        except Exception: pass
        await q.answer("已取消"); return
    if kind == "redeem":
        ok, txt = await _redeem_dm_ok(context, cid, uid, idx)
    elif kind == "mall":
        ok, txt = await _mall_dm_ok(context, cid, uid, idx)
    else:
        # sexch：idx 段承载的是「消耗的聊天积分」
        ok, txt = await _season_exchange_execute(context, cid, uid, idx)
    try:
        await q.message.edit_text(txt)
    except Exception:
        pass
    await q.answer(txt if not ok else "🎉 兑换成功！", show_alert=not ok)


async def _deep_redeem_start(update, context, payload):
    """私聊里收到 /start redeem_<cid>_<idx>：按竞品流程显示 是否兑换 / 积分不足。"""
    if not update.effective_chat or update.effective_chat.type != "private":
        await send_reply(update, context, "⚠️ 请到机器人私聊完成兑换确认。"); return
    try:
        _, cid_s, idx_s = payload.split("_", 2)
        cid, idx = int(cid_s), int(idx_s)
    except (ValueError, AttributeError):
        await send_reply(update, context, "❌ 兑换链接无效，请回群重新打开列表。"); return
    uid = update.effective_user.id
    if not is_auth(cid):
        await send_reply(update, context, "❌ 该群未授权使用本机器人。"); return
    items = _redeem_items_for(cid)
    if not items:
        await send_reply(update, context, "🎁 本群暂无可兑换商品。"); return
    if not (1 <= idx <= len(items)):
        await send_reply(update, context, "❌ 商品不存在或已下架，请回群重新打开列表。"); return
    item = items[idx - 1]
    price = int(item.get("price", 0) or 0)
    bal = game_chips[cid][uid]
    if bal < price:
        await send_reply(update, context, f"❌ 积分不足：需要 {price}，当前 {bal}。\n去群聊赢积分后再来兑换吧～")
        return
    left = int(item.get("left", 0) or 0)
    kb = InlineKeyboardMarkup([[
        InlineKeyboardButton("✅ 确认兑换", callback_data=f"redeem_ok_{cid}_{idx}"),
        InlineKeyboardButton("❌ 取消兑换", callback_data=f"redeem_no_{cid}_{idx}"),
    ]])
    # 逐行字段 + 等长按钮：手机端两个按钮宽度才一致（用户 2026-09-10 截图报「文本和按钮没对齐」）
    txt = (f"🎁 <b>{item['name']}</b>\n"
           f"━━━━━━━━━━━━━━━\n"
           f"价格：{price} 积分\n"
           f"剩余：{'不限' if left <= 0 else left}\n"
           f"当前积分：{bal}\n"
           f"━━━━━━━━━━━━━━━\n"
           f"是否兑换？")
    # 确认弹窗不清除（等用户点确认/取消后再编辑）；不走 REPLY_DELETE_SECONDS
    await send_reply(update, context, txt, kb=kb, parse_mode="HTML", delete_after=0)


async def _deep_mall_start(update, context, payload):
    """私聊里收到 /start mall_<cid>_<idx>：商城商品显示 是否兑换 / 积分不足。"""
    if not update.effective_chat or update.effective_chat.type != "private":
        await send_reply(update, context, "⚠️ 请到机器人私聊完成兑换确认。"); return
    try:
        _, cid_s, idx_s = payload.split("_", 2)
        cid, idx = int(cid_s), int(idx_s)
    except (ValueError, AttributeError):
        await send_reply(update, context, "❌ 兑换链接无效，请回群重新打开列表。"); return
    uid = update.effective_user.id
    if not is_auth(cid):
        await send_reply(update, context, "❌ 该群未授权使用本机器人。"); return
    if not sget("MALL_ENABLED"):
        await send_reply(update, context, "ℹ️ 积分商城未开启。"); return
    items = _mall_items_on()
    if not (1 <= idx <= len(items)):
        await send_reply(update, context, "❌ 商品不存在或已下架，请回群重新打开列表。"); return
    item = items[idx - 1]
    stk = item.get("stock")
    if isinstance(stk, int) and stk <= 0:
        await send_reply(update, context, "❌ 该商品已售罄。"); return
    price = _mall_price(item)
    bal = game_chips[cid][uid]
    if bal < price:
        await send_reply(update, context, f"❌ 积分不足：需要 {price}，当前 {bal}。\n去群聊赢积分后再来兑换吧～")
        return
    kb = InlineKeyboardMarkup([[
        InlineKeyboardButton("✅ 确认兑换", callback_data=f"mall_ok_{cid}_{idx}"),
        InlineKeyboardButton("❌ 取消兑换", callback_data=f"mall_no_{cid}_{idx}"),
    ]])
    # 逐行字段 + 等长按钮：与积分兑换确认卡同款（手机端按钮宽度一致）
    txt = (f"🛒 <b>{item['name']}</b>\n"
           f"━━━━━━━━━━━━━━━\n"
           f"价格：{price} 积分\n"
           f"当前积分：{bal}\n"
           f"━━━━━━━━━━━━━━━\n"
           f"是否兑换？")
    # 确认弹窗不清除（等用户点确认/取消后再编辑）；不走 REPLY_DELETE_SECONDS
    await send_reply(update, context, txt, kb=kb, parse_mode="HTML", delete_after=0)


async def _deep_season_exchange_start(update, context, payload):
    """私聊里收到 /start sexch_<cid>_<cost>：显示「是否兑换 / 积分不足」确认卡片。
    与兑换/商城同一套竞品式流程；真正扣款仍走 _season_exchange_execute（唯一入口）。"""
    if not update.effective_chat or update.effective_chat.type != "private":
        await send_reply(update, context, "⚠️ 请到机器人私聊完成兑换确认。"); return
    try:
        _, cid_s, cost_s = payload.split("_", 2)
        cid, cost = int(cid_s), int(cost_s)
    except (ValueError, AttributeError):
        await send_reply(update, context, "❌ 兑换链接无效，请回群重新打开面板。"); return
    uid = update.effective_user.id
    if not is_auth(cid):
        await send_reply(update, context, "❌ 该群未授权使用本机器人。"); return
    if not sget("RANKED_EXCHANGE_ENABLED"):
        await send_reply(update, context, "❌ 积分兑换排位分功能未开启（管理员可在后台「排位赛」分组开启）。"); return
    unit_c = max(1, sget("RANKED_EXCHANGE_COST"))
    if cost < unit_c:
        await send_reply(update, context, f"❌ 最少兑换 {unit_c} 积分（当前比例 {_exchange_rate_text()}）。"); return
    gain = cost * sget("RANKED_EXCHANGE_GAIN") // unit_c
    if gain <= 0:
        await send_reply(update, context, f"❌ 兑换数量太小，至少能得到 1 排位分（比例 {_exchange_rate_text()}）。"); return
    bal = game_chips[cid][uid]
    if bal < cost:
        await send_reply(update, context,
                         f"❌ 聊天积分不足：需要 {cost}，当前 {bal}。\n去群聊赢积分后再来兑换吧～")
        return
    if sget("RANKED_EXCHANGE_DAILY_LIMIT") > 0:
        used = season_exchange_daily[business_date()][cid].get(uid, 0)
        if used + cost > sget("RANKED_EXCHANGE_DAILY_LIMIT"):
            await send_reply(update, context,
                             f"❌ 超出每日兑换上限：今日已兑换 {used} 积分，"
                             f"上限 {sget('RANKED_EXCHANGE_DAILY_LIMIT')}（管理员可在后台调整）。")
            return
    kb = InlineKeyboardMarkup([[
        InlineKeyboardButton("✅ 确认兑换", callback_data=f"sexch_ok_{cid}_{cost}"),
        InlineKeyboardButton("❌ 取消兑换", callback_data=f"sexch_no_{cid}_{cost}"),
    ]])
    txt = (f"🏆 <b>积分兑换排位分</b>\n"
           f"━━━━━━━━━━━━━━━\n"
           f"消耗：{cost} 聊天积分\n"
           f"获得：{gain} 排位分\n"
           f"当前积分：{bal}\n"
           f"当前排位分：{season_points[cid][uid]}\n"
           f"━━━━━━━━━━━━━━━\n"
           f"是否兑换？")
    await send_reply(update, context, txt, kb=kb, parse_mode="HTML", delete_after=0)


async def cmd_points_redeem(update, context):
    """积分兑换（阿福式活动）：发触发词看商品按钮列表，点蓝色按钮立即兑换；
    仍支持「触发词 编号/名称」。剩余 0=不限；限量兑完自动下架；支持起止时间与每人限购。"""
    if not await need_auth(update, context): return
    if not is_group_chat(update):
        await send_reply(update, context, "⚠️ 积分兑换请在群聊中使用。"); return
    cid, uid = update.effective_chat.id, update.effective_user.id
    gate = _redeem_gate()
    if gate:
        await send_reply(update, context, gate); return
    items = [x for x in redeem_goods if x.get("on", True)
             and (not x.get("target_groups") or cid in x["target_groups"])]
    if not items:
        await send_reply(update, context, "🎁 本群暂无可兑换商品，管理员可在后台「积分系统 → 积分兑换」给本群上架。"); return
    args = context.args or []
    if not args:  # 货架卡：正文逐商品小卡 + 行内蓝色「立即兑换」文本超链接（点蓝字跳私聊确认）
        lines = ["🎁 <b>积分兑换</b>", ""]
        rows = []
        for i, x in enumerate(items, 1):
            price = int(x.get("price", 0) or 0)
            left = int(x.get("left", 0) or 0)
            left_txt = "不限" if left <= 0 else str(left)
            lines.append(f"🟡 <b>{html.escape(x['name'])}</b>")
            desc = str(x.get("desc", "") or "").strip()
            if desc and len(desc) <= 60:
                lines.append(f"<i>{html.escape(desc)}</i>")
            meta = f"{price} 积分 剩余 {left_txt}"
            url = _deep_buy_url("redeem", cid, i)
            if url:
                lines.append(f"└ {meta} <a href='{html.escape(url, quote=True)}'>立即兑换</a>")
            else:
                # 启动早期/无 bot 用户名 → 没有可用深链，退回底部按钮直兑
                lines.append(f"└ {meta}")
                rows.append([InlineKeyboardButton(f"{i}. 立即兑换", callback_data=f"redeem_buy_{i}")])
            lines.append("")
        msg = await safe_send(context.bot, cid, "\n".join(lines),
                              reply_markup=(InlineKeyboardMarkup(rows) if rows else None))
        if msg and MALL_LIST_DELETE_SECONDS > 0:
            schedule_delete(context.application, cid, msg, MALL_LIST_DELETE_SECONDS)
        return
    arg = args[0].strip()
    item = None
    if arg.isdigit() and 1 <= int(arg) <= len(items):
        item = items[int(arg) - 1]
    else:
        item = next((x for x in items if x["name"] == arg), None)
    if not item:
        await send_reply(update, context, f"❌ 没有这个商品，发「{REDEEM_CMD}」查看列表。"); return
    err = await _redeem_execute(context, cid, uid, item)
    if err:
        await send_reply(update, context, err)

def _mall_panel(page, items, cid):
    """商城货架卡：正文逐商品小卡 + 行内蓝色「立即兑换」文本超链接（售罄置灰）。
    返回 (text, rows)；cmd_mall 首屏与 mall_page_ 翻页共用，保证样式一致。

    样式对齐用户 2026-09-10 指定截图：商品名 + 「└ 价格 积分 剩余 N 立即兑换(蓝字)」，
    底部「第 x/y 页」；不再每商品占一行按钮（按钮只留翻页）。
    """
    pages = max(1, (len(items) + sget("MALL_PAGE_SIZE") - 1) // sget("MALL_PAGE_SIZE"))
    page = max(1, min(page, pages))
    chunk = items[(page - 1) * sget("MALL_PAGE_SIZE"): page * sget("MALL_PAGE_SIZE")]
    lines = ["🛒 <b>积分商城</b>", ""]
    rows = []
    for i, item in enumerate(chunk, (page - 1) * sget("MALL_PAGE_SIZE") + 1):
        stk = item.get("stock")
        sold_out = isinstance(stk, int) and stk <= 0
        left_txt = "不限" if not isinstance(stk, int) else str(stk)
        lines.append(f"🟡 <b>{html.escape(item['name'])}</b>")
        meta = f"{_mall_price(item)} 积分 剩余 {left_txt}"
        url = _deep_buy_url("mall", cid, i)
        if sold_out:
            lines.append(f"└ {meta} <s>已售罄</s>")
        elif url:
            lines.append(f"└ {meta} <a href='{html.escape(url, quote=True)}'>立即兑换</a>")
        else:
            # 启动早期/无 bot 用户名 → 没有可用深链，退回底部按钮直兑
            lines.append(f"└ {meta}")
            rows.append([InlineKeyboardButton(f"{i}. 立即兑换", callback_data=f"mall_buy_{i}")])
        lines.append("")
    lines.append(f"第 {page}/{pages} 页")
    nav = []
    if page > 1:
        nav.append(InlineKeyboardButton("⬅ 上一页", callback_data=f"mall_page_{page-1}"))
    if pages > 1:
        nav.append(InlineKeyboardButton(f"📄 {page}/{pages}", callback_data="noop"))
    if page < pages:
        nav.append(InlineKeyboardButton("➡ 下一页", callback_data=f"mall_page_{page+1}"))
    if nav:
        rows.append(nav)
    return "\n".join(lines), rows


async def cmd_mall(update, context):
    if not await need_auth(update, context): return
    if not sget("MALL_ENABLED"):
        await send_reply(update, context, "ℹ️ 积分商城未开启。"); return
    items = [x for x in sget("MALL_ITEMS") if x.get("on", True)]
    if not items:
        await send_reply(update, context, _fmt_tpl("mall_msg_empty")); return
    cid = update.effective_chat.id
    page = 1
    if context.args and context.args[0].isdigit():
        page = max(1, int(context.args[0]))
    text, rows = _mall_panel(page, items, cid)
    kb = InlineKeyboardMarkup(rows) if rows else None
    await send_reply(update, context, text, kb=kb, delete_after=MALL_LIST_DELETE_SECONDS)

async def cmd_mall_buy(update, context):
    if not await need_auth(update, context): return
    if not is_group_chat(update):
        await send_reply(update, context, "⚠️ 购买请在群聊中进行。"); return
    if not sget("MALL_ENABLED"):
        await send_reply(update, context, "ℹ️ 积分商城未开启。"); return
    items = [x for x in sget("MALL_ITEMS") if x.get("on", True)]
    if not items:
        await send_reply(update, context, _fmt_tpl("mall_msg_empty")); return
    if not context.args:
        await send_reply(update, context, f"用法：购买 编号（1~{len(items)}），用「积分商城」查看列表。"); return
    arg = context.args[0].strip()
    item = None
    if arg.isdigit() and 1 <= int(arg) <= len(items):
        item = items[int(arg) - 1]
    else:
        name = arg.lstrip("0123456789.、 ").strip()
        item = next((x for x in items if x["name"] == name), None)
    if not item:
        await send_reply(update, context, "❌ 没有这个商品，用「积分商城」查看列表。"); return
    stk = item.get("stock")
    if isinstance(stk, int) and stk <= 0:
        await send_reply(update, context, "❌ 该商品已售罄。"); return
    cid, uid = update.effective_chat.id, update.effective_user.id
    price = _mall_price(item)
    if sget("MALL_MIN_AGE_DAYS") > 0:  # 兑换门槛1：与 bot 首次互动满 N 天（小号没有历史）
        seen = user_first_seen.get(uid)
        days = (now_bj().timestamp() - seen) / 86400 if seen else 0.0
        if days < sget("MALL_MIN_AGE_DAYS"):
            await send_reply(update, context, f"❌ 兑换门槛：使用满 {sget('MALL_MIN_AGE_DAYS')} 天才能兑换（当前 {days:.0f} 天）。"); return
    if sget("MALL_MIN_ACTIVE_DAYS") > 0:  # 兑换门槛2：有游戏盈亏记录的天数 ≥N
        active_days = set()
        for prof in (poker_profit_by_date, race_profit_by_date, blackjack_profit_by_date, jinhua_profit_by_date):
            for d, chats in prof.items():
                if uid in (chats.get(cid) or {}): active_days.add(d)
        if len(active_days) < sget("MALL_MIN_ACTIVE_DAYS"):
            await send_reply(update, context, f"❌ 兑换门槛：累计 {sget('MALL_MIN_ACTIVE_DAYS')} 天参与游戏才能兑换（当前 {len(active_days)} 天）。"); return
    async with wallet_locks[uid]:
        if game_chips[cid][uid] < price:
            await send_reply(update, context, f"❌ 积分不足：需要 {price}，当前 {game_chips[cid][uid]}。"); return
        game_chips[cid][uid] -= price
        if isinstance(stk, int):
            item["stock"] = stk - 1
        mall_orders.append({"ts": now_bj().strftime("%Y-%m-%d %H:%M"), "cid": cid, "uid": uid,
                            "name": await get_name(context.application, uid), "item": item["name"], "price": price})
        save_data()
    await send_reply(update, context, _fmt_tpl("mall_msg_buy",
        name=await get_name(context.application, uid), item=item["name"], price=price, balance=game_chips[cid][uid]))
    # 消费点不再检查等级：等级按「累计获得」算，花分不掉级（此前误传余额 → 花分即降级公告）
    try:
        await context.bot.send_message(ADMIN_USER_ID,
            f"🛒 积分商城订单\n群：{chat_name_cache.get(cid, cid)}\n"
            f"玩家：{await get_name(context.application, uid)}（{uid}）\n商品：{item['name']}（{price} 积分）")
    except Exception:
        logger.exception("商城订单通知管理员失败")

async def cmd_record(update, context):
    """个人战绩：本群四游戏累计盈亏汇总。用法：战绩 / 回复成员消息发「战绩」/「战绩 用户ID」。"""
    if not await need_auth(update, context): return
    if not is_group_chat(update):
        await send_reply(update, context, "⚠️ 战绩请在群聊中查看。"); return
    cid, uid = update.effective_chat.id, update.effective_user.id
    args = context.args or []
    reply = update.message.reply_to_message
    if reply is not None and reply.from_user and not reply.from_user.is_bot:
        target = reply.from_user.id
    elif args and args[0].lstrip("-").isdigit():
        target = int(args[0])
    else:
        target = uid
    per, days = {}, set()
    for label, prof in (("🃏 德州", poker_profit_by_date), ("🏎️ 赛车", race_profit_by_date),
                        ("♠️ 21点", blackjack_profit_by_date), ("♣️ 炸金花", jinhua_profit_by_date)):
        total = 0
        for d, chats in prof.items():
            v = (chats.get(cid) or {}).get(target)
            if v: total += v; days.add(d)
        per[label] = total
    balance = game_chips[cid].get(target, 0)
    name = await get_name(context.application, target, cid=cid)
    lines = [f"📊 {name} 的战绩（本群）", "━━━━━━━━━━━━"]
    for label, total in per.items():
        lines.append(f"{label}：{total:+d}")
    lines.append("━━━━━━━━━━━━")
    lines.append(f"💰 累计：{sum(per.values()):+d}")
    lines.append(f"📅 活跃 {len(days)} 天｜💳 当前余额 {balance}")
    reply_msg = await send_reply(update, context, "\n".join(lines))
    schedule_delete(context.application, cid, reply_msg, sget("REPLY_DELETE_SECONDS"))


async def cmd_webcode(update, context):
    """后台登录验证码（管理员）：bot 私聊推送失败时的备用取码通道。

    Telegram 不允许 bot 主动给「从未私聊过」的用户发消息，此时网页端拿不到码，
    用这条命令主动索取即可——命令是用户发起的，不受该限制。
    """
    if not is_bot_admin(update.effective_user.id):
        await send_reply(update, context, "❌ 仅机器人管理员可用。"); return
    now = time.time()
    alive = [(k, v) for k, v in web_pending_otp.items() if v["exp"] > now]
    if not alive:
        await send_reply(update, context, 
            "当前没有待验证的登录请求。\n\n"
            "用法：先在网页端输入密码 → 再回来发 /网页码 取验证码。")
        return
    _tok, rec = alive[-1]
    left = int(rec["exp"] - now)
    await send_reply(update, context, 
        f"🔐 <b>后台登录验证码</b>\n\n"
        f"验证码：<code>{rec['code']}</code>\n"
        f"来源 IP：<code>{rec['ip']}</code>\n"
        f"剩余有效：{left} 秒\n\n"
        f"⚠️ 不是你本人操作请立即改后台密码。",
        parse_mode="HTML")

# =============== 群组抽奖 ===============
def _lottery_render_prizes(prizes):
    """奖品列表渲染为多行：• 名称 × 数量"""
    return "\n".join(f"  • {html.escape(p['name'])} × {int(p['count'])}" for p in prizes)

def _lottery_parse_end(spec: str):
    """解析开奖时间字段：纯数字=秒数；'20:00'=今天(已过顺延明天)；'09-08 20:00'=今年(已过顺延明年)；
    '2026-09-08 20:00'=指定日期。均按北京时间。非法返回 None。"""
    s = (spec or "").strip().replace("：", ":")
    if not s:
        return None
    if s.isdigit():
        return time.time() + max(10, min(7 * 86400, int(s)))
    now = now_bj()
    for fmt in ("%Y-%m-%d %H:%M", "%Y-%m-%d %H:%M:%S", "%m-%d %H:%M", "%m-%d %H:%M:%S", "%H:%M"):
        try:
            t = datetime.strptime(s, fmt).replace(tzinfo=BEIJING_TZ)  # strptime 产出 naive，必须补时区才能与 now_bj 比较
        except ValueError:
            continue
        if fmt == "%H:%M":
            dt = now.replace(hour=t.hour, minute=t.minute, second=0, microsecond=0)
            if dt <= now:
                dt += timedelta(days=1)
        elif fmt.startswith("%m-%d"):
            dt = t.replace(year=now.year)
            if dt <= now:
                dt = dt.replace(year=now.year + 1)
        else:
            dt = t
        ts = dt.timestamp()
        return time.time() + 10 if ts < time.time() + 10 else ts  # 至少留 10 秒
    return None

def _lottery_form_parse(form):
    """网页创建抽奖表单（阿福格式）→ (fields, err)。

    fields: title/desc/keyword/prizes/min_bal/end_ts。
    奖品：结构化行 prize_name[] + prize_count[]（优先），无则回退旧 textarea prizes。
    开奖方式 mode：'time'=定时开奖（按北京时间解析 endtime）；'duration'=倒计时秒数。
    """
    title = (form.get("title", [""])[0] or "").strip()
    if not title or len(title) > 50:
        return None, "标题不能为空或超过 50 字"
    desc = (form.get("desc", [""])[0] or "").strip()[:300]
    keyword = (form.get("keyword", [""])[0] or "").strip() or sget("LOTTERY_KEYWORD")
    mode = form.get("mode", ["duration"])[0]
    min_bal_raw = (form.get("min_bal", [""])[0] or "").strip()
    if min_bal_raw:
        try:
            min_bal = max(0, int(min_bal_raw))
        except ValueError:
            return None, "参与门槛（最低积分）必须是数字"
    else:
        min_bal = 0   # 留空=不限制（门槛只跟活动走，不再有全局默认）
    # 奖品：结构化行优先，回退 textarea
    names = [x.strip() for x in form.get("prize_name", [])]
    if names:
        counts = [x.strip() for x in form.get("prize_count", [])]
        spec = ",".join(f"{n}:{(counts[i] if i < len(counts) and counts[i] else '1')}"
                        for i, n in enumerate(names) if n)
    else:
        spec = (form.get("prizes", [""])[0] or "").strip().replace("\r", "").replace("\n", ",")
    prizes, perr = _lottery_parse_prizes(spec)
    if perr:
        return None, perr
    if mode == "time":
        end_ts = _lottery_parse_end(form.get("endtime", [""])[0])
        if end_ts is None:
            return None, "开奖时间格式不对：支持 20:00 / 09-08 20:00 / 2026-09-08 20:00"
    else:
        dur_raw = (form.get("duration", [""])[0] or "").strip()
        try:
            duration = max(10, min(7 * 86400, int(dur_raw)))
        except ValueError:
            return None, "持续秒数必须是数字"
        end_ts = time.time() + duration
    return {"title": title, "desc": desc, "keyword": keyword, "prizes": prizes,
            "min_bal": min_bal, "end_ts": end_ts}, ""

def _lottery_parse_prizes(spec: str):
    """解析「奖品A:数量,奖品B:数量」；空 / 非法返回 ([], err)。"""
    if not spec:
        return [], "奖品不能为空"
    out, seen = [], set()
    for chunk in spec.replace("，", ",").split(","):
        chunk = chunk.strip()
        if not chunk:
            continue
        if ":" not in chunk:
            return [], f"奖品格式错误：{chunk}（应为 名称:数量）"
        name, _, cnt = chunk.partition(":")
        name = name.strip()
        cnt = cnt.strip()
        if not name:
            return [], f"奖品名称不能为空：{chunk}"
        try:
            n = int(cnt)
        except ValueError:
            return [], f"奖品数量必须是数字：{chunk}"
        if n <= 0:
            return [], f"奖品数量必须 >0：{chunk}"
        if name in seen:
            return [], f"重复奖品：{name}"
        seen.add(name)
        out.append({"name": name, "count": n})
    if not out:
        return [], "奖品不能为空"
    if len(out) > LOTTERY_MAX_PRIZES:
        return [], f"奖品最多 {LOTTERY_MAX_PRIZES} 档"
    return out, ""

def _lottery_active(cid):
    """返回进行中的活动；不存在或已结束返回 None。"""
    lo = lotteries.get(cid)
    if not lo or lo.get("status") != "open":
        return None
    return lo

def _lottery_join(lo, uid, name):
    """加入参与者；返回 (ok, reason_or_index)。已加入返回 (False, 'dup')。"""
    for i, (u, _, _) in enumerate(lo["participants"]):
        if u == uid:
            return False, "dup"
    lo["participants"].append((uid, time.time(), name))
    return True, len(lo["participants"])

async def _lottery_publish(app, cid, lo):
    """编辑/发送活动公告消息；记录 msg_id 用于开奖后编辑。"""
    if not sget("LOTTERY_ENABLED"): return
    msg = await safe_send(app.bot, cid, _lottery_announce_text(lo), parse_mode="HTML")
    if msg:
        lo["msg_id"] = msg.message_id

def _lottery_announce_text(lo):
    """公告文案：横幅版式 + 实时参与人数。"""
    end_line = (datetime.fromtimestamp(lo["end_ts"], BEIJING_TZ).strftime("%m-%d %H:%M")
                + f"（还剩 {max(0, int(lo['end_ts'] - time.time()) // 60)} 分"
                  f"{max(0, int(lo['end_ts'] - time.time())) % 60} 秒）")
    fee_line = f"💰 参与扣 <b>{lo['fee']}</b> 积分\n" if lo["fee"] else ""
    mb = lo.get("min_bal")
    min_bal = int(mb or 0)   # 门槛只跟活动走：留空/0=不限，N=门槛N
    min_line = f"门槛：<b>{min_bal}</b> 积分以上可参与\n" if min_bal else ""
    desc = (lo.get("desc") or "").strip()
    desc_line = f"📖 {html.escape(desc)}\n" if desc else ""
    return sget("LOTTERY_MSG_START").format(
        title=html.escape(lo["title"]),
        desc_line=desc_line,
        end_line=end_line,
        duration=int(lo["end_ts"] - lo["start_ts"]),
        prize_list=_lottery_render_prizes(lo["prizes"]),
        min_line=min_line,
        fee_line=fee_line,
        keyword=html.escape(lo["keyword"]),
        n=len(lo.get("participants", [])),
    )

async def _lottery_refresh_announce(app, cid, lo):
    """有人参与后刷新公告上的已参与人数（编辑失败静默，不影响参与流程）。"""
    if not lo.get("msg_id"):
        return
    try:
        await app.bot.edit_message_text(chat_id=cid, message_id=lo["msg_id"],
                                        text=_lottery_announce_text(lo), parse_mode="HTML")
    except Exception:
        pass

async def _lottery_draw(app, cid, lo):
    """开奖：从参与者中按奖品库存随机抽；写回 lo['winners']/prizes 剩余库存；发群通知 + 私聊中奖者。

    返回 True=本次实际开奖；False=活动已不在 open 状态（防定时扫描与手动开奖并发重复开奖、覆盖中奖名单）。
    """
    if lo.get("status") != "open":
        return False
    lo["status"] = "drawing"
    prizes = [dict(p) for p in lo["prizes"]]  # 拷贝并加 left 字段
    for p in prizes:
        p["left"] = int(p["count"])
    pool = list(lo["participants"])
    winners = []
    # 总中奖数 ≤ 总奖品数 且 ≤ 参与人数
    while pool and any(p["left"] > 0 for p in prizes):
        # 选一个仍有库存的奖品
        avail = [p for p in prizes if p["left"] > 0]
        if not avail: break
        prize = random.choice(avail)
        # 选一个参与者
        idx = random.randrange(len(pool))
        uid, _ts, name = pool.pop(idx)
        winners.append({"uid": uid, "name": name, "prize": prize["name"]})
        prize["left"] -= 1
    lo["prizes"] = prizes
    lo["winners"] = winners
    # 群内通知：结果单独发一条醒目消息（绝不自动删除，永久保留在群里）
    if winners:
        win_lines = [f"  🏆 <b>{html.escape(w['name'])}</b> → {html.escape(w['prize'])}" for w in winners]
        text = sget("LOTTERY_MSG_RESULT").format(
            title=html.escape(lo["title"]),
            winners="\n".join(win_lines),
            n=len(lo["participants"]),
            w=len(winners),
        )
    else:
        text = ("🎊━━━━━━━━━━━━━━━━━\n"
                f"🎉 <b>{html.escape(lo['title'])}</b> · 开奖结果\n"
                "🎊━━━━━━━━━━━━━━━━━\n"
                "😢 本轮无人中奖（参与人数不足）\n"
                f"📊 共 <b>{len(lo['participants'])}</b> 人参与")
    # 原公告编辑为已开奖状态（原文不再覆盖成结果——结果要独立醒目公布）
    done_line = f"🎊 <b>{html.escape(lo['title'])}</b> 已开奖 ✅ 结果见下方开奖公告"
    try:
        if lo.get("msg_id"):
            await app.bot.edit_message_text(chat_id=cid, message_id=lo["msg_id"],
                                            text=done_line, parse_mode="HTML")
    except Exception:
        logger.exception("编辑公告为已开奖状态失败（忽略）")
    result_msg = await safe_send(app.bot, cid, text, parse_mode="HTML")
    if not result_msg:
        # 编辑路径已废弃，新消息也失败则退回编辑公告兜底
        try:
            if lo.get("msg_id"):
                await app.bot.edit_message_text(chat_id=cid, message_id=lo["msg_id"],
                                                text=text, parse_mode="HTML")
        except Exception:
            logger.exception("开奖结果兜底编辑也失败")
    # 中奖信息推送一份给管理员私聊（与群内同文，永久保留）
    try:
        await app.bot.send_message(ADMIN_USER_ID, "📬 抽奖开奖推送\n\n" + text, parse_mode="HTML")
    except Exception:
        logger.exception("开奖结果推送管理员失败（忽略）")
    # 私聊中奖者
    for w in winners:
        try:
            await app.bot.send_message(chat_id=w["uid"],
                text=f"🎉 恭喜！你中奖了：<b>{html.escape(w['prize'])}</b>\n来自活动：{html.escape(lo['title'])}",
                parse_mode="HTML")
        except Exception:
            pass  # 对方没私聊过 bot 也没关系
    lo["status"] = "finished"
    lo["end_ts"] = time.time()
    save_data()
    return True

async def cmd_lottery(update, context):
    """群组抽奖：管理员用 /开奖 <标题> | <奖品> | <秒数> 开局；玩家用 /开奖 或 关键词 参与。

    用法：
      /开奖                              → 若活动进行中视为参与；否则帮助
      /开奖 <标题> | <奖品> | <秒数>      → 管理员开新活动
      /开奖开奖                           → 管理员手动立即开奖
      /开奖结束                           → 管理员强制结束并退款（按需）
    """
    if not await need_auth(update, context): return
    if not sget("LOTTERY_ENABLED"):
        await send_reply(update, context, "❌ 群组抽奖已关闭（后台「积分系统→群组抽奖」可开启）"); return
    cid = update.effective_chat.id
    uid = update.effective_user.id
    text = (update.message.text or "").strip()
    # 参与形态：/开奖、/抽奖、全局触发词、或本活动自定义关键词；其余原样交给开局参数
    _alo = _lottery_active(cid)
    _join_words = {sget("LOTTERY_KEYWORD"), "抽奖", (_alo.get("keyword") or "").strip() if _alo else ""}
    if text.startswith("/开奖"):
        args_part = text[len("/开奖"):].strip()
    elif text in _join_words:
        args_part = ""
    else:
        args_part = text
    # 管理员子命令
    if is_bot_admin(uid):
        if args_part in ("开奖", "开奖开奖", "开", "开奖", "开奖开奖"):
            lo = _lottery_active(cid)
            if not lo:
                await send_reply(update, context, "❌ 当前没有进行中的抽奖活动"); return
            await send_reply(update, context, "🎲 正在开奖…")
            if not await _lottery_draw(context.application, cid, lo):
                await send_reply(update, context, "ℹ️ 本活动已开奖/已结束，请勿重复操作")
            return
        if args_part in ("结束", "取消"):
            lo = _lottery_active(cid)
            if not lo:
                await send_reply(update, context, "❌ 当前没有进行中的抽奖活动"); return
            # 退积分（若有扣费）
            if lo["fee"] > 0:
                for u, _, _ in lo["participants"]:
                    game_chips[cid][u] = game_chips[cid].get(u, 0) + lo["fee"]
            lo["status"] = "cancelled"
            save_data()
            await safe_send(context.application.bot, cid,
                f"🛑 抽奖活动「<b>{html.escape(lo['title'])}</b>」已被管理员取消" + (
                    f"，已退还 {lo['fee']} 积分/人" if lo["fee"] else ""))
            return
    # 玩家参与
    if not args_part:
        lo = _lottery_active(cid)
        if not lo:
            await send_reply(update, context, 
                "❌ 当前没有进行中的抽奖\n\n"
                "管理员开局：<code>/开奖 标题 | 奖品A:数量,奖品B:数量 | 秒数或时间</code>",
                parse_mode="HTML")
            return
        ok, info = await _lottery_try_join(context.application, lo, uid, cid)
        if ok:
            name = await get_name(context.application, uid)
            bal = game_chips.get(cid, {}).get(uid, 0)
            await send_reply(update, context, 
                sget("LOTTERY_MSG_JOINED").format(nick=html.escape(name), n=info, balance=bal),
                parse_mode="HTML")
            # 公告上的已参与人数实时刷新
            await _lottery_refresh_announce(context.application, cid, lo)
        elif info == "dup":
            name = await get_name(context.application, uid)
            await send_reply(update, context, sget("LOTTERY_MSG_DUP").format(nick=html.escape(name)))
        else:
            name = await get_name(context.application, uid)
            await send_reply(update, context, sget("LOTTERY_MSG_FAIL").format(nick=html.escape(name), reason=info))
        return
    # 管理员开新活动
    if not is_bot_admin(uid):
        await send_reply(update, context, "❌ 仅管理员可以开局"); return
    if _lottery_active(cid):
        await send_reply(update, context, "⚠️ 当前群已有进行中的抽奖，请先 /开奖开奖 或 /开奖结束"); return
    # 解析 "标题 | 奖品 | 秒数"（秒数可选，奖品必填）
    parts = [p.strip() for p in args_part.split("|")]
    title = parts[0]
    if not title or len(title) > 50:
        await send_reply(update, context, "❌ 标题不能为空或超过 50 字"); return
    if len(parts) < 2:
        await send_reply(update, context, 
            "用法：\n"
            "<code>/开奖 标题 | 奖品A:数量,奖品B:数量 | 秒数或开奖时间</code>\n\n"
            "示例：\n"
            "<code>/开奖 群友福利 | 100积分:1,小星星:5 | 60</code>（60 秒后开）\n"
            "<code>/开奖 群友福利 | 100积分:1 | 20:00</code>（今晚 8 点开）\n"
            "<code>/开奖 群友福利 | 100积分:1 | 09-08 20:00</code>（指定日期）",
            parse_mode="HTML"); return
    prizes, perr = _lottery_parse_prizes(parts[1])
    if perr:
        await send_reply(update, context, f"❌ {perr}"); return
    # 第三段：纯数字=秒数倒计时；或指定开奖时间（20:00 / 09-08 20:00 / 2026-09-08 20:00）
    end_ts = None
    if len(parts) >= 3 and parts[2]:
        end_ts = _lottery_parse_end(parts[2])
        if end_ts is None:
            await send_reply(update, context, 
                "❌ 开奖时间格式不对\n\n支持：<code>90</code>（90秒后）、<code>20:00</code>、"
                "<code>09-08 20:00</code>、<code>2026-09-08 20:00</code>",
                parse_mode="HTML"); return
    duration = max(10, int(end_ts - time.time())) if end_ts else sget("LOTTERY_DEFAULT_DURATION")
    lotteries[cid] = {
        "title": title, "prizes": prizes, "fee": int(sget("LOTTERY_FEE")),
        "keyword": sget("LOTTERY_KEYWORD"), "start_ts": time.time(),
        "end_ts": end_ts or (time.time() + duration), "msg_id": None,
        "participants": [], "status": "open", "winners": [],
        "creator": uid, "chat_id": cid,
    }
    save_data()
    await _lottery_publish(context.application, cid, lotteries[cid])

async def _lottery_try_join(app, lo, uid, cid):
    """尝试加入抽奖：扣积分（若需）、检查门槛。返回 (ok, info_or_err_msg)。"""
    if not lo or lo.get("status") != "open":
        return False, "活动已结束"
    if time.time() >= lo["end_ts"]:
        return False, "活动已结束"
    balance = game_chips.get(cid, {}).get(uid, 0)
    min_bal = int(lo.get("min_bal") or 0)   # 门槛只跟活动走：留空/0=不限，N=门槛N
    if min_bal > 0 and balance < min_bal:
        return False, f"余额不足 {min_bal}，无法参与"
    fee = int(lo.get("fee", 0))
    if fee > 0 and balance < fee:
        return False, f"余额不足（需 {fee}）"
    if fee > 0:
        game_chips[cid][uid] = balance - fee
    ok, info = _lottery_join(lo, uid, user_names.get(uid, str(uid)))
    if not ok:
        # 重复参与：退还已扣（按理说前面不会走到这，但保险）
        if fee > 0:
            game_chips[cid][uid] = game_chips[cid].get(uid, 0) + fee
        return False, "dup"
    save_data()
    return True, info

async def lottery_scheduler(app):
    """每 5 秒扫一遍所有群的超时活动，到点自动开奖。"""
    while True:
        try:
            now = time.time()
            for cid, lo in list(lotteries.items()):
                if lo.get("status") != "open": continue
                if now < lo["end_ts"]: continue
                await _lottery_draw(app, cid, lo)
        except Exception:
            logger.exception("lottery_scheduler 本轮异常（已吞并继续）")
        await asyncio.sleep(5)

async def cmd_weblogin(update, context):
    """后台一键登录（管理员）：校验身份后私聊发一次性登录链接，点开即进后台，免密码免验证码。

    链接 2 分钟有效、单次使用；新链接会作废旧链接。需先在网页「通用与应急」
    配置「后台公网地址」（WEB_BASE_URL），否则 bot 不知道该拼什么域名。
    """
    uid = update.effective_user.id
    if not is_bot_admin(uid):
        await send_reply(update, context, "⛔ 仅机器人管理员可用")
        return
    base = (sget("WEB_BASE_URL") or "").strip().rstrip("/")
    if not base:
        await send_reply(update, context, 
            "⚠️ 还没配置后台地址，一键登录不可用。\n\n"
            "请先用密码登录网页后台 → 「通用与应急」→「后台公网地址」\n"
            "填你的后台访问地址（如 https://xxx.northflank.app），保存后再来。")
        return
    # 同一管理员旧 token 一律作废
    now = time.time()
    for k in [k for k, v in web_magic_tokens.items() if v["uid"] == uid or v["exp"] < now]:
        web_magic_tokens.pop(k, None)
    token = secrets.token_urlsafe(32)
    web_magic_tokens[token] = {"uid": uid, "exp": now + 120}
    url = f"{base}/magic?token={token}"
    try:
        await context.bot.send_message(chat_id=uid, text=(
            "🔐 <b>后台一键登录</b>\n\n"
            f"<a href='{url}'>👉 点这里直接登录</a>\n\n"
            "· 2 分钟内有效，仅可使用一次\n"
            "· 点开即进后台，无需密码\n"
            "· 不是你本人操作请忽略"),
            parse_mode="HTML", disable_web_page_preview=True)
        if update.effective_chat.id != uid:
            await send_reply(update, context, "✅ 登录链接已发到你的私聊（2 分钟内有效）")
    except Exception:
        await send_reply(update, context, 
            "⚠️ 链接发送失败（你可能从未私聊过本机器人）。\n"
            "请先私聊我发 /start，然后再发 /后台。")

async def cmd_status(update, context):
    """机器人自检（管理员）：运行时长/各游戏活跃局/台账/数据文件/调度任务。"""
    if not is_bot_admin(update.effective_user.id):
        await send_reply(update, context, "❌ 仅机器人管理员可用。"); return
    uptime = int(time.time() - BOT_BOOT_TS)
    uptime_txt = f"{uptime // 86400}天{uptime % 86400 // 3600}小时{uptime % 3600 // 60}分"
    try: dsz = f"{os.path.getsize(DATA_FILE) / 1024:.0f} KB"
    except OSError: dsz = "无"
    lines = [
        "🩺 机器人自检", "━━━━━━━━━━━━",
        f"⏱ 运行时长：{uptime_txt}",
        f"🃏 德州进行中：{len(active_poker_games)} 局",
        f"♠️ 21点进行中：{len(active_blackjack_games)} 局",
        f"♣️ 炸金花进行中：{len(active_jinhua_games)} 局",
        f"🏎️ 赛车进行中：{len(active_horse_races)} 场",
        f"🧧 未结算红包：{len(rp_packets)} 个",
        f"📒 资金流台账：{len(ledger)} 条",
        f"💾 数据文件：{dsz}｜后台任务：{len(background_tasks)} 个",
    ]
    await send_reply(update, context, "\n".join(lines))


async def cmd_redpacket(update, context):
    if not await need_auth(update, context): return
    if not sget("REDPACKET_ENABLED"):
        await send_reply(update, context, "ℹ️ 红包功能未开启。"); return
    if not is_group_chat(update):
        await send_reply(update, context, "⚠️ 红包请在群聊中发。"); return
    cid = update.effective_chat.id

    async def _reply(text):  # 机器人提示语也按后台设置自动删除
        reply = await send_reply(update, context, text)
        schedule_delete(context.application, cid, reply, sget("REPLY_DELETE_SECONDS"))

    args = context.args
    reply_to = update.message.reply_to_message
    target = 0  # 0=人人可抢；>0=专属红包仅 TA 可抢
    if reply_to is not None and reply_to.from_user and not reply_to.from_user.is_bot:
        target = reply_to.from_user.id
    elif len(args) >= 3 and args[2].lstrip("-").isdigit():
        target = int(args[2])
    if len(args) < 2 or not args[0].isdigit() or not args[1].isdigit():
        await _reply("用法：红包 总积分 份数（如：红包 1000 5）\n🎁 专属红包：回复某人消息发同样命令，或「红包 1000 5 用户ID」，仅 TA 能抢"); return
    total, count = int(args[0]), int(args[1])
    if not (1 <= total <= 1000000 and 2 <= count <= 100 and count <= total):
        await _reply("❌ 份数至少 2 份（防小号互刷），总积分 1~100 万且份数不超过总积分。"); return
    uid = update.effective_user.id
    if target == uid:
        await _reply("❌ 专属红包不能指定自己。"); return
    if target and not sget("RP_EXCLUSIVE_ENABLED"):
        await _reply("❌ 专属红包未开启（后台「积分系统 → 积分红包」可开启）。"); return
    async with wallet_locks[uid]:
        if game_chips[cid][uid] < total:
            await _reply(_fmt_tpl("rp_msg_poor", need=total, balance=game_chips[cid][uid])); return
        game_chips[cid][uid] -= total
        pid = secrets.token_urlsafe(8)
        rp_packets[pid] = {"cid": cid, "from": uid, "left_amt": total, "left_n": count,
                           "grabbed": {}, "ts": now_bj().timestamp(), "msg_id": None, "target": target,
                           "lock": asyncio.Lock()}  # 包级锁：检查+扣减必须原子，防并发双付
        save_data()
    await action_notice(cid, context.application, uid, f"发出了 {total} 积分 / {count} 份红包")
    who = f"\n🎯 仅 {await get_name(context.application, target, cid=cid)} 可抢" if target else ""
    msg = await safe_send(context.bot, cid,
        f"🧧 {await get_name(context.application, uid)} 的积分红包\n💰 {total} 积分 × {count} 份{who}\n点击下方按钮抢！",
        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🧧 抢红包", callback_data=f"rp_grab_{pid}")]]))
    if msg:
        rp_packets[pid]["msg_id"] = msg.message_id

async def _rp_grab(p, pid, uid, context, q):
    """红包抢夺核心：检查过期/重复 → 随机拆分 → 入账 → 更新看板。

    全程持包级锁：剩余份数/金额的检查与扣减必须原子，否则两个不同用户
    并发抢同一包时，各自持有的是不同的 wallet_locks[uid]，互不排斥 → 超额派发。
    """
    cid = p["cid"]
    async with p["lock"]:
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
            await q.answer(_fmt_tpl("rp_msg_dup", amount=p["grabbed"][uid]), show_alert=True); return
        tgt = p.get("target") or 0  # 旧数据无 target 键按普通红包处理
        if tgt and uid != tgt:
            await q.answer(_fmt_tpl("rp_msg_target", name=await get_name(context.application, tgt, cid=cid)), show_alert=True); return
        if p["left_n"] <= 0:
            await q.answer(_fmt_tpl("rp_msg_none"), show_alert=True); return
        if p["left_n"] == 1:
            amt = p["left_amt"]
        elif sget("RP_LUCK_ENABLED"):  # 拼手气：随机拆分；关闭则平均分
            amt = random.randint(1, max(1, p["left_amt"] - p["left_n"] + 1))
        else:
            amt = max(1, p["left_amt"] // p["left_n"])
        async with wallet_locks[uid]:
            p["grabbed"][uid] = amt
            p["left_amt"] -= amt; p["left_n"] -= 1
            game_chips[cid][uid] += amt
            # 红包是「人对人转移」不产生新积分 → 不写入 total_earned（防小号对倒刷等级）
            ledger_add(cid, p["from"], uid, amt, "红包")  # 资金流台账：发包人→领取人
            save_data()
    await q.answer(_fmt_tpl("rp_msg_grab", amount=amt, balance=game_chips[cid][uid]))
    # 等级只看真实产出，转移类不动 → 无需检查
    total, count = sum(p["grabbed"].values()), len(p["grabbed"])
    if p["left_n"] <= 0:
        if sget("RP_LOG_ENABLED"):  # 手气排行：按金额降序，前三名带奖牌表情
            lines = []
            for i, (u, a) in enumerate(sorted(p["grabbed"].items(), key=lambda x: -x[1]), 1):
                lines.append(_fmt_tpl("rp_msg_log", rank=rank_marker(i),
                                      name=await get_name(context.application, u, cid=cid), amount=a))
            detail = "\n".join(lines)
        else:
            detail = "\n".join(f"{await get_name(context.application, u, cid=cid)}：{a}"
                               for u, a in p["grabbed"].items())
        await safe_edit(context.bot, cid, p["msg_id"],
                        f"🧧 红包已被抢完（{count} 份 / {total} 积分）\n{detail}", reply_markup=None)
    else:
        await safe_edit(context.bot, cid, p["msg_id"],
                        f"🧧 红包进行中\n💰 已领 {count}/{p['left_n'] + count} 份｜剩 {p['left_amt']} 积分",
                        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🧧 抢红包", callback_data=f"rp_grab_{pid}")]]))


# ---------- 积分转赠 / 购买积分（统一钱包） ----------
async def cmd_inherit(update, context):
    """积分转赠（继承）：把积分转给同群其他成员，可收手续费。"""
    if not await need_auth(update, context): return
    if not is_group_chat(update):
        await send_reply(update, context, "⚠️ 转赠请在群聊中使用。"); return
    if not sget("INHERIT_ENABLED"):
        await send_reply(update, context, "❌ 转赠功能未开启（网页「积分系统 → 积分继承」可开启）。"); return
    cid, uid = update.effective_chat.id, update.effective_user.id
    args = context.args or []
    reply = update.message.reply_to_message
    if reply and args and args[0].isdigit():
        target, amount = reply.from_user.id, int(args[0])
    elif len(args) >= 2 and args[0].isdigit() and args[1].isdigit():
        target, amount = int(args[0]), int(args[1])
    else:
        await send_reply(update, context, "用法：回复成员消息发「转赠 数量」，或「转赠 用户ID 数量」"); return
    if amount <= 0:
        await send_reply(update, context, "❌ 转赠数量必须为正数。"); return
    if target == uid:
        await send_reply(update, context, "❌ 不能转给自己。"); return
    if player_is_busy(cid, uid) or player_is_busy(cid, target):
        await send_reply(update, context, "⚠️ 转赠双方有正在进行的游戏，请先结束。"); return
    fee = amount * sget("INHERIT_FEE_PERCENT") // 100
    recv = amount - fee
    if sget("INHERIT_DAILY_LIMIT") > 0:  # 每日转赠总额上限（防小号互刷）
        today = now_bj().strftime("%Y-%m-%d")
        used = inherit_daily[today][cid].get(uid, 0)
        if used + amount > sget("INHERIT_DAILY_LIMIT"):
            await send_reply(update, context, f"❌ 超出每日转赠上限：今日已转出 {used}，上限 {sget('INHERIT_DAILY_LIMIT')}（网页「积分继承」可调）。"); return
    # 必须同时锁住收款方：只锁付款方的话，收款方此刻若有 /add、结算等持锁写操作，转入会被覆盖丢失
    async with user_wallet_locks([uid, target]):
        if game_chips[cid][uid] < amount:
            await send_reply(update, context, f"❌ 你的积分不足：需要 {amount}，当前 {game_chips[cid][uid]}。"); return
        game_chips[cid][uid] -= amount
        game_chips[cid][target] += recv
        if sget("INHERIT_DAILY_LIMIT") > 0:
            inherit_daily[now_bj().strftime("%Y-%m-%d")][cid][uid] += amount
        ledger_add(cid, uid, target, amount, "转赠")  # 资金流台账
        save_data()
    fee_txt = f"（手续费 {fee}）" if fee else ""
    await send_reply(update, context, _fmt_tpl("inherit_msg_ok",
        name=await get_name(context.application, uid), target=await get_name(context.application, target, cid=cid),
        amount=amount, fee=fee_txt, recv=recv, balance=game_chips[cid][uid]))
    # 转赠是「人对人转移」，不产生新积分 → 不写入 total_earned（否则小号互转即可刷等级）
    # 因此这里不做等级变动检查：等级只看真实获得，不看分在谁手上。


# ---------- 积分竞猜：管理开局面两方下注，封盘后按比例瓜分奖池 ----------
def _guess_buttons(cid):
    g = guesses[cid]
    return InlineKeyboardMarkup([[InlineKeyboardButton(f"🔵 {g['a']} {amt}", callback_data=f"guessbet_A_{amt}"),
                                  InlineKeyboardButton(f"🔴 {g['b']} {amt}", callback_data=f"guessbet_B_{amt}")]
                                 for amt in sget("FIXED_BET_AMOUNTS")])


def _guess_text(cid):
    g = guesses[cid]
    ta, tb = g["side_pots"]["A"], g["side_pots"]["B"]
    pot = ta + tb
    od_a = f"{pot / ta:.2f}" if ta else "-"
    od_b = f"{pot / tb:.2f}" if tb else "-"
    if g.get("locked"):
        return (f"🎯 积分竞猜｜{g['q']}（已封盘）\n"
                f"🔵 {g['a']}｜池 {ta}\n🔴 {g['b']}｜池 {tb}\n"
                f"⏳ 下注已截止，等待管理员结算：群里发「竞猜结算 A/B」开出答案，「竞猜撤销」全额退款")
    return (f"🎯 积分竞猜｜{g['q']}\n"
            f"🔵 {g['a']}｜池 {ta}｜赔率约 {od_a}\n🔴 {g['b']}｜池 {tb}｜赔率约 {od_b}\n"
            f"⏱ 剩余 {max(0, int(g['end_ts'] - now_bj().timestamp()))} 秒｜点按钮下注，封盘后由猜中一方按注额比例瓜分全部奖池！")


async def _guess_bet(cid, uid, context, side, amount, q):
    """竞猜下注：立即扣分托管进奖池，封盘后拒绝。"""
    g = guesses.get(cid)
    if not g:
        await q.answer("竞猜已结束", show_alert=True); return
    if g.get("locked") or now_bj().timestamp() > g["end_ts"]:
        await q.answer("已封盘，等待结算", show_alert=True); return
    if side not in ("A", "B") or amount <= 0:
        await q.answer("无效下注", show_alert=True); return
    if amount < sget("GUESS_MIN_BET"):
        await q.answer(f"单注至少 {sget('GUESS_MIN_BET')} 积分", show_alert=True); return
    if sget("GUESS_MAX_BET") and amount > sget("GUESS_MAX_BET"):
        await q.answer(f"单注最多 {sget('GUESS_MAX_BET')} 积分", show_alert=True); return
    async with wallet_locks[uid]:
        if game_chips[cid][uid] < amount:
            await q.answer(f"积分不足：需 {amount}，你当前 {game_chips[cid][uid]}", show_alert=True); return
        game_chips[cid][uid] -= amount
        g["bets"].setdefault(uid, {"A": 0, "B": 0})[side] += amount
        g["side_pots"][side] += amount
        save_data()
    await q.answer(f"✅ 已押 {'🔵 ' + g['a'] if side == 'A' else '🔴 ' + g['b']} {amount} 分")
    await safe_edit(context.bot, cid, g["msg_id"], _guess_text(cid), reply_markup=_guess_buttons(cid))


async def _guess_close(cid, app):
    """竞猜倒计时：到点封盘（不下注、不退款），等管理员结算/撤销。"""
    g = guesses.get(cid)
    if not g: return
    remain = g["end_ts"] - now_bj().timestamp()
    if remain > 0:
        await asyncio.sleep(remain)
        g = guesses.get(cid)
        if not g: return
    if g.get("locked"): return
    g["locked"] = True
    save_data()
    try:
        await safe_edit(app.bot, cid, g["msg_id"], _guess_text(cid), reply_markup=None)
    except Exception:
        logger.exception("竞猜封盘看板刷新异常（已吞并）")
    # 兜底：管理员迟迟不结算/撤销时自动退款，绝不让玩家积分卡在奖池里（重启也捞不回来）
    if GUESS_AUTO_SETTLE_MINUTES and GUESS_AUTO_SETTLE_MINUTES > 0:
        try: background_tasks.add(asyncio.create_task(_guess_auto_settle(cid, app)))
        except Exception: pass


async def _guess_auto_settle(cid, app):
    """封盘后超时未处理 → 自动撤销并全额退款（积分卡死兜底）。"""
    try:
        await asyncio.sleep(max(1, float(GUESS_AUTO_SETTLE_MINUTES) * 60))
        g = guesses.get(cid)
        if not g or not g.get("locked") or g.get("settled"):
            return      # 已被结算/撤销/重开
        try:
            await _guess_do_cancel(app, cid, auto=True)
        except Exception:
            logger.exception("竞猜超时自动退款失败（已吞并）")
    except Exception:
        logger.exception("竞猜超时兜底任务异常（已吞并）")


async def _guess_do_settle(app, cid, winner):
    """结算：猜中方按注额比例瓜分全部奖池；无人猜中则奖池沉没。返回错误文案或 None。"""
    g = guesses.get(cid)
    if not g: return "本群没有进行中的竞猜"
    if g.get("settled"): return "本局已结算，请勿重复操作"
    g["settled"] = True      # 先占位：派彩里有 await，两个管理员同时结算会导致重复派彩
    winner = (winner or "").strip().upper()
    if winner not in ("A", "B"): return "用法：竞猜结算 A 或 竞猜结算 B"
    pots = g["side_pots"]
    total = pots["A"] + pots["B"]
    win_total = pots[winner]
    paid = []
    for uid, bets in g["bets"].items():
        stake = bets.get(winner, 0)
        if not stake or not win_total:
            continue
        amt = total * stake // win_total  # 比例瓜分（向下取整）
        if amt <= 0:
            continue
        async with wallet_locks[uid]:
            old = game_chips[cid].get(uid, 0)
            game_chips[cid][uid] = old + amt
        paid.append((uid, stake, amt, old))
    # 资金流审查：竞猜是人对人瓜分，净转移记账（赢家净得=派付-押注，输家净损=押注）
    nets = {}
    for uid, bets in g["bets"].items():
        staked = int(bets.get("A", 0)) + int(bets.get("B", 0))
        won = next((a for w, _s, a, _o in paid if w == uid), 0)
        nets[uid] = won - staked
    record_game_flows(cid, nets, "竞猜")
    rake_per = calc_rake(nets)[1]
    await commit_rake(app, cid, rake_per, "竞猜")
    guesses.pop(cid, None)
    save_data()
    ans_txt = g["a"] if winner == "A" else g["b"]
    if paid:
        lines = ""
        for uid, stake, amt, _old in sorted(paid, key=lambda x: -x[2])[:20]:
            _staked_all = sum(int(v) for v in g["bets"].get(uid, {}).values())
            _net = amt - _staked_all
            _r = rake_per.get(uid, 0)
            _r_txt = f"（实收 {_net - _r}，含抽水{_r}）" if _r else ""
            lines += f"\n🎉 {await get_name(app, uid, cid=cid)} 押 {stake} → 分得 {amt}｜净 {_net:+d}{_r_txt}"
        # 竞猜是「人对人瓜分」不产生新积分 → 不写入 total_earned（防对倒下注刷等级）
    else:
        lines = "\n（无人猜中，奖池沉没）"
    try:
        await send_settle(app, cid, f"🎯 竞猜结算｜{g['q']}\n✅ 答案：{ans_txt}｜奖池 {total} 分（{len(paid)} 人瓜分）" + lines)
    except Exception:
        logger.exception("竞猜结算播报异常（已吞并）")
    return None


async def _guess_do_cancel(app, cid, auto=False):
    """撤销竞猜：全额退还托管注金。返回错误文案或 None。"""
    g = guesses.get(cid)
    if not g: return "本群没有进行中的竞猜"
    g["settled"] = True   # 与结算互斥，防并发重复退款
    n = 0
    for uid, bets in g["bets"].items():
        back = int(bets.get("A", 0)) + int(bets.get("B", 0))
        if back <= 0:
            continue
        async with wallet_locks[uid]:
            game_chips[cid][uid] = game_chips[cid].get(uid, 0) + back
        n += 1
    guesses.pop(cid, None)
    save_data()
    try:
        tip = (f"⏳ 竞猜「{g['q']}」封盘后 {GUESS_AUTO_SETTLE_MINUTES} 分钟无人结算，已自动撤销，"
               f"{n} 人的托管注金全额退回。" if auto else
               f"🎯 竞猜「{g['q']}」已撤销，{n} 人的托管注金已全额退回。")
        await send_settle(app, cid, tip)
    except Exception:
        logger.exception("竞猜撤销播报异常（已吞并）")
    return None


async def _guess_do_create(app, cid, q, a, b, duration):
    """创建竞猜并发布到群（命令与网页共用）。返回错误文案或 None。"""
    if not sget("GUESS_ENABLED"):
        return "竞猜功能未开启（网页「积分系统 → 积分竞猜」可开启）"
    if cid in guesses:
        return "本群已有竞猜进行中，结算或撤销后再开"
    q, a, b = (q or "").strip()[:50], (a or "").strip()[:20], (b or "").strip()[:20]
    if not q or not a or not b:
        return "题目与选项 A/B 不能为空"
    try:
        duration = max(1, min(1440, int(duration)))
    except (TypeError, ValueError):
        duration = sget("GUESS_DURATION")
    guesses[cid] = {"q": q, "a": a, "b": b,
                    "end_ts": now_bj().timestamp() + duration * 60, "locked": False,
                    "bets": {}, "side_pots": {"A": 0, "B": 0}, "msg_id": None, "task": None}
    msg = await safe_send(app.bot, cid, _guess_text(cid), reply_markup=_guess_buttons(cid))
    if msg: guesses[cid]["msg_id"] = msg.message_id
    guesses[cid]["task"] = asyncio.create_task(_guess_close(cid, app))
    save_data()
    return None


async def cmd_guess_open(update, context):
    """管理员发起积分竞猜：/开竞猜 题目/选项A/选项B [时长分钟]，按钮下注，封盘后按比例瓜分。"""
    if not await need_auth(update, context): return
    if not is_group_chat(update):
        await send_reply(update, context, "⚠️ 竞猜请在群聊中使用。"); return
    if not is_bot_admin(update.effective_user.id):
        await send_reply(update, context, "❌ 仅 Bot 管理员可发起竞猜。"); return
    cid = update.effective_chat.id
    spec = " ".join(context.args or []).strip()
    parts = [p.strip() for p in spec.split("/") if p.strip()]
    if len(parts) < 3 or len(parts) > 4:
        await send_reply(update, context, "用法：/开竞猜 题目/选项A/选项B [时长分钟]"); return
    err = await _guess_do_create(context.application, cid, parts[0], parts[1], parts[2],
                                 parts[3] if len(parts) == 4 else sget("GUESS_DURATION"))
    if err:
        await send_reply(update, context, f"❌ {err}")


async def cmd_guess_settle(update, context):
    """管理员开出竞猜答案：/竞猜结算 A 或 /竞猜结算 B，猜中方按比例瓜分奖池。"""
    if not await need_auth(update, context): return
    if not is_group_chat(update):
        await send_reply(update, context, "⚠️ 请在群聊中使用。"); return
    if not is_bot_admin(update.effective_user.id):
        await send_reply(update, context, "❌ 仅 Bot 管理员可结算竞猜。"); return
    err = await _guess_do_settle(context.application, update.effective_chat.id,
                                 (context.args or [""])[0] if context.args else "")
    if err:
        await send_reply(update, context, f"❌ {err}")


async def cmd_guess_cancel(update, context):
    """管理员撤销竞猜：/竞猜撤销，全额退款。"""
    if not await need_auth(update, context): return
    if not is_group_chat(update):
        await send_reply(update, context, "⚠️ 请在群聊中使用。"); return
    if not is_bot_admin(update.effective_user.id):
        await send_reply(update, context, "❌ 仅 Bot 管理员可撤销竞猜。"); return
    err = await _guess_do_cancel(context.application, update.effective_chat.id)
    if err:
        await send_reply(update, context, f"❌ {err}")


async def cmd_buy_points(update, context):
    """购买积分（人工确认制，无需支付通道）：玩家申请 → 私聊通知管理员 → 管理员一键确认到账。"""
    if not await need_auth(update, context): return
    if not is_group_chat(update):
        await send_reply(update, context, "⚠️ 请在群聊中申请购买积分。"); return
    if not sget("BUY_ENABLED"):
        await send_reply(update, context, "❌ 购买积分功能未开启（网页「积分系统 → 购买积分」可开启）。"); return
    args = context.args or []
    if not args:
        on = sorted([p for p in buy_packages if p.get("on")], key=lambda x: x.get("sort", 0))
        if on:
            lines = ["💳 积分套餐", "━" * 14]
            for i, p in enumerate(on, 1):
                lines.append(f"{i}. {p.get('name', '?')}　¥{p.get('cny', 0)} = {p.get('points', 0)} 积分")
            lines.append("")
            lines.append("💡 发「充值 套餐名」或「充值 数量」提交申请，管理员确认后到账。")
            await send_reply(update, context, "\n".join(lines)); return
        await send_reply(update, context, f"用法：充值 数量（{sget('BUY_MIN')} ~ {sget('BUY_MAX')}）\n提交申请后联系管理员转账，管理员确认后积分自动到账。"); return
    pkg_arg = args[0].strip()
    amount = int(pkg_arg) if pkg_arg.isdigit() else None
    if amount is None:
        p = next((x for x in buy_packages if x.get("on") and x.get("name") == pkg_arg), None)
        if p:
            amount = int(p.get("points", 0) or 0)
    if not amount:
        await send_reply(update, context, "❌ 没有这个套餐；按数量充值用法：充值 数量。"); return
    from_pkg = amount is not None and not pkg_arg.isdigit()
    if not from_pkg and not (sget("BUY_MIN") <= amount <= sget("BUY_MAX")):
        await send_reply(update, context, f"❌ 单次购买需在 {sget('BUY_MIN')} ~ {sget('BUY_MAX')} 之间。"); return
    cid, uid = update.effective_chat.id, update.effective_user.id
    oid = secrets.token_hex(4)
    buy_orders[oid] = {"cid": cid, "uid": uid, "amount": amount, "ts": now_bj().strftime("%Y-%m-%d %H:%M")}
    save_data()
    await send_reply(update, context, f"📝 购买申请已提交：{amount} 积分（单号 {oid}）\n请联系管理员完成转账，确认后积分自动到账。")
    try:
        kb = InlineKeyboardMarkup([[InlineKeyboardButton("✅ 确认到账", callback_data=f"buyok_{oid}"),
                                    InlineKeyboardButton("❌ 取消", callback_data=f"buyno_{oid}")]])
        await context.bot.send_message(ADMIN_USER_ID,
            f"💳 购买积分申请｜单号 {oid}\n用户：{await get_name(context.application, uid, cid=cid)}（{uid}）\n群：{chat_name_cache.get(cid) or cid}（{cid}）\n数量：{amount} 积分", reply_markup=kb)
    except Exception:
        logger.exception("购买积分申请通知管理员失败（已吞并）")


async def _buy_settle(context, oid, ok, q):
    o = buy_orders.pop(oid, None)
    if not o:
        await q.answer("该申请已处理过", show_alert=True); return
    if ok:
        _cid, _uid = o["cid"], o["uid"]
        old_earned = _earn_get(_cid, _uid)
        game_chips[_cid][_uid] += o["amount"]
        _earn_add(_cid, _uid, o["amount"])   # 购买到账是系统新产出，计入累计获得
        try:
            await context.bot.send_message(o["cid"], f"✅ 你的购买申请（{o['amount']} 积分）已确认到账，当前积分 {game_chips[o['cid']][o['uid']]}。")
        except Exception:
            pass
        try:
            await _check_level_change(context.application, _cid, _uid, old_earned, _earn_get(_cid, _uid))
        except Exception:
            logger.exception("购买到账等级通知失败（已吞并）")
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
    if not await need_auth(update, context): return
    cid, admin = update.effective_chat.id, update.effective_user.id
    if not is_group_chat(update):
        await send_reply(update, context, "⚠️ 禁言请在群聊中使用。"); return
    if not await _is_group_admin(context, cid, admin):
        await send_reply(update, context, "❌ 仅管理员可操作"); return
    args = context.args or []
    reply = update.message.reply_to_message
    if reply and args and args[0].isdigit():
        target, minutes = reply.from_user.id, max(1, min(int(args[0]), 43200))
    elif len(args) >= 2 and args[0].lstrip("-").isdigit() and args[1].isdigit():
        target, minutes = int(args[0]), max(1, min(int(args[1]), 43200))
    else:
        await send_reply(update, context, "用法：回复消息发「禁言 分钟」，或「禁言 用户ID 分钟」"); return
    if target in whitelist[cid]:
        await send_reply(update, context, "✅ 该用户在白名单中，已跳过禁言。"); return
    if target == admin:
        await send_reply(update, context, "❌ 不能禁言自己。"); return
    try:
        await context.bot.restrict_chat_member(cid, target, permissions=ChatPermissions(can_send_messages=False),
                                               until_date=int(now_bj().timestamp()) + minutes * 60)
    except Exception as e:
        await send_reply(update, context, f"❌ 禁言失败（需 bot 为群管理员且有禁言权限）：{e}"); return
    tname = user_names.get(target, str(target))
    _admin_log(cid, admin, f"禁言 {minutes} 分钟", tname); save_data()
    await send_reply(update, context, f"🔇 已禁言 {tname} {minutes} 分钟。")

async def cmd_unmute(update, context):
    if not await need_auth(update, context): return
    cid, admin = update.effective_chat.id, update.effective_user.id
    if not await _is_group_admin(context, cid, admin):
        await send_reply(update, context, "❌ 仅管理员可操作"); return
    reply = update.message.reply_to_message
    args = context.args or []
    if reply:
        target = reply.from_user.id
    elif args and args[0].lstrip("-").isdigit():
        target = int(args[0])
    else:
        await send_reply(update, context, "用法：回复消息发「解禁」，或「解禁 用户ID」"); return
    try:
        await context.bot.restrict_chat_member(cid, target, permissions=ChatPermissions(
            can_send_messages=True, can_send_other_messages=True, can_add_web_page_previews=True,
            can_send_polls=True, can_invite_users=True))
    except Exception as e:
        await send_reply(update, context, f"❌ 解禁失败：{e}"); return
    _admin_log(cid, admin, "解除禁言", user_names.get(target, str(target))); save_data()
    await send_reply(update, context, f"🔊 已解除 {user_names.get(target, target)} 的禁言。")

async def cmd_jv_pass(update, context):
    """管理员一键放行入群验证（2026-09-09 兜底通道）。

    场景：新人卡在验证（被禁言/验证消息被顶掉/答错超限）在群里求助，
    管理员回复其消息发「放行」即可解除限制并清掉 pending，不用去后台改配置。
    """
    if not await need_auth(update, context): return
    cid, admin = update.effective_chat.id, update.effective_user.id
    if not await _is_group_admin(context, cid, admin):
        await send_reply(update, context, "❌ 仅管理员可操作"); return
    reply = update.message.reply_to_message
    args = context.args or []
    if reply:
        target = reply.from_user.id
    elif args and args[0].lstrip("-").isdigit():
        target = int(args[0])
    else:
        await send_reply(update, context, "用法：回复该成员的消息发「放行」，或「放行 用户ID」"); return
    rec = join_verify_pending.pop(f"{cid}:{target}", None)
    try:
        await context.bot.restrict_chat_member(cid, target, permissions=ChatPermissions(
            can_send_messages=True, can_send_other_messages=True, can_add_web_page_previews=True,
            can_send_polls=True, can_invite_users=True))
    except Exception as e:
        await send_reply(update, context, f"❌ 放行失败：{e}"); return
    if rec and rec.get("msg_id"):
        try:
            await context.bot.delete_message(cid, int(rec["msg_id"]))
        except Exception:
            pass
    _admin_log(cid, admin, "放行入群验证", user_names.get(target, str(target))); save_data()
    await send_reply(update, context,
                     f"✅ 已放行 {user_names.get(target, target)}，他现在可以发言了。"
                     + ("（原有验证记录已清除）" if rec else ""))


async def cmd_groupban(update, context):
    """Telegram 级封禁：踢出并禁止再入群（区别于 /拉黑 的 bot 层黑名单）。"""
    if not await need_auth(update, context): return
    cid, admin = update.effective_chat.id, update.effective_user.id
    if not is_group_chat(update):
        await send_reply(update, context, "⚠️ 请在群聊中使用。"); return
    if not await _is_group_admin(context, cid, admin):
        await send_reply(update, context, "❌ 仅管理员可操作"); return
    reply = update.message.reply_to_message
    args = context.args or []
    if reply:
        target = reply.from_user.id
    elif args and args[0].lstrip("-").isdigit():
        target = int(args[0])
    else:
        await send_reply(update, context, "用法：回复消息发「群封」，或「群封 用户ID」"); return
    if target in whitelist[cid]:
        await send_reply(update, context, "✅ 该用户在白名单中，已跳过。"); return
    try:
        await context.bot.ban_chat_member(cid, target)
    except Exception as e:
        await send_reply(update, context, f"❌ 封禁失败（需 bot 为群管理员）：{e}"); return
    tname = user_names.get(target, str(target))
    _admin_log(cid, admin, "Telegram级封禁", tname); save_data()
    await send_reply(update, context, f"🔨 已将 {tname} 封禁并移出群组（可用「群解封」撤销）。")

async def cmd_groupunban(update, context):
    if not await need_auth(update, context): return
    cid, admin = update.effective_chat.id, update.effective_user.id
    if not await _is_group_admin(context, cid, admin):
        await send_reply(update, context, "❌ 仅管理员可操作"); return
    args = context.args or []
    if not args or not args[0].lstrip("-").isdigit():
        await send_reply(update, context, "用法：群解封 用户ID"); return
    target = int(args[0])
    try:
        await context.bot.unban_chat_member(cid, target, only_if_banned=True)
    except Exception as e:
        await send_reply(update, context, f"❌ 解封失败：{e}"); return
    _admin_log(cid, admin, "Telegram级解封", str(target)); save_data()
    await send_reply(update, context, f"✅ 已解封 {target}，可重新拉入群。")

async def cmd_whitelist(update, context):
    if not await need_auth(update, context): return
    cid = update.effective_chat.id
    users = whitelist.get(cid, set())
    if not users:
        await send_reply(update, context, "白名单为空。回复成员消息发「加白」可加入。"); return
    lines = ["📋 白名单成员", "━" * 14]
    for i, u in enumerate(sorted(users), 1):
        lines.append(f"{i}. {user_names.get(u, u)}（{u}）")
    lines.append("💡 白名单成员免疫禁言/群封；「加白」「删白」管理。")
    await send_reply(update, context, "\n".join(lines))

async def cmd_whitelist_add(update, context):
    if not await need_auth(update, context): return
    cid, admin = update.effective_chat.id, update.effective_user.id
    if not await _is_group_admin(context, cid, admin):
        await send_reply(update, context, "❌ 仅管理员可操作"); return
    reply = update.message.reply_to_message
    args = context.args or []
    if reply:
        target = reply.from_user.id
    elif args and args[0].lstrip("-").isdigit():
        target = int(args[0])
    else:
        await send_reply(update, context, "用法：回复成员消息发「加白」，或「加白 用户ID」"); return
    whitelist[cid].add(target); save_data()
    _admin_log(cid, admin, "加白名单", user_names.get(target, str(target)))
    await send_reply(update, context, f"✅ 已把 {user_names.get(target, target)} 加入白名单。")

async def cmd_whitelist_del(update, context):
    if not await need_auth(update, context): return
    cid, admin = update.effective_chat.id, update.effective_user.id
    if not await _is_group_admin(context, cid, admin):
        await send_reply(update, context, "❌ 仅管理员可操作"); return
    reply = update.message.reply_to_message
    args = context.args or []
    if reply:
        target = reply.from_user.id
    elif args and args[0].lstrip("-").isdigit():
        target = int(args[0])
    else:
        await send_reply(update, context, "用法：回复成员消息发「删白」，或「删白 用户ID」"); return
    whitelist[cid].discard(target); save_data()
    _admin_log(cid, admin, "移出白名单", user_names.get(target, str(target)))
    await send_reply(update, context, f"✅ 已把 {user_names.get(target, target)} 移出白名单。")

async def cmd_adminlist_tg(update, context):
    """列出本群 Telegram 管理员（实时接口）。"""
    if not await need_auth(update, context): return
    cid = update.effective_chat.id
    try:
        admins = await context.bot.get_chat_administrators(cid)
    except Exception as e:
        await send_reply(update, context, f"❌ 获取失败：{e}"); return
    lines = ["👥 本群管理员", "━" * 14]
    for a in sorted(admins, key=lambda x: (x.status != "creator", x.user.id)):
        mark = "👑" if a.status == "creator" else "⚙️"
        lines.append(f"{mark} {a.user.first_name or ''}（{a.user.id}）")
    await send_reply(update, context, "\n".join(lines))

# ---------- 邀请系统：专属链接追踪进群、合格结算、排行 ----------
# 记录状态语义（2026-09-08 改造，替代 audit 审核层 + 前置死字段）：
#   qualified=True = 已合格（本群达标）· rejected=True = 进群硬门槛不满足(无头像/用户名)永不计
#   award>0 = 已发放奖励；旧存档 audit=="ok" 视为合格、audit=="rejected" 视为拒绝（兼容读取）。
def _rec_qualified(rec):
    if not rec: return False
    if rec.get("qualified") is not None: return bool(rec.get("qualified"))
    return rec.get("audit") == "ok"

def _rec_rejected(rec):
    if not rec: return False
    if rec.get("rejected") is not None: return bool(rec.get("rejected"))
    return rec.get("audit") == "rejected"

def _rec_awarded(rec):
    return int((rec or {}).get("award", 0) or 0) > 0

def _rec_ok(rec):
    """合格记录（含已退群）：达标且未被拒、未被广告连坐。用于「合格人数/每日合格」统计。

    与 _rec_valid 的区别：本函数**不排除已退群**——用户面板的「合格」表示「历史达标过的人数」，
    退群不抹掉这个事实（测试 test_race_schedule_invdel 已固化该语义）。
    """
    if not rec:
        return False
    return bool(_rec_qualified(rec) and not _rec_rejected(rec) and not rec.get("ad_flag"))


def _rec_valid(rec):
    """有效邀请记录（唯一判定入口）：合格 + 未退群 + 未被拒 + 未因发广告被连坐。

    2026-09-09 收口：此前多处各自手写 `_rec_qualified(r) and not _rec_rejected(r) and not r.get("left")`，
    加「广告连坐」时只改了 _invite_count → 排行和群总览仍把广告号算作有效邀请。
    用于「有效邀请数」口径（邀请数、排行、群总览今日有效邀请）。
    """
    if not rec:
        return False
    return bool(_rec_ok(rec) and not rec.get("left"))


def _invite_count(inviter, cid=None):
    """邀请人有效邀请数（合格且未退群、未发广告连坐）；cid 限定群，None=全部群。"""
    n = 0
    for rec in invite_records.values():
        if rec.get("inviter") != inviter:
            continue
        if cid is not None and rec.get("cid") != cid:
            continue
        if _rec_valid(rec):
            n += 1
    return n

def _inviter_awarded_count(cid, inviter):
    """该邀请人在本群已发放奖励的次数（超额即不再发，防白嫖）。"""
    return sum(1 for r in invite_records.values()
               if r.get("inviter") == inviter and r.get("cid") == cid and _rec_awarded(r))

def _join_user_obj(cmu):
    """从 chat_member 事件或服务消息中取被邀请人 user 对象。"""
    u = getattr(getattr(cmu, "new_chat_member", None), "user", None)
    if u is None:
        mlist = getattr(cmu, "new_chat_members", None)
        if mlist:
            u = mlist[0]
    return u

async def _user_has_avatar(context, uid):
    """查询用户是否有头像（邀请质量门槛；网络异常视为有头像放行，防误伤正常进群）。"""
    try:
        photos = await context.bot.get_user_profile_photos(uid, limit=1)
        return bool(getattr(photos, "total_count", 0))
    except Exception:
        return True

async def _invite_qualify_ready(cid, uid):
    """被邀请人在本群是否达到质量要求（发言阈值 / 净赚积分阈值）。
    注意：game_chips 是 defaultdict(初始分)——必须用「净赚=余额-初始分」判定积分，
    否则人人进群即自动 5W 初始分 → 积分门槛永远满足，防白嫖失效。"""
    if sget("INVITE_QUALIFY_MSGS") > 0:
        msgs = int((member_profiles.get(cid, {}).get(uid, {}) or {}).get("msgs", 0) or 0)
        if msgs < sget("INVITE_QUALIFY_MSGS"):
            return False
    if sget("INVITE_QUALIFY_POINTS") > 0:
        bal = int(game_chips.get(cid, {}).get(uid, sget("GAME_STARTING_CHIPS")) or 0)
        if abs(bal - sget("GAME_STARTING_CHIPS")) < sget("INVITE_QUALIFY_POINTS"):
            return False
    return True

def _invite_daily_get(cid, inviter):
    """取邀请人当日拉新统计 {"times":已发奖次数,"points":已发奖积分}。"""
    return invite_daily[now_bj().strftime("%Y-%m-%d")][cid][inviter]

def _invite_daily_capped(cid, inviter):
    """是否已达当日拉新上限（人数 / 积分任一超限即停发）。0=不限。"""
    d = _invite_daily_get(cid, inviter)
    if sget("INVITE_DAILY_CAP_TIMES") > 0 and int(d.get("times", 0)) >= int(sget("INVITE_DAILY_CAP_TIMES")):
        return True
    if sget("INVITE_DAILY_CAP_POINTS") > 0 and int(d.get("points", 0)) >= int(sget("INVITE_DAILY_CAP_POINTS")):
        return True
    return False

def _invite_daily_add(cid, inviter, pts):
    """记一次当日发放（人数+1，积分累加）。"""
    d = _invite_daily_get(cid, inviter)
    d["times"] = int(d.get("times", 0)) + 1
    d["points"] = int(d.get("points", 0)) + int(pts)

async def _invite_try_award(app, rec):
    """合格后发奖（不超每人上限 INVITE_REWARD_TIMES / 当日上限；award>0 防重入）。"""
    if _rec_awarded(rec):
        return
    cid, inviter = rec["cid"], rec["inviter"]
    if _inviter_awarded_count(cid, inviter) >= max(1, int(sget("INVITE_REWARD_TIMES"))):
        return  # 超上限：仍合格（计入合格数），但不再发奖
    if _invite_daily_capped(cid, inviter):
        return  # 当日拉新上限：仍合格，但当日不再发奖（次日恢复）
    await _invite_award(app, rec)

async def _invite_ping_qualify(app, cid, uid):
    """被邀请人在本群有动静（发言/签到/刷新按钮）后调用：达标则标合格并发奖。幂等、异常吞并。"""
    try:
        rec = invite_records.get(f"{cid}:{uid}")
        if not rec or rec.get("left") or _rec_rejected(rec) or _rec_qualified(rec):
            return
        if not sget("INVITE_QUALIFY_ENABLED"):
            return  # 开关关 = 进群已即时结算，不重复判
        if not await _invite_qualify_ready(cid, uid):
            return
        rec["qualified"] = True
        await _invite_try_award(app, rec)
        save_data()
    except Exception:
        logger.exception("邀请达标判定异常（已吞并）")

async def _invite_refresh_all(app, cid, inviter):
    """刷新进度：重判某邀请人在本群全部待达标记录（事件驱动兜底）。返回新发奖数。"""
    n = 0
    for key, rec in list(invite_records.items()):
        if rec.get("inviter") != inviter or rec.get("cid") != cid:
            continue
        if rec.get("left") or _rec_rejected(rec) or _rec_qualified(rec):
            continue
        before = _rec_awarded(rec)
        await _invite_ping_qualify(app, cid, rec.get("invitee"))
        after = _rec_awarded(invite_records.get(key))
        if after and not before:
            n += 1
    return n


async def _invite_award(app, rec):
    """给邀请人发合格奖励并通知（群内 + 私聊）。rec 需含 cid/inviter/invitee_name；qualified 由调用方先置位。"""
    inviter, cid = rec["inviter"], rec["cid"]
    reward = max(0, int(sget("INVITE_REWARD")))
    if reward:
        # 必须持锁：两名被邀请人同时达标时，两次"读 old + 写 old+reward"会互相覆盖，只到账一份
        async with wallet_locks[inviter]:
            old = game_chips[cid].get(inviter, 0)
            old_earned = _earn_get(cid, inviter)
            game_chips[cid][inviter] = old + reward
            _earn_add(cid, inviter, reward)   # 邀请奖励是系统新产出，计入累计获得
        rec["award"] = reward
        _invite_daily_add(cid, inviter, reward)   # 当日拉新统计（每日上限用）
        ledger_add(cid, 0, inviter, reward, "邀请奖励")
        await _check_level_change(app, cid, inviter, old_earned, _earn_get(cid, inviter))
    inviter_name = await get_name(app, inviter, cid=cid)
    if sget("INVITE_NOTIFY"):
        try:
            await app.bot.send_message(chat_id=inviter,
                text=f"🎟️ 你邀请的 {rec.get('invitee_name', '')} 已达标合格，奖励 {reward} 积分已到账。发「{INVITE_LINK_CMD}」看进度。")
        except Exception:
            pass
    if str(sget("INVITE_OK_GROUP")).strip():
        try:
            ok_msg = await app.bot.send_message(chat_id=cid, text=_fmt_tpl(
                "invite_ok_group", inviter=inviter_name, inviter_id=inviter,
                invitee=rec.get("invitee_name", ""), invitee_id=rec.get("invitee", ""), reward=reward))
            if ok_msg and sget("REPLY_DELETE_SECONDS") > 0:
                schedule_delete(app, cid, ok_msg, sget("REPLY_DELETE_SECONDS"))
        except Exception:
            pass
    save_data()


def _grant_newbie_reward(cid, uid, name=""):
    """新人欢迎奖励（2026-09-09 用户规则）：新人首次发言时发放，帮助其有基础分。

    幂等：`newbie_rewarded["cid:uid"]` 标记，重复调用不重复发。
    只对「入群记录里能查到的新人」发（避免老成员补发）。
    返回 (发放积分, 升级前的累计获得)；未发放返回 (0, None)。
    """
    if not sget("NEWBIE_REWARD_ENABLED") or int(sget("NEWBIE_REWARD")) <= 0:
        return 0, None
    key = f"{cid}:{uid}"
    if newbie_rewarded.get(key):
        return 0, None
    if uid not in member_joined_at.get(cid, {}):
        return 0, None                # 非本群记录过的新成员（老成员/重启后清空）不发
    newbie_rewarded[key] = True
    pts = int(sget("NEWBIE_REWARD"))
    old_earned = _earn_get(cid, uid)
    game_chips[cid][uid] += pts
    _earn_add(cid, uid, pts)
    ledger_add(cid, 0, uid, pts, "新人欢迎奖励")
    save_data()
    logger.info("新人欢迎奖励已发放 cid=%s uid=%s +%s（累计 %s）", cid, uid, pts, _earn_get(cid, uid))
    return pts, old_earned


def _invite_flag_ad(cid, uid, reason=""):
    """风控连坐（2026-09-09 用户规则）：被邀请人发广告 → 标记其邀请记录，不再计入邀请人的合格数。

    不追回已发奖励（钱已到账，追回会引起纠纷），只做「后续不计合格」+ 记录违规原因，
    让邀请人无法继续靠拉广告号刷奖励。
    """
    rec = invite_records.get(f"{cid}:{uid}")
    if not rec:
        return False
    rec["ad_flag"] = True
    rec["ad_reason"] = str(reason or "")
    rec["ad_ts"] = now_bj().strftime("%Y-%m-%d %H:%M")
    save_data()
    logger.warning("邀请连坐：被邀请人发广告 cid=%s uid=%s inviter=%s 原因=%s",
                   cid, uid, rec.get("inviter"), reason)
    return True


async def _invite_track_join(cmu, cid, uid, name, context):
    """邀请追踪归因（优先级）：① invite_confirmed（deep-link/主动问确认，最可靠）
    → ② 事件/申请携带的链接精确匹配 → ③ 都没有则不归因（宁缺毋滥）。
    归因后记记录/发奖励/通知（所有异常吞并）。"""
    try:
        if not sget("INVITE_ENABLED") or uid <= 0 or cid not in AUTHORIZED_GROUPS:
            _inv_dbg(cid, f"进群 uid={uid} 跳过：开关{sget('INVITE_ENABLED')}/授权{cid in AUTHORIZED_GROUPS}")
            return
        key = f"{cid}:{uid}"
        if key in invite_records:   # 重复进群不重复计，仅视为回归
            invite_records[key]["left"] = False
            _inv_dbg(cid, f"进群 uid={uid} 重复（已有记录，视为回归）")
            return
        link = (getattr(getattr(cmu, "invite_link", None), "link", "")
                or invite_pending.pop(f"{cid}:{uid}", ""))   # 申请制兜底：审批后的 join 事件常不带链接
        _inv_dbg(cid, f"进群 uid={uid} 事件链接：{link or '（无）'}")
        confirmed = invite_confirmed.pop(key, 0)
        inviter = 0
        if confirmed:
            inviter = confirmed   # deep-link START / 主动问按钮：归因最可靠，优先于一切链接字段
            _inv_dbg(cid, f"✅ 归因成功 uid={uid} → 邀请人 {confirmed}（确认制）")
        else:
            for i_uid, info in invite_links.get(cid, {}).items():
                if info.get("link") == link and i_uid != uid:
                    inviter = i_uid
                    break
        if not inviter:
            if link:
                _inv_dbg(cid, f"⚠️ 归因失败：链接不在已存表（已存：{[i.get('link','')[-12:] for i in invite_links.get(cid, {}).values()]}）")
                if str(sget("INVITE_INVALID_MSG")).strip() and _inv_notice_fresh(key):
                    try:
                        await context.bot.send_message(chat_id=cid, text=_fmt_tpl("invite_invalid_msg", name=name))
                    except Exception:
                        pass
            else:
                # 事件/申请都没带链接 → 不归因（宁缺毋滥，绝不猜测安错人）。
                # /link 发的是申请制链接：正常路径 申请(chat_join_request 必带链接入 pending)→批准→进群，
                # 进群事件即使漏链接也能从 pending 兜底归因；都查不到说明是手动拉人/直接搜索进群。
                _inv_dbg(cid, "⚠️ 事件与申请均无链接 → 不归因（宁缺毋滥）：申请制路径应有 pending，查不到多为手动拉人/搜索进群")
                # 手动拉人计入（可选开关）：chat_member 的 from_user = 造成本次进群的人（手动添加时即添加人）
                adder = getattr(cmu, "from_user", None)
                a_id = getattr(adder, "id", 0) if adder else 0
                if sget("INVITE_MANUAL_COUNT") and a_id > 0 and a_id != uid and not getattr(adder, "is_bot", False):
                    inviter = a_id
                    _inv_dbg(cid, f"✅ 手动拉人计入邀请：uid={uid} 由 {a_id} 添加（开关已开）")
                else:
                    # 黑盒终结：给管理员私聊发诊断通知（不打扰群），说明为何没计入
                    # 双事件源去重：chat_member + 服务消息各调一次，不去重管理员会收到 2 条（2026-09-10 用户报障）
                    try:
                        if _inv_notice_fresh(key):
                            await context.bot.send_message(
                                ADMIN_USER_ID,
                                f"ℹ️ 进群未计入邀请：{name}（<code>{uid}</code>）加入群 <code>{cid}</code> 时"
                                f"未携带任何邀请链接（多为手动拉人/直接搜索进群）。\n"
                                f"邀请只认「邀请人的专属链接」进群；可让邀请人邀请，或后台开启「手动拉人计入邀请」。",
                                parse_mode="HTML")
                    except Exception:
                        pass
            if not inviter:
                return
        if inviter == uid:
            _inv_dbg(cid, f"uid={uid} 自己邀自己，跳过")
            if str(sget("INVITE_SELF_MSG")).strip():
                try:
                    await context.bot.send_message(chat_id=cid, text=_fmt_tpl("invite_self_msg", name=name))
                except Exception:
                    pass
            return
        _inv_dbg(cid, f"✅ 归因成功 uid={uid} → 邀请人 {inviter}")
        rec = {"cid": cid, "inviter": inviter, "invitee": uid, "invitee_name": name,
               "ts": now_bj().strftime("%Y-%m-%d %H:%M"), "qualified": False,
               "rejected": False, "left": False, "award": 0, "link": link,
               "manual": not bool(link) and not confirmed,   # 手动拉人计入的记录带 manual 标记（确认制归因不算）
               "source": "confirm" if confirmed else "link"}
        # 进群硬门槛（头像/用户名，进群瞬间检查一次；不满足直接拒绝，永不发奖）
        ju = _join_user_obj(cmu)
        if sget("INVITE_QUALIFY_USERNAME") and not getattr(ju, "username", None):
            rec["rejected"] = True; rec["note"] = "无用户名"
            _inv_dbg(cid, f"进群 uid={uid} 无用户名 → 拒绝（永不发奖）")
        elif sget("INVITE_QUALIFY_AVATAR") and not await _user_has_avatar(context, uid):
            rec["rejected"] = True; rec["note"] = "无头像"
            _inv_dbg(cid, f"进群 uid={uid} 无头像 → 拒绝（永不发奖）")
        invite_records[key] = rec
        if not sget("INVITE_QUALIFY_ENABLED") and not rec["rejected"]:
            # 合格结算关 → 兼容老行为：进群即合格发奖
            rec["qualified"] = True
            await _invite_try_award(context.application, rec)
        else:
            _inv_dbg(cid, f"进群 uid={uid} 记待达标（达标后事件驱动发奖）")
        save_data()
    except Exception:
        logger.exception("邀请追踪异常（已吞并）")


def _invite_rank_rows(scope):
    """按 scope（today/month/all）算邀请排行，返回 [(rank, uid, count)]（前 10）。"""
    today = now_bj().strftime("%Y-%m-%d")
    month = today[:7]
    counts = defaultdict(int)
    for rec in invite_records.values():
        if not _rec_valid(rec):
            continue
        ts = str(rec.get("ts", ""))
        if scope == "today" and not ts.startswith(today):
            continue
        if scope == "month" and not ts.startswith(month):
            continue
        counts[rec.get("inviter")] += 1
    counts.pop(0, None)
    ranked = sorted(counts.items(), key=lambda x: -x[1])[:10]
    return [(i + 1, uid, n) for i, (uid, n) in enumerate(ranked)]


async def _invite_send_rank(update, context, scope):
    if not await need_auth(update, context): return
    if not sget("INVITE_ENABLED"):
        await send_reply(update, context, "❌ 邀请系统未开启（网页「群组设置 → 邀请系统」可开启）。"); return
    if sget("INVITE_RANK_ADMIN_ONLY") and not is_bot_admin(update.effective_user.id):
        await send_reply(update, context, "❌ 邀请排行仅管理员可查。"); return
    cid = update.effective_chat.id
    titles = {"today": "invite_rank_today_msg", "month": "invite_rank_month_msg", "all": "invite_rank_all_msg"}
    lines = [_fmt_tpl(titles[scope])]
    rows = _invite_rank_rows(scope)
    if not rows:
        lines.append("暂无数据")
    for i, uid, n in rows:
        lines.append(_fmt_tpl("invite_rank_line_fmt", i=i, name=await get_name(context.application, uid, cid=cid), count=n))
    await send_reply(update, context, "\n".join(lines))


async def cmd_invite_rank_today(update, context):
    """今日邀请排行。"""
    await _invite_send_rank(update, context, "today")


async def cmd_invite_rank_month(update, context):
    """本月邀请排行。"""
    await _invite_send_rank(update, context, "month")


async def cmd_invite_rank_all(update, context):
    """总邀请排行。"""
    await _invite_send_rank(update, context, "all")


async def cmd_invite_link(update, context):
    """获取本群专属邀请链接：/link。生成的是 deep-link（t.me/<bot>?start=inv_邀请人_群id）：
    新人点开 → bot 私聊点 START → 归因即时锁定（不依赖 Telegram 群事件带链接——公开群
    官方就不保证给 bot 传 invite_link，实测直链/申请制两条路都丢链接）。"""
    if not await need_auth(update, context): return
    if not is_group_chat(update):
        await send_reply(update, context, "⚠️ 请在群聊中使用。"); return
    if not sget("INVITE_ENABLED"):
        await send_reply(update, context, "❌ 邀请系统未开启（网页「群组设置 → 邀请系统」可开启）。"); return
    cid = update.effective_chat.id
    uid = update.effective_user.id
    # 守卫：bot 用户名未就绪时会拼出 t.me/None 这种坏链接（深链功能的已知坑），宁可直接提示也别发坏链
    _bot_un = (getattr(context.bot, "username", "") or "").strip() or str(globals().get("_BOT_USERNAME") or "").strip()
    if not _bot_un:
        await send_reply(update, context, "❌ 机器人用户名尚未就绪，请稍等几秒后重试（或联系管理员）。")
        return
    deep = f"https://t.me/{_bot_un}?start=inv_{uid}_{cid}"
    mine = invite_links.get(cid, {}).get(uid)
    if not mine or mine.get("mode") != "deeplink" or mine.get("link") != deep:
        invite_links.setdefault(cid, {})[uid] = {"link": deep,
                                                 "invite_id": f"inv_{uid}",
                                                 "ts": now_bj().strftime("%Y-%m-%d %H:%M"),
                                                 "mode": "deeplink"}
        _inv_dbg(cid, f"生成 deep-link inviter={uid}：…{deep[-24:]}")
        save_data()
        mine = invite_links[cid][uid]
    link = mine.get("link", "")
    cname = chat_name_cache.get(cid) or (getattr(update.effective_chat, "title", "") or str(cid))
    # 邀请面板推私聊（群内不刷屏）；私聊发不出（用户没 /start）才回退群内卡片
    if await _invite_push_card_to_private(context, uid, cid, cname):
        await send_reply(update, context, "🎟️ 邀请面板已发到你的私聊，进度可随时在私聊刷新。")
        return
    await send_reply(update, context, "⚠️ 私聊推送失败（可能你还没私聊过我发 /start），先在这里看：")
    await _invite_send_progress_card(update, context, uid, cid, cname, link=link)


async def cmd_invite_test(update, context):
    """邀请归因预演（管理员）：只读模拟，不改任何数据、不发奖励。
    演示归因判定：①事件带链接 → 精确匹配 ②事件漏链接 → 一律不归因（宁缺毋滥）。
    用于定位「进人不加分」：/link 直链进群事件必带链接；若事件常漏链接，多半是群开了「申请加入」。"""
    if not await need_auth(update, context): return
    cid = update.effective_chat.id
    uid = update.effective_user.id
    if cid not in AUTHORIZED_GROUPS:
        await send_reply(update, context, "❌ 本群未授权。"); return
    mine = invite_links.get(cid, {}).get(uid)
    if not mine:
        await send_reply(update, context, "❌ 你还没有专属链接，先发「邀请」领。"); return
    link = mine.get("link", "")
    n_links = len([i for i, info in invite_links.get(cid, {}).items() if str(info.get("link", "")).startswith("http") and i != uid])
    fake_uid = 10 ** 12 + int(time.time() * 1000) % (10 ** 11)

    def _judge(evt_link):
        """与 _invite_track_join 同款判定：返回 (inviter, 说明)。虚拟受邀人是 fake_uid。"""
        if evt_link:
            for i_uid, info in invite_links.get(cid, {}).items():
                if info.get("link") == evt_link and i_uid != fake_uid:
                    return i_uid, "命中：事件携带的链接与" + ("你的" if i_uid == uid else "别人的") + "专属链接一致"
            return 0, "⚠️ 链接不在已存表（进的人用的是别处链接？）"
        return 0, "事件漏链接 → 一律不归因（宁缺毋滥）：直链进群必带链接，漏链接说明走的是申请制或直接拉人"

    L = ["🧪 邀请归因预演（只读，不改数据）", "━━━━━━━━━━━━━━━━━"]
    L.append(f"你的专属链接：…{link[-12:]}")
    L.append(f"本群专属链接数（含你的）：{n_links + 1} 条")
    L.append("")
    L.append("<b>场景① 事件带链接</b>（/link 直链进群，正常都带）")
    a, b = _judge(link)
    L.append(f"　→ 归因：{'✅ ' + str(a) if a else '❌ 失败'}")
    L.append(f"　　{b}")
    L.append("")
    L.append("<b>场景② 事件漏链接</b>（直链不会发生；申请制/直接拉人会出现）")
    c_, d = _judge("")
    L.append(f"　→ 归因：{'✅ ' + str(c_) if c_ else '❌ 不归因'}")
    L.append(f"　　{d}")
    L.append("")
    L.append("判定失败 ≠ 系统坏了：先发 /邀请调试 看 bot 是不是管理员、群有没有开「申请加入」。")
    await send_reply(update, context, "\n".join(L))


async def on_new_members_msg(update, context):
    """message 版入群事件（普通群收不到 chat_member 更新，只能靠服务消息兜底）。
    普通群的服务消息不带邀请链接，能归因到就走 pending 映射，归因不到就静默跳过。"""
    _bind_update_cid(update)
    try:
        message = update.effective_message
        if not message or not message.new_chat_members:
            return
        cid = message.chat_id
        _inv_dbg(cid, f"[svc] on_new_members_msg 触发 新成员数={len(message.new_chat_members)}")
        for member in message.new_chat_members:
            uid = member.id
            name = member.first_name or f"用户{uid}"
            _inv_dbg(message.chat_id, f"服务消息进群 uid={uid}（new_chat_members 兜底）")
            await _invite_track_join(message, cid, uid, name, context)
            _gate_ok = True
            if not member.is_bot and not is_bot_admin(uid):
                _gate_ok = await _join_gate_check(context, cid, member, name)    # 硬门槛：不满足直接移出
                await _raid_on_join(context, cid, uid)                           # 防突袭计数（按人去重）
                # 入群时间无条件记录：观察期起点与「强制订阅只拦新人」都依赖它，
                # 只在验证开启时才记 → 验证关着时这两项全部静默失效。
                member_joined_at[cid][uid] = time.time()
                if _gate_ok and (sget("JOIN_VERIFY_ENABLED") or _raid_active(cid)):
                    await _join_verify_start(context, cid, uid, name)
    except Exception:
        logger.exception("message 入群事件处理异常（已吞并）")


async def _cleanup_left_member_games(app, cid, uid):
    """⑭ 退群清理：把已退群成员从等待房移除，防止幽灵玩家被开局带上场。

    - 金花/德州 waiting：纯移除（两游戏入房不扣钱，德州 chips 只是只读快照）
    - 21点 waiting：入房时已预扣积分，移除必须原额退款并清 pending（防重启重复退）
    - 进行中对局（betting/playing/open_pending）不动内部结构——各游戏已有回合超时
      （德州/21点超时自动弃牌停牌、金花 open_pending 看门狗自动开牌），不卡局不丢钱。
    全程吞异常：退群清理绝不能拖垮成员事件处理。
    """
    try:
        g = active_jinhua_games.get(cid)
        if g and g.phase == "waiting" and uid in g.players:
            g.players.remove(uid)
            await update_jinhua_waiting(g, app)
            return
        g = active_poker_games.get(cid)
        if g and g.phase == "waiting" and uid in g.players:
            g.players.remove(uid)
            await update_poker_waiting(g, app)
            return
        g = active_blackjack_games.get(cid)
        if g and g.phase == "waiting" and uid in g.players:
            async with wallet_locks[uid]:
                if uid in g.players:
                    g.players.remove(uid)
                    amt = g.bets.pop(uid, 0)
                    if amt:
                        game_chips[cid][uid] += amt   # 与 bj_end 手动终止同一退款语义
                    pending_game_bets[cid].get(uid, {}).pop("21", None)
            await update_blackjack_ui(g, app)
    except Exception:
        logger.exception("退群清理牌局异常（已吞并）")


async def on_member_event(update, context):
    """成员进出事件：退群/入群记录（bot 需为群管理员才能收到）。"""
    _bind_update_cid(update)
    try:
        cmu = update.chat_member
        if not cmu:
            return
        cid = cmu.chat.id
        _inv_dbg(cid, f"[evt] on_member_event 触发 cid={cid}")
        new, old = cmu.new_chat_member, cmu.old_chat_member
        uid, name = new.user.id, new.user.first_name or f"用户{new.user.id}"
        ts = now_bj().strftime("%Y-%m-%d %H:%M")
        if new.status == "left" and old.status != "left":
            leave_records[cid].append({"ts": ts, "uid": uid, "name": name})
            leave_records[cid] = leave_records[cid][-100:]
            rec = invite_records.get(f"{cid}:{uid}")
            if rec: rec["left"] = True   # 邀请记录：退群即失效（不再计入排行）
            join_verify_pending.pop(f"{cid}:{uid}", None)  # 退群清待验证：防幽灵记录（重进可重新验证）
            raid_counted.pop(f"{cid}:{uid}", None)         # 退群清计数：重进算新一次
            await _cleanup_left_member_games(context.application, cid, uid)  # ⑭ 从等待房移除，防幽灵开局
        elif _is_join_transition(new, old):
            leave_records[cid].append({"ts": ts, "uid": uid, "name": name, "join": True})
            leave_records[cid] = leave_records[cid][-100:]
            member_joined_at[cid][uid] = time.time()  # 观察期起点
            _inv_dbg(cid, f"chat_member 进群事件 uid={uid}，事件链接：{(getattr(getattr(cmu, 'invite_link', None), 'link', '') or '（无）')}")
            await _invite_track_join(cmu, cid, uid, name, context)  # 邀请系统追踪（内部自吞异常）
            _gate_ok = True
            if not new.user.is_bot and not is_bot_admin(uid):
                _gate_ok = await _join_gate_check(context, cid, new.user, name)  # 硬门槛：不满足直接移出
                await _raid_on_join(context, cid, uid)                           # 防突袭计数（按人去重）
                if _gate_ok and (sget("JOIN_VERIFY_ENABLED") or _raid_active(cid)):
                    await _join_verify_start(context, cid, uid, name)            # 入群验证（默认关/突袭期强制）
            if sget("WELCOME_ENABLED"):
                try:
                    text = sget("WELCOME_TPL").replace("{name}", name).replace("{group}", getattr(cmu.chat, "title", "") or "").replace("{id}", str(uid))
                    wmsg = await context.bot.send_message(chat_id=cid, text=text)
                    if wmsg and sget("REPLY_DELETE_SECONDS") > 0:
                        schedule_delete(context.application, cid, wmsg, sget("REPLY_DELETE_SECONDS"))
                except TelegramError: pass
        _remember_name(update)
        save_data()
    except Exception:
        logger.exception("成员事件处理异常（已吞并）")

async def on_join_request(update, context):
    """入群申请处理（三路归因，全部不依赖群事件的链接字段可靠性）：
    ① deep-link/按钮 已锁定归因（invite_confirmed）→ 无条件自动批准秒进；
    ② 申请自带链接且命中专属链接 → 存 invite_pending，按 INVITE_AUTO_APPROVE 开关决定是否自动批；
    ③ 都没有（搜群/旧链接进的）→ bot 用 user_chat_id 主动私聊弹邀请人按钮（Bot API 5.5
       文档保证 bot 管理员可主动联系发申请者），点按钮补归因后自动批。"""
    _bind_update_cid(update)
    try:
        req = getattr(update, "chat_join_request", None)
        if req is None and hasattr(update, "from_user") and hasattr(update, "chat"):
            req = update   # 兼容直接传入 request 对象（内部复用/测试）
        if not req:
            return
        cid = req.chat.id
        _inv_dbg(cid, f"[req] on_join_request 触发 cid={cid}")
        uid, name = req.from_user.id, req.from_user.first_name or f"用户{req.from_user.id}"
        join_requests[cid].append({"ts": now_bj().strftime("%Y-%m-%d %H:%M"), "uid": uid, "name": name})
        join_requests[cid] = join_requests[cid][-100:]
        inviter = invite_confirmed.get(f"{cid}:{uid}")
        has_link = bool(getattr(req, "invite_link", None) and getattr(req.invite_link, "link", ""))
        if has_link:
            invite_pending[f"{cid}:{uid}"] = req.invite_link.link   # 归因兜底：批准后的 join 事件可能不带链接
            _inv_dbg(cid, f"入群申请 uid={uid}，已存待归因链接 …{req.invite_link.link[-12:]}")
        else:
            _inv_dbg(cid, f"入群申请 uid={uid}，申请未携带链接（归因{'已锁定 ' + str(inviter) if inviter else '未确认'}）")
        if inviter:
            try:
                await context.bot.approve_chat_join_request(chat_id=cid, user_id=uid)
                _inv_dbg(cid, f"归因已锁定（邀请人 {inviter}）→ 自动批准 uid={uid}")
            except Exception as e:
                _inv_dbg(cid, f"自动批准失败 uid={uid}：{e!r}（转人工）")
        elif not has_link:
            await _invite_ask_inviter(req, cid, uid, name, context)   # 主动问兜底（内部吞异常）
        elif sget("INVITE_AUTO_APPROVE"):
            try:
                await context.bot.approve_chat_join_request(chat_id=cid, user_id=uid)
                _inv_dbg(cid, f"申请带链接 + 开关开 → 自动批准 uid={uid}")
            except Exception as e:
                _inv_dbg(cid, f"自动批准失败 uid={uid}：{e!r}（转人工）")
        save_data()
    except Exception:
        logger.exception("入群申请处理异常（已吞并）")


async def _invite_ask_inviter(req, cid, uid, name, context):
    """主动问兜底：无归因、无链接的入群申请 → bot 主动私聊申请者选邀请人。
    Bot API 5.5+：bot 为群管理员（can_invite_users）时，可主动联系发入群申请的用户
    （user_chat_id，24h 窗口），即使对方从未 /start。全程吞异常，失败不影响申请本身。"""
    try:
        candidates = [(i_uid, info) for i_uid, info in invite_links.get(cid, {}).items()
                      if i_uid != uid and isinstance(info, dict) and info.get("link")]
        if not candidates:
            _inv_dbg(cid, f"[主动问] uid={uid} 本群无邀请人候选，跳过")
            return
        async def _nm(i):
            try: return await get_name(context.application, i, cid=cid)
            except Exception: return f"用户{i}"
        rows, shown = [], 0
        for i_uid, _info in candidates[:8]:
            nm = _nm_r(await _nm(i_uid))
            rows.append([InlineKeyboardButton(f"🎟️ {nm}", callback_data=f"inva_{cid}_{i_uid}_{uid}")])
            shown += 1
        if shown:
            rows.append([InlineKeyboardButton("🚶 我是自己进的（不占邀请名额）",
                                              callback_data=f"inva_none_{cid}_{uid}")])
            await context.bot.send_message(
                chat_id=getattr(req, "user_chat_id", uid),
                text=f"👋 <b>{name}</b> 你好！你申请加入「{chat_name_cache.get(cid) or cid}」。\n\n"
                     f"你是被谁邀请进群的？点一下邀请人（计入 TA 的邀请奖励）：",
                reply_markup=InlineKeyboardMarkup(rows), parse_mode="HTML")
            _inv_dbg(cid, f"[主动问] 已私聊 uid={uid} 选择邀请人（候选 {shown} 人）")
    except Exception as e:
        _inv_dbg(cid, f"[主动问] 私聊 uid={uid} 失败（吞并）：{e!r}")


def _nm_r(n):
    """按钮名压短：去 HTML 敏感字符并截断（callback 按钮 64 字节限制余量留给 data）。"""
    return str(n or "?").replace("<", "‹").replace(">", "›").replace("&", "＆")[:16]



async def season_settle_scheduler(app):
    """独立赛季结算调度：每 60 秒检查一次到点，精确到分钟结算（不再依赖每日 0 点循环，避免最多延迟 ~24h）。"""
    while True:
        try:
            if season_active and now_bj().timestamp() >= season_end_ts:
                await season_settle(app)
        except Exception:
            logger.exception("season_settle_scheduler 本轮异常（已吞并继续，下个周期重试）")
        await asyncio.sleep(60)


def parse_hm(value, def_h, def_m):
    """解析 'HH:MM' 配置；非法回退默认。"""
    try:
        h, mnt = str(value).split(":")
        h, mnt = int(h), int(mnt)
        if 0 <= h < 24 and 0 <= mnt < 60: return h, mnt
    except (ValueError, AttributeError): pass
    return def_h, def_m


async def daily_reset_scheduler(app):
    global last_business_date
    today = now_bj().strftime("%Y-%m-%d")
    # 第一次启动只记录业务日，避免因部署重启立刻重置玩家积分。
    if not last_business_date:
        last_business_date = today; save_data()
    while True:
        now = now_bj()
        rh, rm = parse_hm(sget("DAILY_RESET_TIME"), 0, 0)  # 每轮重读，网页改时间即时生效
        target = now.replace(hour=rh, minute=rm, second=1, microsecond=0)
        if target <= now: target += timedelta(days=1)
        await asyncio.sleep((target-now).total_seconds())
        if not sget("DAILY_RESET_ENABLED"):  # 后台「定时任务」开关：关闭期间到点不执行
            continue
        # 懒填默认：空作用群 = 全授权群
        if not daily_reset_groups: daily_reset_groups.update(AUTHORIZED_GROUPS)
        target_groups = daily_reset_groups & AUTHORIZED_GROUPS
        if not target_groups: continue
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
                season_daily_refresh(day_key, target_groups, season_protected)
                save_data()
            for cid in target_groups:
                _CUR_CID.set(_safe_cid(cid))   # 马匹数量可按群覆盖 → 该群日统计长度按该群解析
                if cid in race_daily_stats: race_daily_stats[cid] = [0] * sget("HORSE_COUNT")
            archive_old_profit_data()
            # 积分系统：清掉前天的聊天积分（保留当天用于跨午夜），过期红包退余款
            chat_today.pop((now_bj() - timedelta(days=2)).strftime("%Y-%m-%d"), None)
            # 兑换排位分的每日累计：只留最近两天，防长期运行后字典无限膨胀
            for _d in [d for d in season_exchange_daily if d < (now_bj() - timedelta(days=1)).strftime("%Y-%m-%d")]:
                season_exchange_daily.pop(_d, None)
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
        now = now_bj()
        lh, lm = parse_hm(sget("LEADERBOARD_TIME"), 23, 50)  # 每轮重读，网页改时间即时生效
        target = now.replace(hour=lh, minute=lm, second=0, microsecond=0)
        if target <= now: target += timedelta(days=1)
        await asyncio.sleep((target-now).total_seconds())
        if not sget("LEADERBOARD_ENABLED"):  # 后台「定时任务」开关：关闭期间到点不推送
            continue
        if not leaderboard_groups: leaderboard_groups.update(AUTHORIZED_GROUPS)
        target_groups = leaderboard_groups & AUTHORIZED_GROUPS
        if not target_groups: continue
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
                if cid not in target_groups: continue  # 只推目标群
                _CUR_CID.set(_safe_cid(cid))
                lines = [f"🏆 德州当日排行榜（{date}）", "━"*14]
                for i, (uid, amount) in enumerate(sorted(data.items(), key=lambda x:x[1], reverse=True)[:50], 1): lines.append(f"{rank_marker(i)} {await get_name(app, uid)}：{amount:+d}")
                await safe_send_long(app.bot, cid, "\n".join(lines))
            # 排位赛每日 23:50 推送「当日盈亏」（当前分 - 基准分，兑换底分不计入）
            if season_active:
                for cid in list(season_points.keys()):
                    if cid not in target_groups: continue  # 只推目标群
                    _CUR_CID.set(_safe_cid(cid))   # 起始分/最低局数按该群配置解析
                    users = season_points.get(cid, {})
                    if not users: continue
                    # 当日盈亏 = 当前分 - (起始分+兑换底分)，与排位榜口径一致（兑换分不计入）
                    day_rows = [(u, val - _season_base(cid, u)) for u, val in users.items()]
                    day_standings = sorted(day_rows, key=lambda x: (-x[1], x[0]))
                    lines = [f"🏆 第{season_id}赛季 当日盈亏榜（基准分 {sget('SEASON_START_CHIPS')}+兑换底分）", "━" * 18]
                    for i, (u, val) in enumerate(day_standings[:50], 1):
                        g = season_games[cid].get(u, 0)
                        tag = "" if g >= sget("SEASON_MIN_GAMES") else f"（{g}局·未达标）"
                        lines.append(f"{rank_marker(i)} {await get_name(app, u, cid=cid, with_title=False)}：{val:+d}｜{g}局{tag}")
                    await safe_send_long(app.bot, cid, "\n".join(lines))
            save_data()
        except Exception:
            logger.exception("leaderboard_scheduler 本轮异常（已吞并继续，下个周期重试）")

async def build_daily_report_text(app, yesterday):
    """经营日报内容拼装（昨日四游戏人次/总流水/盈亏TOP/异常警示/富豪榜）。"""
    games = (("🃏德州", poker_profit_by_date), ("🏎️赛车", race_profit_by_date),
             ("♠️21点", blackjack_profit_by_date), ("♣️炸金花", jinhua_profit_by_date))
    total_flow, net_map, parts = 0, defaultdict(int), []
    for label, prof in games:
        day = prof.get(yesterday, {})
        cnt = sum(1 for chats in day.values() for v in chats.values() if v)
        parts.append(f"{label}{cnt}人次")
        for chats in day.values():
            for uid, v in chats.items(): total_flow += abs(v); net_map[uid] += v
    lines = [f"📊 经营日报（{yesterday}）", "━━━━━━━━━━━━"]
    lines.append("🎮 " + ("｜".join(parts) if total_flow else "昨日无对局"))
    lines.append(f"💰 总流水 {total_flow}")
    winners = sorted(net_map.items(), key=lambda x: -x[1])
    losers = sorted(net_map.items(), key=lambda x: x[1])
    win_parts = []
    for u, v in winners[:3]:
        if v > 0: win_parts.append(f"{await get_name(app, u, with_title=False)} +{v}")
    if win_parts:
        lines.append("🏆 昨日净赢 TOP3：" + "｜".join(win_parts))
    lose_parts = []
    for u, v in losers[:3]:
        if v < 0: lose_parts.append(f"{await get_name(app, u, with_title=False)} {v}")
    if lose_parts:
        lines.append("💸 昨日净亏 TOP3：" + "｜".join(lose_parts))
    alerts = [(u, v) for u, v in winners if v >= max(5000, total_flow * 0.2)]
    if alerts:
        lines.append("🚨 异常警示（单人大额集中赢钱，注意小号对刷）：")
        for u, v in alerts[:3]:
            lines.append(f"　{await get_name(app, u, with_title=False)} 净赢 +{v}（占流水 {v * 100 // max(1, total_flow)}%）")
    lines.append("👑 当前富豪榜：")
    for cid in sorted(AUTHORIZED_GROUPS):
        chips = game_chips.get(cid, {})
        if not chips: continue
        gname = chat_name_cache.get(cid) or str(cid)
        top_parts = []
        for u, v in sorted(chips.items(), key=lambda x: -x[1])[:3]:
            top_parts.append(f"{await get_name(app, u, cid=cid, with_title=False)} {v}")
        lines.append(f"　[{gname}] " + "｜".join(top_parts))
    return "\n".join(lines)


async def admin_report_scheduler(app):
    """经营日报：每天定时把昨日经营数据私聊推送给「配置的目标管理员」（时间网页可配，改完即时生效）。"""
    sent_date = None
    while True:
        now = now_bj()
        rh, rm = parse_hm(sget("ADMIN_REPORT_TIME"), 9, 0)
        target = now.replace(hour=rh, minute=rm, second=0, microsecond=0)
        if target <= now: target += timedelta(days=1)
        await asyncio.sleep(max(1, (target - now).total_seconds()))
        if not sget("ADMIN_REPORT_ENABLED"):  # 后台「定时任务」开关：关闭期间到点不推送
            continue
        if not admin_report_admins: admin_report_admins.add(ADMIN_USER_ID)
        try:
            yesterday = (now_bj() - timedelta(days=1)).strftime("%Y-%m-%d")
            if sent_date == yesterday: continue
            sent_date = yesterday
            text = await build_daily_report_text(app, yesterday)
            for uid in list(admin_report_admins):
                try: await safe_send_long(app.bot, uid, text)
                except Exception as exc: logger.warning("日报推送 %s 失败: %s", uid, exc)
        except Exception:
            logger.exception("admin_report_scheduler 本轮异常（已吞并继续）")

async def _auto_race_tick(app, now):
    """自动开赛单轮扫描：总开关开着且到点时，对每个授权群发车。
    每群默认开启；群里发「整点自动赛车」可单独关/开本群。（此前默认关闭+只遍历手动开过的群，
    网页总开关打开也不会发车——bug 已修）"""
    if not (sget("RACE_AUTO_ENABLED") and sget("RACE_ENABLED")
            and now.minute == max(0, min(59, sget("RACE_HOURLY_MINUTE")))
            and _race_hour_in_window(sget("RACE_HOURLY_START"), sget("RACE_HOURLY_END"), now.hour)):
        return
    for cid in list(AUTHORIZED_GROUPS):
        if not hourly_race_enabled.get(cid, True):
            race_skip_stats[cid]["群开关关闭"] += 1; continue
        if cid in active_horse_races:
            race_skip_stats[cid]["已有进行中赛车"] += 1; continue
        try:
            mode = current_game_mode()
            jackpot = race_jackpot.get(cid, 0) if mode == "official" else 0
            race = HorseRace(cid, ADMIN_USER_ID, jackpot, mode, auto=True); active_horse_races[cid] = race
            msg = await safe_send(app.bot, cid, await race.view(app), reply_markup=race.buttons())
            if not msg:
                race_skip_stats[cid]["safe_send返回None"] += 1
                active_horse_races.pop(cid, None); continue
            race.game_msg_id = msg.message_id
            race.task = asyncio.create_task(race.run(app))
            race_last_sent[cid] = now.strftime("%Y-%m-%d %H:%M")
            save_data()
        except Exception as exc:
            logger.exception(f"自动开赛 群 {cid} 异常")
            race_skip_stats[cid][f"异常:{type(exc).__name__}"] += 1
            active_horse_races.pop(cid, None)


async def hourly_race_scheduler(app):
    last_key = None
    while True:
        try:
            now = now_bj(); key = now.strftime("%Y%m%d%H")
            if key != last_key:  # 每分钟轮询，同一小时只发一轮；开赛分钟/时段均网页可配
                await _auto_race_tick(app, now)
                if sget("RACE_AUTO_ENABLED") and now.minute == max(0, min(59, sget("RACE_HOURLY_MINUTE"))):
                    last_key = key
            next_minute = (now + timedelta(minutes=1)).replace(second=0, microsecond=0)
            await asyncio.sleep(max(1, (next_minute-now).total_seconds()))
        except Exception:
            logger.exception("hourly_race_scheduler 本轮异常（已吞并继续）")
            await asyncio.sleep(60)


# ---------- 定时任务调试 ----------
async def cmd_schedule_status(update, context):
    """管理员一键打印所有调度任务状态 + 每群最近推送。"""
    uid = update.effective_user.id if update.effective_user else 0
    if not is_bot_admin(uid):
        await send_reply(update, context, "⛔ 仅管理员可用。"); return
    now = now_bj()
    lines = ["<b>🕐 定时任务状态</b>", ""]

    # 1) 整点赛车
    lines.append(f"<b>1️⃣ 整点自动赛车</b>　总开关：{'✅ 开' if sget('RACE_AUTO_ENABLED') and sget('RACE_ENABLED') else '❌ 关'}　时段：{_race_window_text(sget('RACE_HOURLY_START'), sget('RACE_HOURLY_END'))}　开赛分钟：{sget('RACE_HOURLY_MINUTE'):02d} 分")
    if AUTHORIZED_GROUPS:
        for cid in sorted(AUTHORIZED_GROUPS):
            on = "✅" if hourly_race_enabled.get(cid, True) else "⏸"
            last = race_last_sent.get(cid) or "（暂无记录）"
            skips = race_skip_stats.get(cid, {})
            skip_txt = ""
            if skips:
                items = ", ".join(f"{k}×{v}" for k, v in skips.items())
                skip_txt = f"　跳过：{items}"
            lines.append(f"　{on} <code>{cid}</code> {html.escape(chat_name_cache.get(cid) or str(cid))}　最近推送：{last}{skip_txt}")
    else:
        lines.append("　（无授权群）")
    lines.append("")

    # 2) 每日重置
    lines.append(f"<b>2️⃣ 每日重置</b>　时刻：{sget('DAILY_RESET_TIME')}　上次业务日：{last_business_date or '（未记录）'}")
    lines.append("")

    # 3) 自动备份
    jq = getattr(context.application, "job_queue", None)
    if jq is not None:
        lines.append(f"<b>3️⃣ 自动备份</b>　间隔：{sget('BACKUP_INTERVAL_HOURS')} 小时　job_queue：✅ 运行中")
    else:
        lines.append(f"<b>3️⃣ 自动备份</b>　间隔：{sget('BACKUP_INTERVAL_HOURS')} 小时　job_queue：❌ 未启用（需 python-telegram-bot[job-queue]）")
    lines.append("")

    # 4) 赛季结算
    if season_active:
        end_str = time.strftime("%Y-%m-%d %H:%M", time.localtime(season_end_ts))
        lines.append(f"<b>4️⃣ 赛季结算</b>　当前赛季：<b>{html.escape(season_name)}</b>（ID {season_id}）　结束：{end_str}")
    else:
        lines.append("<b>4️⃣ 赛季结算</b>　无进行中的赛季")
    lines.append("")

    lines.append(f"⏱ 当前时间：{now.strftime('%Y-%m-%d %H:%M:%S')}")
    await send_reply(update, context, "\n".join(lines))


# ---------- 数据备份/恢复 ----------
async def cmd_backup(update, context):
    """管理员备份：把数据文件发送到管理员私聊。"""
    uid = update.effective_user.id
    if not is_bot_admin(uid):
        await send_reply(update, context, "⛔ 仅管理员可用")
        return
    # 强制写盘，确保文件是最新的
    ok = await asyncio.to_thread(force_save_now)
    if not ok:
        await send_reply(update, context, "⚠️ 写盘失败，请稍后再试")
        return
    if not os.path.exists(DATA_FILE):
        await send_reply(update, context, "⚠️ 数据文件不存在")
        return
    # 拆开 try：把「数据文件发送」单独包，失败时把真实异常返回给管理员；
    # 之前一个大 try 吞所有，群内 /backup 失败只会看到「请先 /start」这种误导性提示。
    try:
        with open(DATA_FILE, "rb") as f:
            data_bytes = f.read()
        await context.bot.send_document(
            chat_id=uid,
            document=data_bytes,
            filename=f"bot_backup_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json",
            caption="📦 数据备份完成（此文件内含网页设置快照，恢复数据即恢复设置）",
        )
    except Exception as exc:
        logger.exception("数据备份发送失败")
        await send_reply(update, context, 
            f"⚠️ 数据备份失败：{type(exc).__name__}: {str(exc)[:200]}\n"
            f"请把这条错误发我排查（常见原因：私聊未 /start、容器磁盘满、文件被另一进程锁定）"
        )
        return
    # 同时发一份纯设置备份，便于「只恢复设置、保留现有数据」
    if os.path.exists(SETTINGS_FILE):
        try:
            with open(SETTINGS_FILE, "rb") as f:
                cfg_bytes = f.read()
            await context.bot.send_document(
                chat_id=uid, document=cfg_bytes,
                filename=f"bot_settings_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json",
                caption="⚙️ 网页设置备份（只需恢复设置：回复此文件发 /restore）",
            )
        except Exception as exc:
            logger.exception("设置备份发送失败")
            # 数据备份已成功，设置备份失败只是少一个文件，不影响主流程
            await send_reply(update, context, 
                f"⚠️ 设置备份失败：{type(exc).__name__}: {str(exc)[:160]}"
            )
    # 在群里发的命令时，提示一下文件已发到私聊
    if update.effective_chat.id != uid:
        await send_reply(update, context, "✅ 备份文件已发送到你的私聊")


async def cmd_restore(update, context):
    """管理员恢复：回复一个 JSON 备份文件来恢复数据，直接载入内存立即生效（不依赖平台重启）。"""
    global data_dirty
    uid = update.effective_user.id
    if not is_bot_admin(uid):
        await send_reply(update, context, "⛔ 仅管理员可用")
        return
    replied = update.message.reply_to_message
    if not replied or not replied.document:
        await send_reply(update, context, "⚠️ 请回复一个 JSON 备份文件，再发送 /restore\n\n用法：点开备份文件 → 回复 → 发送 /restore")
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
        # 设置备份文件（顶层是 fields/web_password，没有 game_chips）→ 只恢复设置，不动积分数据
        if "fields" in data and "game_chips" not in data:
            try:
                os.remove(tmp_path)
            except Exception:
                pass
            try:
                _write_settings_file(data.get("fields", {}),
                                     data.get("web_password") or "",   # 新格式备份没有明文，空=不动凭据
                                     data.get("cmd_aliases") or {}, data.get("tg_menu") or [])
                load_settings()
                await asyncio.to_thread(force_save_now)
                await send_reply(update, context, "\n".join([
                    "✅ 网页设置恢复成功，已立即生效",
                    "━━━━━━━━━━━━━━━",
                    f"⚙️ 恢复设置项：{len(data.get('fields', {}))} 项",
                    "",
                    "本次只恢复设置，积分与数据未改动。",
                ]))
                logger.warning("管理员 %s 恢复了网页设置", uid)
            except Exception:
                logger.exception("设置恢复失败")
                await send_reply(update, context, "⚠️ 设置恢复失败，文件可能已损坏")
            return
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
        # 一并还原网页设置：备份里内嵌了设置快照，恢复数据即恢复设置，
        # 避免重新部署后网页设置回退成代码默认值。
        try:
            embedded = data.get("_settings")
            if isinstance(embedded, dict) and embedded.get("fields"):
                SETTINGS_SNAPSHOT.clear(); SETTINGS_SNAPSHOT.update(embedded)
                apply_settings(embedded.get("fields", {}))
                ca = embedded.get("cmd_aliases") or {}
                if isinstance(ca, dict):
                    CMD_ALIAS_OVERRIDES.clear()
                    CMD_ALIAS_OVERRIDES.update({str(k): str(v) for k, v in ca.items()})
                tm = embedded.get("tg_menu") or []
                if isinstance(tm, list) and tm:
                    TG_MENU.clear()
                    TG_MENU.extend([list(x) for x in tm if isinstance(x, (list, tuple)) and len(x) == 2])
                apply_command_aliases()
                _write_settings_file(embedded.get("fields", {}),
                                     embedded.get("web_password") or "",   # 空=不动凭据，避免把密码打回默认
                                     embedded.get("cmd_aliases") or {}, embedded.get("tg_menu") or [])
                logger.warning("数据恢复：已一并还原网页设置（%s 项）", len(embedded.get("fields", {})))
        except Exception:
            logger.exception("数据恢复：设置还原失败")
        # 恢复摘要：一眼确认恢复成没成功，不用再翻 /列表
        try:
            all_players = {u for users in list(game_chips.values()) for u in users}
            game_total = sum(sum(users.values()) for users in list(game_chips.values()))
            await send_reply(update, context, "\n".join([
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
            await send_reply(update, context, "✅ 数据恢复成功，已立即生效（无需重启）")
        logger.warning("管理员 %s 执行了数据恢复，已直接载入内存", uid)
    except json.JSONDecodeError:
        await send_reply(update, context, "⚠️ 文件不是有效的 JSON 格式，恢复已取消")
        if os.path.exists(tmp_path):
            os.remove(tmp_path)
    except Exception as e:
        logger.exception("恢复失败")
        await send_reply(update, context, f"⚠️ 恢复失败：{e}")
        if os.path.exists(tmp_path):
            os.remove(tmp_path)


# Telegram 原生 / 菜单（网页「命令管理」页可改，存 bot_settings.json 的 tg_menu；命令仅限英文小写/数字/下划线）
DEFAULT_TG_MENU = [
    ("start", "开始"), ("help", "功能帮助"), ("dz", "德州扑克"), ("sc", "赛车"), ("21", "21点"), ("mylv", "我的等级"), ("jifen", "积分兑换"),
    ("jinhua", "炸金花"), ("sign", "每日签到"), ("mypoints", "我的积分"), ("mall", "积分商城"),
    ("end", "结束当前游戏"), ("add", "加/减积分(正加负减)"), ("cx", "盈亏查询"), ("ph", "排行榜"),
    ("sq", "授权群组"), ("qxsh", "取消授权"), ("addadmin", "添加机器人管理员"), ("deladmin", "移除机器人管理员"),
    ("adminlist", "查看管理员列表"), ("authlist", "查看已授权群"), ("autosm", "切换整点自动赛车"),
    ("backup", "备份数据"), ("restore", "恢复数据"), ("season", "德州排位赛"), ("seasonjoin", "排位报名"),
    ("seasonrank", "排位榜"), ("seasonhelp", "排位赛帮助"), ("seasonstart", "排位强制开赛(管理员)"),
    ("seasonend", "排位提前结算(管理员)"), ("god", "赌神称号/荣誉墙"), ("godgrant", "封赌神(管理员)"),
    ("godrevoke", "撤赌神(管理员)"), ("shop", "积分商店-称号兑换"), ("redeem", "兑换称号"),
    ("mytitles", "查看我的称号"), ("equip", "佩戴称号"), ("seasonpoints", "加减排位分(管理员)"),
    ("ban", "拉黑玩家(管理员)"), ("unban", "解封玩家(管理员)"), ("banlist", "查看黑名单(管理员)"),
    ("list", "管理总览(管理员/群/黑名单)"),
    ("record", "个人战绩"), ("status", "机器人自检(管理员)"),
]
TG_MENU = [list(t) for t in DEFAULT_TG_MENU]

async def post_init(app):
    global _bot_app, _bot_loop, _BOT_USERNAME
    _bot_app, _bot_loop = app, asyncio.get_running_loop()  # 供网页后台跨线程调用 bot API（入群批准/拒绝等）
    # 兑换按钮深链需要 bot 用户名（https://t.me/<用户名>?start=...）；启动时缓存
    try:
        _me = await app.bot.get_me()
        _BOT_USERNAME = (_me.username or "").lstrip("@")
    except Exception:
        _BOT_USERNAME = ""
    background_tasks.update({
        asyncio.create_task(daily_reset_scheduler(app)),
        asyncio.create_task(leaderboard_scheduler(app)),
        asyncio.create_task(season_settle_scheduler(app)),
        asyncio.create_task(hourly_race_scheduler(app)),
        asyncio.create_task(admin_report_scheduler(app)),
        asyncio.create_task(lottery_scheduler(app)),
        asyncio.create_task(data_save_worker())
    })
    background_tasks.add(asyncio.create_task(_warm_group_names(app)))   # 群名预热：网页/推送不再显示裸群ID
    # 待删消息队列：重放上次没删完的（重部署不再残留游戏面板）+ 每 60 秒兜底 flush 一轮
    try:
        restore_pending_deletes(app)
        async def _delete_sweeper():
            while True:
                await asyncio.sleep(60)
                try: await _flush_deletes(app)
                except Exception: pass
        background_tasks.add(asyncio.create_task(_delete_sweeper()))
    except Exception:
        logger.exception("待删消息队列恢复失败（不影响主功能）")
    # 重启恢复：竞猜：未封盘且未到点的重建封盘倒计时；已封盘的原样等待结算
    for _cid, _g in list(guesses.items()):
        if not _g.get("locked") and not _g.get("task") and _g["end_ts"] > now_bj().timestamp():
            try: _g["task"] = asyncio.create_task(_guess_close(_cid, app))
            except Exception: pass
    # 注册 Telegram 原生命令菜单（仅支持拉丁字符命令，中文命令走自定义路由）。
    # 作用：群里打 / 能看到、能点；命令以 bot_command 实体发送，不受隐私模式影响，必定送达。
    # 菜单内容在「命令管理」页可改，存 bot_settings.json 的 tg_menu。
    try:
        menu = [BotCommand(c, d) for c, d in TG_MENU]
        await app.bot.set_my_commands(menu)
    except Exception:
        logger.warning("注册命令菜单失败（不影响主功能）")
    # 全新部署检测：容器重建会清空 bot_settings.json，数据里也没有快照时，
    # 主动私聊提醒管理员恢复设置，避免「设置莫名回退成默认值」却没人知道。
    try:
        if not SETTINGS_SNAPSHOT:
            await app.bot.send_message(
                chat_id=ADMIN_USER_ID,
                text="⚠️ 检测到全新部署：网页后台的设置已回退为代码默认值。\n\n"
                     "恢复方法（二选一）：\n"
                     "1️⃣ 回复最近一份「⚙️ 网页设置备份」文件 → 发送 /restore\n"
                     "2️⃣ 回复「🤖 每日自动备份」数据文件 → 发送 /restore（设置已内嵌在数据里）\n\n"
                     "要重新配置的话，忽略本条即可。",
            )
    except Exception:
        logger.warning("全新部署提醒发送失败（不影响运行）")


async def post_shutdown(app):
    force_save_now()


# 命令路由：支持中文命令（Telegram 命令菜单只认拉丁字符，故用 MessageHandler 解析 /中文）
CMD_ALIASES = {
    # 中文命令
    "开始": cmd_start, "菜单": cmd_help, "帮助": cmd_help, "help": cmd_help,
    "德州": cmd_dz, "德州扑克": cmd_dz,
    "赛车": cmd_sm, "sc": cmd_sm, "赛马": cmd_sm,
    "21点": cmd_21, "二十一点": cmd_21,
    "结束": cmd_end, "终止": cmd_end, "结束游戏": cmd_end, "终止游戏": cmd_end, "终止比赛": cmd_end,
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
    "adminlist": cmd_admin_list,
    "备份": cmd_backup,
    "恢复": cmd_restore,
    "炸金花": cmd_jinhua, "jinhua": cmd_jinhua, "zjh": cmd_jinhua, "金花": cmd_jinhua,
    "大话骰": cmd_dice, "大話骰": cmd_dice, "吹牛": cmd_dice, "摇骰": cmd_dice,
    "签到": cmd_sign, "每日签到": cmd_sign, "签到排行": cmd_sign_rank,
    "我的积分": cmd_my_points, "积分排行": cmd_points_rank, "我的等级": cmd_my_level, "积分兑换": cmd_points_redeem, "jifen": cmd_points_redeem,
    "积分商城": cmd_mall, "商城": cmd_mall, "购买": cmd_mall_buy,
    "红包": cmd_redpacket, "发红包": cmd_redpacket,
    "战绩": cmd_record, "个人战绩": cmd_record, "record": cmd_record,
    "自检": cmd_status, "运行状态": cmd_status, "status": cmd_status,
    "网页码": cmd_webcode, "验证码": cmd_webcode, "登录码": cmd_webcode, "webcode": cmd_webcode,
    "开奖": cmd_lottery, "抽奖": cmd_lottery, "lottery": cmd_lottery,
    "后台": cmd_weblogin, "登录后台": cmd_weblogin, "后台登录": cmd_weblogin, "weblogin": cmd_weblogin,
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
    "兑换排位": cmd_season_exchange, "排位兑换": cmd_season_exchange, "积分换排位": cmd_season_exchange,
    "兑换排位分": cmd_season_exchange, "seasonexchange": cmd_season_exchange,
    # 2026-09-10 用户指定：聊天积分→排位分 的主推触发词（更好记）
    "游戏积分兑换": cmd_season_exchange, "游戏积分换排位": cmd_season_exchange, "排位分兑换": cmd_season_exchange,
    # 旧英文/数字别名（保留兼容，仍可用）
    "start": cmd_start, "help": cmd_help, "dz": cmd_dz, "sm": cmd_sm,
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
    "放行": cmd_jv_pass, "验证放行": cmd_jv_pass, "jvpass": cmd_jv_pass,
    "白名单": cmd_whitelist, "加白": cmd_whitelist_add, "删白": cmd_whitelist_del,
    "群管理员": cmd_adminlist_tg, "admins": cmd_adminlist_tg,
    "转赠": cmd_inherit, "继承": cmd_inherit, "转让": cmd_inherit, "transfer": cmd_inherit,
    "开竞猜": cmd_guess_open, "guess": cmd_guess_open,
    "竞猜结算": cmd_guess_settle, "竞猜撤销": cmd_guess_cancel,
    "充值": cmd_buy_points, "购买积分": cmd_buy_points, "topup": cmd_buy_points,
    "link": cmd_invite_link, "邀请链接": cmd_invite_link, "邀请": cmd_invite_link,
    "my_invite": cmd_my_invite, "我的邀请": cmd_my_invite, "邀请进度": cmd_my_invite,
    "invite_debug": cmd_invite_debug, "邀请调试": cmd_invite_debug,
    "invite_test": cmd_invite_test, "测试邀请": cmd_invite_test, "邀请自测": cmd_invite_test,
    "invite_report": cmd_invite_report, "报备入群": cmd_invite_report, "邀请报备": cmd_invite_report,
    "schedule_status": cmd_schedule_status, "定时任务": cmd_schedule_status, "调度状态": cmd_schedule_status,
    "流水": cmd_points_flow, "积分流水": cmd_points_flow,
    "今日邀请排行": cmd_invite_rank_today, "本月邀请排行": cmd_invite_rank_month, "总邀请排行": cmd_invite_rank_all,
}
# 动态指令接管默认名：网页改指令后，旧默认名同步失效
_DYN_CMD_OWNED.update({"QUERY_CMD": "我的积分", "SIGN_CMD": "签到", "RANK_CMD": "积分排行",
                       "INVITE_LINK_CMD": "link", "INVITE_RANK_TODAY_CMD": "今日邀请排行",
                       "INVITE_RANK_MONTH_CMD": "本月邀请排行", "INVITE_RANK_ALL_CMD": "总邀请排行"})

# ---------- 命令管理：别名覆盖层（网页「命令管理」页编辑，保存立即生效） ----------
BASE_CMD_ALIASES = dict(CMD_ALIASES)   # 出厂别名基线（只读）
_HANDLERS_BY_NAME = {}
for _fn in set(BASE_CMD_ALIASES.values()):
    _HANDLERS_BY_NAME[_fn.__name__] = _fn
CMD_ALIAS_OVERRIDES = {}               # 处理函数名 -> "别名1,别名2,..."

_CMD_FACTORY_DEFAULTS = {"QUERY_CMD": "我的积分", "SIGN_CMD": "签到", "RANK_CMD": "积分排行",
                         "LEVEL_CMD": "我的等级", "REDEEM_CMD": "积分兑换",
                         "INVITE_LINK_CMD": "link", "INVITE_RANK_TODAY_CMD": "今日邀请排行",
                         "INVITE_RANK_MONTH_CMD": "本月邀请排行", "INVITE_RANK_ALL_CMD": "总邀请排行"}

def _sync_cmd_globals_from_aliases():
    """指令名单一真源：网页「命令管理」改了触发词，帮助文案里的指令名同步跟着变。

    之前 QUERY_CMD/SIGN_CMD 等既是设置项又在命令管理页可改，两处各说各话，
    改了页面里显示的还是旧词。现在设置项已下线，统一以命令管理的别名为准。
    """
    for gname, fn in (("QUERY_CMD", cmd_my_points), ("SIGN_CMD", cmd_sign), ("RANK_CMD", cmd_points_rank),
                      ("LEVEL_CMD", cmd_my_level), ("REDEEM_CMD", cmd_points_redeem),
                      ("INVITE_LINK_CMD", cmd_invite_link), ("INVITE_RANK_TODAY_CMD", cmd_invite_rank_today),
                      ("INVITE_RANK_MONTH_CMD", cmd_invite_rank_month), ("INVITE_RANK_ALL_CMD", cmd_invite_rank_all)):
        override = CMD_ALIAS_OVERRIDES.get(fn.__name__)
        names = [a.strip() for a in str(override or "").replace("，", ",").split(",") if a.strip()]
        if not names:
            base_names = sorted(a for a, f in BASE_CMD_ALIASES.items() if f is fn)
            d = _CMD_FACTORY_DEFAULTS.get(gname)   # 出厂默认优先（中文指令比英文别名更贴近用户认知）
            names = [d] if d in base_names else base_names[:1]
        if names:
            globals()[gname] = names[0]


def cmd_conflicts():
    """触发词冲突体检：同一个触发词被多个命令占用时，后注册者会顶掉前者（表现为某命令莫名失效）。

    返回 [(触发词, [命令函数, ...])]，按触发词排序；无冲突返回空列表。命令管理页顶部展示。
    """
    parsed = {}
    for fn_name, alias_str in CMD_ALIAS_OVERRIDES.items():
        if fn_name not in _HANDLERS_BY_NAME:
            continue
        aliases = [a.strip() for a in str(alias_str).replace("，", ",").split(",") if a.strip()]
        if aliases:
            parsed[fn_name] = aliases
    owner = {}
    for alias, fn in BASE_CMD_ALIASES.items():
        if fn.__name__ in parsed:
            continue                      # 被覆盖的命令其出厂触发词已整体失效
        owner.setdefault(alias, set()).add(fn.__name__)
    for fn_name, aliases in parsed.items():
        for a in aliases:
            owner.setdefault(a, set()).add(fn_name)
    return sorted((a, sorted(fns)) for a, fns in owner.items() if len(fns) > 1)


def apply_command_aliases():
    """重建命令分发表：出厂别名 + 网页覆盖层 + QUERY/SIGN/RANK 动态名。
    某命令有非空覆盖时，其出厂触发词整体失效（覆盖即替换）；覆盖为空则恢复出厂。"""
    CMD_ALIASES.clear()
    parsed = {}
    for fn_name, alias_str in CMD_ALIAS_OVERRIDES.items():
        if fn_name not in _HANDLERS_BY_NAME: continue
        aliases = [a.strip() for a in str(alias_str).replace("，", ",").split(",") if a.strip()]
        if aliases: parsed[fn_name] = aliases
    overridden_fns = {_HANDLERS_BY_NAME[fn_name] for fn_name in parsed}
    for alias, fn in BASE_CMD_ALIASES.items():
        if fn in overridden_fns: continue
        CMD_ALIASES[alias] = fn
    for fn_name, aliases in parsed.items():
        fn = _HANDLERS_BY_NAME[fn_name]
        for a in aliases: CMD_ALIASES[a] = fn
    _sync_cmd_globals_from_aliases()   # 帮助文案里的指令名跟随网页改动（单一真源）
    _sync_dyn_aliases()

async def _dispatch_alias(cmd, args, update, context):
    """根据命令别名（无论带不带 /）分发到对应处理函数，并填充 context.args。
    命中已知命令后，按 POINTS_DELETE_SECONDS 自动删除用户发的命令消息（全局，群聊限定）。"""
    handler = CMD_ALIASES.get(cmd)
    if not handler:
        await send_reply(update, context, "❓ 未知命令，发送 /开始 查看可用命令")
        return
    context.args = args
    # 抽奖相关消息（参与关键词/开奖命令）不删：参与痕迹与开奖信息都要保留在群里
    if sget("POINTS_DELETE_SECONDS") > 0 and handler is not cmd_lottery and is_group_chat(update):
        schedule_delete(context.application, update.effective_chat.id, update.message, sget("POINTS_DELETE_SECONDS"))
    await handler(update, context)


async def route_command(update, context):
    """把 /中文 或 /英文 命令路由到对应处理函数。"""
    _bind_update_cid(update)
    if not update.message or not update.message.text:
        return
    _remember_name(update)
    # 拉黑拦截：被封禁用户（非管理员）禁止使用全部命令
    if update.effective_user.id in BLACKLISTED_USERS and not is_bot_admin(update.effective_user.id):
        await send_reply(update, context, "🚫 你已被禁止使用本机器人，如有疑问请联系管理员。"); return
    parts = update.message.text.strip().split()
    if not parts or not parts[0].startswith("/"):
        return
    cmd = parts[0][1:]
    if "@" in cmd:
        cmd = cmd.split("@", 1)[0]
    await _dispatch_alias(cmd, parts[1:], update, context)


# ---------- 云平台保活 + 云端持久化（Render / Zeabur 等无持久磁盘的平台用）----------
def _parse_multipart(raw, content_type):
    """极简 multipart/form-data 解析（积分导入文件上传用）。
    返回 {字段名: 字符串值 或 (文件名, bytes)}。"""
    m = re.search(r'boundary="?([^";]+)"?', content_type or "")
    if not m: return {}
    boundary = ("--" + m.group(1)).encode()
    fields = {}
    for part in raw.split(boundary):
        part = part.strip(b"\r\n")
        if not part or part in (b"--", b"--\r\n"): continue
        if b"\r\n\r\n" not in part: continue
        head, _, value = part.partition(b"\r\n\r\n")
        headers = head.decode("utf-8", "replace")
        name = re.search(r'name="([^"]*)"', headers)
        fname = re.search(r'filename="([^"]*)"', headers)
        key = name.group(1) if name else ""
        if not key: continue
        if fname and fname.group(1):
            fields[key] = (fname.group(1), value[:-2] if value.endswith(b"\r\n") else value)
        else:
            fields[key] = value.decode("utf-8", "replace")
    return fields


def _parse_points_rows(data, filename):
    """把上传文件解析为 [(uid, points, nickname)]。支持 CSV(utf-8/gbk) 与 xlsx(需 openpyxl)。
    返回 (rows, err)；err 非 None 表示失败。表头行自动识别，列按表头定位（缺省 用户ID=0列,积分=2列）。"""
    rows_raw = None
    if filename.lower().endswith((".xlsx", ".xls")):
        try:
            import io as _io
            from openpyxl import load_workbook
        except ImportError:
            return None, "服务器未安装 openpyxl，无法读 Excel：请把表格另存为 CSV(逗号分隔) 再导入"
        try:
            wb = load_workbook(_io.BytesIO(data), read_only=True, data_only=True)
            rows_raw = [[("" if cell is None else str(cell.value)) for cell in row] for row in wb.active.iter_rows()]
        except Exception as exc:
            return None, f"Excel 解析失败：{exc}"
    else:
        text = None
        for enc in ("utf-8-sig", "utf-8", "gbk"):
            try: text = data.decode(enc); break
            except (UnicodeDecodeError, LookupError): continue
        if text is None: return None, "无法识别文件编码（请用 UTF-8 或 GBK 编码的 CSV）"
        rows_raw = [line.split(",") for line in text.splitlines() if line.strip()]
    if not rows_raw: return None, "文件内容为空"
    idx_uid, idx_pts, idx_name = 0, 2, 1
    start = 0
    header = [h.strip().strip('"').lower() for h in rows_raw[0]]
    if any("用户id" in h for h in header):
        start = 1
        for i, h in enumerate(header):
            if "用户id" in h: idx_uid = i
            elif h == "积分": idx_pts = i
            elif "昵称" in h or "用户名" in h: idx_name = i
    rows, skipped = [], 0
    for row in rows_raw[start:]:
        cells = [c.strip().strip('"') for c in row] + ["", "", ""]
        try:
            uid, pts = int(cells[idx_uid]), int(float(cells[idx_pts]))
        except (ValueError, IndexError):
            skipped += 1; continue
        if pts < 0: skipped += 1; continue
        rows.append((uid, pts, cells[idx_name] if idx_name < len(cells) else ""))
    return (rows, skipped), None


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
        login_fails = {}  # ip -> [连续失败次数, 锁定截止时间戳]（防爆破：连续错 5 次锁 10 分钟）
        otp_fails = {}    # ip -> [连续验证码错误次数, 锁定截止]

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
            _gcid = cur_cid()                                        # 当前正在配置的群（0=全局默认）
            _gact = ("/page/" + sidebar_active) if sidebar_active else "/page/dashboard"
            _gq = (f"?cid={_gcid}" if _gcid else "")                 # 左侧菜单链接带上群，切页不串台
            _gbanner = ("" if not _gcid else
                        "<div style='margin:0 0 14px;padding:10px 14px;border-radius:10px;"
                        "background:rgba(var(--acr),.12);border:1px solid rgba(var(--acr),.3);font-size:13px;"
                        "color:#d9d3f0'>🏷 正在为 <b>" + html.escape(chat_name_cache.get(_gcid) or "该群")
                        + "</b>（<b>" + str(_gcid) + "</b>）配置 · 只保存与该群不同的项，"
                        "未单独设置的项自动继承全局默认；标有「⚑ 群专属」的项才是该群已覆盖的</div>")
            # 群级页面：给所有 /save 表单自动补一个 cid 隐藏字段，保存才知道往哪个群写
            # （表单有十几处手写，逐个加容易漏；这里用一次 JS 统一注入，零遗漏）
            _gjs = ("<script>var _GCID=" + str(_gcid) + ";"
                    "document.addEventListener('DOMContentLoaded',function(){if(!_GCID)return;"
                    "document.querySelectorAll(\"form[action='/save']\").forEach(function(f){"
                    "if(f.querySelector(\"input[name='cid']\"))return;"
                    "var i=document.createElement('input');i.type='hidden';i.name='cid';i.value=_GCID;"
                    "f.appendChild(i);});});</script>")
            _thm_key = SETTINGS_SNAPSHOT.get("ui_theme") if SETTINGS_SNAPSHOT.get("ui_theme") in _UI_THEMES else "purple"
            _ac, _ac2, _actx, _bg, _side, _card, _input, _border, _thead, _hover = _UI_THEMES[_thm_key]
            _acr = ",".join(str(int(_ac[i:i + 2], 16)) for i in (1, 3, 5))   # 主色的 R,G,B（供 rgba(var(--acr),x)）
            _bgr = ",".join(str(int(_card[i:i + 2], 16)) for i in (1, 3, 5))  # 卡片底色的 R,G,B（玻璃条用）
            items = []
            child_of = {ck: pk for pk, cks in SIDEBAR_CHILDREN.items() for ck in cks}
            meta = {g[0]: (g[1], g[2]) for g in SETTINGS_GROUPS}

            def _render_group(gkey):
                name, icon = meta.get(gkey, (gkey, "•"))
                active_now = sidebar_active == gkey or sidebar_active.startswith(gkey + "/")
                subpage_subs = SUBPAGES.get(gkey) or []
                child_groups = [(ck, meta.get(ck, (ck, "•"))) for ck in SIDEBAR_CHILDREN.get(gkey, [])]
                if subpage_subs or child_groups:
                    subs = []
                    # 父组只有"挂子组"（如德州挂排位赛）而无自身子页时，父组菜单变折叠开关，
                    # 原设置页会失去入口 → 子菜单第一位固定补"XX设置"链接
                    if not subpage_subs and child_groups:
                        pcls = "active" if sidebar_active == gkey else ""
                        subs.append(f"<a class='{pcls}' href='/page/{gkey}{_gq}'>⚙️ {name}设置</a>")
                    for skey, sname in subpage_subs:
                        cls = "active" if sidebar_active == f"{gkey}/{skey}" else ""
                        subs.append(f"<a class='{cls}' href='/page/{gkey}/{skey}{_gq}'>{sname}</a>")
                    for ck, (cname, cicon) in child_groups:
                        ccls = "active" if sidebar_active == ck or sidebar_active.startswith(ck + "/") else ""
                        subs.append(f"<a class='{ccls}' href='/page/{ck}{_gq}'>{cname}</a>")
                    items.append(
                        f"<details{' open' if active_now else ''}>"
                        f"<summary class='{'active' if active_now else ''}'>{icon}<span>{name}</span></summary>"
                        f"<div class='sub'>{''.join(subs)}</div></details>")
                else:
                    cls = "item active" if active_now else "item"
                    items.append(f"<a class='{cls}' href='/page/{gkey}{_gq}'>{icon}<span>{name}</span></a>")

            def _sec_sort(keys):
                ks = [k for k in keys if k in meta and k not in child_of]
                ks.sort(key=lambda k: SIDEBAR_ORDER.index(k) if k in SIDEBAR_ORDER else 999)
                if "dashboard" in ks:  # 群体总览固定第一
                    ks.remove("dashboard"); ks.insert(0, "dashboard")
                return ks

            rendered = set()
            for sec_name, sec_keys in SIDEBAR_SECTIONS:
                ks = _sec_sort(sec_keys)
                if not ks: continue
                items.append(f"<div class='grp-title'>{sec_name}</div>")
                for k in ks:
                    _render_group(k); rendered.add(k)
            others = [g[0] for g in SETTINGS_GROUPS if g[0] not in child_of and g[0] not in rendered]
            if others:
                items.append("<div class='grp-title'>其他</div>")
                for k in others: _render_group(k)
            return ("<!DOCTYPE html><html lang='zh'><head><meta charset='utf-8'>"
                    "<meta name='viewport' content='width=device-width, initial-scale=1'>"
                    f"<title>{title} - 机器人后台</title><style>"
                    f":root{{--ac:{_ac};--ac2:{_ac2};--acr:{_acr};--ac-tx:{_actx};"
                    f"--bg:{_bg};--side:{_side};--card:{_card};--input:{_input};"
                    f"--border:{_border};--thead:{_thead};--hover:{_hover};--bgr:{_bgr}}}"
                    "*{box-sizing:border-box}"
                    "html,body{height:100%}"
                    "body{background:radial-gradient(1100px 520px at 85% -8%,rgba(var(--acr),.10),transparent 60%),"
                    "radial-gradient(900px 500px at -10% 110%,rgba(var(--acr),.06),transparent 55%),var(--bg);"
                    "color:#e8e6f2;font-family:system-ui,'PingFang SC','Microsoft YaHei',sans-serif;"
                    "margin:0;font-size:16px;-webkit-font-smoothing:antialiased}"
                    "a{color:inherit;text-decoration:none}"
                    "code{font-family:ui-monospace,Consolas,monospace;font-size:14px;color:#dee1ec;"
                    "background:var(--input);padding:1px 6px;border-radius:6px}"
                    # 顶部 header
                    ".hd{position:sticky;top:0;z-index:50;height:54px;background:rgba(var(--bgr),.92);"
                    "backdrop-filter:blur(10px);border-bottom:1px solid var(--border);"
                    "display:flex;align-items:center;padding:0 20px;gap:14px}"
                    ".hd .logo{font-size:16px;font-weight:500;color:#fff;display:flex;align-items:center;gap:8px}"
                    ".hd .crumb{color:#8a89a0;font-size:14px}"
                    # 顶栏「群切换」下拉：切到某群后，下面所有设置页显示/保存的都是该群的专属值
                    ".hd .gsel{margin-left:16px;display:flex;align-items:center;gap:7px}"
                    ".hd .gsel .gl{color:#8a89a0;font-size:13px;white-space:nowrap}"
                    ".hd .gsel select{background:var(--input);border:1px solid var(--border);color:#e6e5f0;"
                    "border-radius:8px;padding:5px 9px;font-size:13px;max-width:240px;cursor:pointer}"
                    ".hd .gsel select:focus{outline:none;border-color:var(--ac)}"
                    ".hd .gsel select option{background:var(--card);color:#e6e5f0}"
                    ".hd .right{margin-left:auto;display:flex;align-items:center;gap:14px;color:#8a89a0;font-size:13px}"
                    ".hd .burger{display:none;background:transparent;border:1px solid var(--thead);color:#e6e5f0;"
                    "border-radius:8px;padding:6px 10px;cursor:pointer}"
                    # 整体布局
                    ".wrap{display:flex;min-height:calc(100vh - 52px)}"
                    # 侧栏
                    ".side{width:242px;background:var(--side);border-right:1px solid var(--border);padding:14px 10px;"
                    "flex-shrink:0;overflow-y:auto;transition:transform .2s ease}"
                    ".side .grp-title{padding:14px 12px 6px;font-size:12px;color:#6a6982;letter-spacing:1px;"
                    "text-transform:uppercase;font-weight:500}"
                    ".side .grp-title:first-child{padding-top:4px}"
                    ".side a{display:flex;align-items:center;gap:10px;color:#a9a8bd;font-size:15px;"
                    "padding:9px 12px;border-radius:8px;margin-bottom:1px;transition:background .12s,color .12s}"
                    ".side a:hover{background:var(--hover);color:#fff}"
                    ".side a.active{background:linear-gradient(135deg,var(--ac) 0%,var(--ac2) 100%);color:var(--ac-tx);"
                    "box-shadow:0 4px 14px rgba(var(--acr),.30)}"
                    ".side a.active .badge{background:rgba(127,127,140,.25);color:var(--ac-tx)}"
                    ".side details{margin-bottom:1px}"
                    ".side summary{list-style:none;cursor:pointer;display:flex;align-items:center;gap:10px;"
                    "font-size:15px;color:#a9a8bd;padding:10px 12px;border-radius:8px;user-select:none;"
                    "transition:background .12s,color .12s}"
                    ".side summary::-webkit-details-marker{display:none}"
                    ".side summary:hover{background:var(--hover);color:#fff}"
                    ".side summary.active{background:rgba(var(--acr),.28);color:#fff}"
                    ".side summary::after{content:'⌄';margin-left:auto;color:#6a6982;font-size:11px;transition:transform .15s}"
                    ".side details[open] summary::after{transform:rotate(180deg)}"
                    ".side .sub a{padding:9px 12px 9px 36px;font-size:14px;position:relative}"
                    ".side .sub a::before{content:'○';position:absolute;left:18px;font-size:9px;color:#6a6982}"
                    ".side .sub a.active::before{content:'●';color:#fff}"
                    ".badge{margin-left:auto;font-size:11px;background:var(--thead);color:#a9a8bd;"
                    "border-radius:6px;padding:1px 6px;font-weight:500}"
                    # 主区
                    ".main{flex:1;padding:26px 38px;min-width:0}"
                    ".main h1{font-size:25px;font-weight:500;margin:0 0 6px;color:#fff}"
                    ".main h1 .ico{margin-right:6px}"
                    ".main .sub{font-size:14px;color:#8a89a0;margin-bottom:18px}"
                    # 卡片
                    ".card{background:var(--card);border:1px solid var(--border);border-radius:14px;padding:22px 24px;"
                    "margin-bottom:18px;box-shadow:0 8px 24px rgba(0,0,0,.22)}"
                    ".card h3{font-size:16px;font-weight:500;margin:0 0 14px;color:#c9c8da}"
                    # 表单
                    "label{display:block;font-size:14px;color:#a9a8bd;margin:14px 0 6px}"
                    "input,select,textarea{width:100%;background:var(--input);border:1px solid var(--border);color:#e8e6f2;"
                    "border-radius:9px;padding:10px 13px;font-size:15px;font-family:inherit;transition:border-color .12s}"
                    "input:focus,select:focus,textarea:focus{outline:none;border-color:var(--ac);"
                    "box-shadow:0 0 0 3px rgba(var(--acr),.15)}"
                    "textarea{font-family:ui-monospace,Consolas,monospace;line-height:1.5}"
                    "button{background:linear-gradient(135deg,var(--ac) 0%,var(--ac2) 100%);color:var(--ac-tx);border:none;"
                    "border-radius:9px;padding:10px 24px;font-size:15px;cursor:pointer;font-weight:500;"
                    "transition:transform .1s,box-shadow .12s;box-shadow:0 2px 10px rgba(var(--acr),.25)}"
                    "button:hover{transform:translateY(-1px);box-shadow:0 4px 16px rgba(var(--acr),.4)}"
                    "button:active{transform:translateY(0)}"
                    "button.danger{background:linear-gradient(135deg,#e06666 0%,#b94545 100%);color:#fff;"
                    "box-shadow:0 2px 8px rgba(224,102,102,.2)}"
                    # 提示
                    ".ok{color:#6fd08c;font-size:14px;padding:10px 14px;background:rgba(111,208,140,.08);"
                    "border:1px solid rgba(111,208,140,.2);border-radius:8px;margin-bottom:14px}"
                    ".err{color:#f09595;font-size:14px;padding:10px 14px;background:rgba(240,149,149,.08);"
                    "border:1px solid rgba(240,149,149,.2);border-radius:8px;margin-bottom:14px}"
                    # 统计卡片
                    ".cards{display:grid;grid-template-columns:repeat(auto-fill,minmax(170px,1fr));gap:14px}"
                    ".stat{background:var(--card);border:1px solid var(--border);"
                    "border-radius:14px;padding:18px 20px;transition:transform .15s,border-color .15s,"
                    "box-shadow .15s;box-shadow:0 6px 18px rgba(0,0,0,.18)}"
                    ".stat:hover{transform:translateY(-2px);border-color:var(--ac2);box-shadow:0 10px 26px rgba(var(--acr),.18)}"
                    ".stat .v{font-size:24px;font-weight:500;margin-top:6px;color:#fff}"
                    ".stat .t{font-size:13px;color:#8a89a0;display:flex;align-items:center;gap:6px}"
                    # 快捷入口
                    ".q{display:inline-flex;align-items:center;gap:5px;margin:5px 6px 0 0;"
                    "background:rgba(var(--acr),.14);border:1px solid rgba(var(--acr),.22);color:#dee1ec;"
                    "font-size:14px;padding:9px 15px;border-radius:9px;transition:background .12s,color .12s,border-color .12s}"
                    ".q:hover{background:var(--ac);border-color:var(--ac);color:var(--ac-tx)}"
                    # 行（照阿福紧凑表单：标签固定列宽、控件紧跟其后，整张表单限宽，不甩到屏幕最右）
                    ".row{display:flex;align-items:center;gap:16px;"
                    "padding:12px 0;border-bottom:1px solid var(--border);max-width:900px}"
                    ".row:last-child{border-bottom:none}"
                    ".row .lbl{width:320px;flex:none;font-size:16px;color:#dee1ec;min-width:0;line-height:1.45}"
                    ".row .lbl small{display:block;color:#8a89a0;font-size:13px;margin-top:3px;font-weight:400;line-height:1.5}"
                    ".row input[type=number],.row input[type=text],.row select{width:320px;flex-shrink:0}"
                    ".row textarea{width:100%;margin-top:8px}"
                    # 简单输入双列紧凑（照阿福：数字/短文本参数两列排布）
                    ".grid2{display:grid;grid-template-columns:repeat(auto-fill,minmax(330px,1fr));"
                    "column-gap:30px;row-gap:2px;max-width:900px}"
                    ".grid2 .row{border-bottom:none;padding:9px 0;max-width:none;flex-wrap:wrap;gap:4px 12px}"
                    ".grid2 .row .lbl{width:100%;font-size:14px}"
                    ".grid2 .row .lbl small{font-size:12px}"
                    ".grid2 .row input[type=number],.grid2 .row input[type=text],.grid2 .row select{width:100%}"
                    # 吸底保存条：滚到哪都能看到保存按钮（照阿福的受控保存区）
                    ".savebar{position:sticky;bottom:0;z-index:20;display:flex;align-items:center;gap:14px;"
                    "margin:18px -24px -22px;padding:12px 24px;background:rgba(var(--bgr),.92);"
                    "backdrop-filter:blur(10px);border-top:1px solid var(--border);border-radius:0 0 14px 14px}"
                    ".savebar button{min-width:150px}"
                    ".savebar .hint{font-size:13px;color:#8a89a0;margin-left:auto}"
                    # 词表标签输入（照方丈：回车即添加下一个，✕ 删除，退格删末尾）
                    ".tagbox{display:flex;flex-wrap:wrap;gap:6px;align-items:center;width:320px;flex-shrink:0;"
                    "background:var(--input);border:1px solid var(--border);border-radius:9px;padding:6px 8px;"
                    "min-height:42px;cursor:text;transition:border-color .12s}"
                    ".tagbox:focus-within{border-color:var(--ac);box-shadow:0 0 0 3px rgba(var(--acr),.15)}"
                    ".tagbox .chip{display:inline-flex;align-items:center;background:rgba(var(--acr),.16);"
                    "border:1px solid rgba(var(--acr),.35);border-radius:6px;padding:3px 4px 3px 9px;"
                    "font-size:13px;color:#dee1ec}"
                    ".tagbox .chip b{font-weight:400}"
                    ".tagbox .chip i{font-style:normal;cursor:pointer;color:#8a89a0;padding:0 5px;font-size:12px}"
                    ".tagbox .chip i:hover{color:#f09595}"
                    ".tagbox input[type=text]{flex:1;min-width:80px;background:transparent;border:none;"
                    "padding:4px 2px;color:#e8e6f2;font-size:14px;box-shadow:none!important}"
                    ".grid2 .tagbox{width:100%}"
                    # 防护编辑弹窗（照方丈：一览点「编辑」弹出，内部仍是我们的表单排版）
                    ".modal{display:none;position:fixed;inset:0;background:rgba(0,0,0,.55);z-index:100;"
                    "align-items:flex-start;justify-content:center;padding:6vh 16px;overflow:auto}"
                    ".modal.open{display:flex}"
                    ".modal .mbox{background:var(--card);border:1px solid var(--border);border-radius:14px;"
                    "width:min(660px,94vw);padding:20px 24px 24px;box-shadow:0 18px 50px rgba(0,0,0,.45)}"
                    ".modal .mhead{display:flex;align-items:center;margin-bottom:6px}"
                    ".modal .mhead h3{margin:0}"
                    ".modal .mclose{margin-left:auto;cursor:pointer;color:#8a89a0;font-size:22px;line-height:1;"
                    "background:none;border:none;padding:2px 6px;box-shadow:none}"
                    ".modal .mclose:hover{color:#f09595;transform:none}"
                    ".modal .msub{font-size:13px;color:#8a89a0;margin-bottom:10px}"
                    # 开关
                    ".tg{position:relative;width:44px;height:24px;flex-shrink:0}"
                    ".tg input{opacity:0;width:0;height:0;position:absolute}"
                    ".tg .sl{position:absolute;inset:0;background:var(--thead);border-radius:24px;transition:.2s;cursor:pointer}"
                    ".tg .sl:before{content:'';position:absolute;width:18px;height:18px;left:3px;top:3px;"
                    "background:#fff;border-radius:50%;transition:.2s}"
                    ".tg input:checked+.sl{background:var(--ac)}"
                    ".tg input:checked+.sl:before{transform:translateX(20px)}"
# 分组标题行（sep 字段）
                    ".sec{margin:20px 0 6px;padding:10px 14px;font-size:14px;font-weight:500;color:#d9d3f0;"
                    "background:var(--thead);border-left:3px solid var(--ac);border-radius:0 8px 8px 0;"
                    "letter-spacing:.3px;max-width:900px}"
                    ".sec:first-child{margin-top:2px}"
                    # 多选勾选组（multi 字段）
                    ".cbs{display:grid;grid-template-columns:repeat(auto-fill,minmax(190px,1fr));gap:8px;margin-top:10px}"
                    ".cb{display:flex;align-items:center;gap:9px;margin:0;padding:9px 11px;background:var(--input);"
                    "border:1px solid var(--border);border-radius:9px;cursor:pointer;transition:border-color .12s,background .12s}"
                    ".cb:hover{border-color:rgba(var(--acr),.5);background:rgba(var(--acr),.1)}"
                    ".cb input{width:16px;height:16px;flex-shrink:0;accent-color:var(--ac);cursor:pointer}"
                    ".cb span{font-size:14px;color:#dee1ec;line-height:1.3}"
                    ".cb:has(input:checked){border-color:var(--ac);background:rgba(var(--acr),.12)}"
                    # 表格
                    ".tbl{width:100%;border-collapse:collapse;font-size:14px;margin-top:8px}"
                    ".tbl td,.tbl th{padding:12px 10px;border-bottom:1px solid var(--border);text-align:left}"
                    ".tbl th{color:#b7bcc9;font-weight:500;font-size:13px;background:var(--thead);"
                    "border-bottom:1px solid var(--border)}"
                    ".tbl th:first-child{border-radius:8px 0 0 0}"
                    ".tbl th:last-child{border-radius:0 8px 0 0}"
                    ".tbl td{color:#dfe1ea}"
                    ".tbl tr:nth-child(even) td{background:rgba(255,255,255,.015)}"
                    ".tbl tr:last-child td{border-bottom:none}"
                    ".tbl tr:hover td{background:rgba(var(--acr),.07)}"
                    # 内部表单行（季节/授权等用 div 套 input 而不是 .row）
                    "[style*='padding:13px 2px']{padding:12px 0 !important;border-bottom:1px solid var(--border) !important}"
                    # footer
                    ".ft{padding:18px 28px;text-align:center;color:#6f6a8a;font-size:13px;border-top:1px solid var(--border)}"
                    ".ft a{color:var(--ac)}"
                    # 移动端
                    "@media(max-width:768px){"
                    ".hd{padding:0 12px}"
                    ".hd .burger{display:inline-flex;align-items:center;justify-content:center}"
                    ".wrap{flex-direction:column}"
                    ".side{position:fixed;top:52px;left:0;bottom:0;width:260px;z-index:40;transform:translateX(-100%);"
                    "box-shadow:4px 0 20px rgba(0,0,0,.3)}"
                    ".side.open{transform:translateX(0)}"
                    ".backdrop{position:fixed;inset:52px 0 0 0;background:rgba(0,0,0,.5);z-index:30;display:none}"
                    ".backdrop.show{display:block}"
                    ".main{padding:16px}"
                    ".main h1{font-size:18px}"
                    ".row{flex-direction:column;align-items:stretch;gap:8px}"
                    ".row input[type=number],.row input[type=text],.row select{width:100%}"
                    ".cards{grid-template-columns:repeat(2,1fr);gap:10px}"
                    ".stat{padding:14px}"
                    ".stat .v{font-size:20px}"
                    ".ft{padding:14px;font-size:11px}"
                    "}"
                    # 滚动条（深色风格）
                    "::-webkit-scrollbar{width:8px;height:8px}"
                    "::-webkit-scrollbar-track{background:transparent}"
                    "::-webkit-scrollbar-thumb{background:var(--border);border-radius:4px}"
                    "::-webkit-scrollbar-thumb:hover{background:var(--ac2)}"
                    # 主题色切换点（顶栏）
                    ".dot{width:15px;height:15px;border-radius:50%;display:inline-block;margin-left:7px;"
                    "border:2px solid transparent;cursor:pointer;vertical-align:middle;opacity:.7;transition:.12s}"
                    ".dot:hover{opacity:1;transform:scale(1.18)}"
                    ".dot.cur{border-color:#fff;opacity:1}"
                    # 成员列表增强：首字母头像 / 身份徽章 / 更多折叠 / 紧凑行距
                    ".av{width:28px;height:28px;border-radius:50%;display:inline-flex;align-items:center;"
                    "justify-content:center;color:#fff;font-size:13px;font-weight:600;flex-shrink:0}"
                    ".role{font-size:11px;padding:1px 7px;border-radius:7px;margin-left:7px;font-weight:500;"
                    "display:inline-block;vertical-align:middle;white-space:nowrap}"
                    ".role.owner{background:rgba(245,158,11,.18);color:#fbbf24;border:1px solid rgba(245,158,11,.35)}"
                    ".role.admin{background:rgba(var(--acr),.16);color:#c4b5fd;border:1px solid rgba(var(--acr),.32)}"
                    ".tbl.cp td,.tbl.cp th{padding:8px 8px}"
                    ".more{position:relative;display:inline-block}"
                    ".more .menu{display:none;position:absolute;right:0;top:100%;margin-top:3px;background:var(--card);"
                    "border:1px solid var(--border);border-radius:10px;padding:6px;z-index:30;min-width:130px;"
                    "box-shadow:0 10px 26px rgba(0,0,0,.45)}"
                    ".more:hover .menu{display:block}"
                    ".pbtn{padding:3px 10px;font-size:12px;border-radius:7px;border:none;color:#fff;cursor:pointer;margin:1px}"
                    "</style></head><body>"
                    # 顶部 header
                    "<header class='hd'>"
                    "<button class='burger' onclick=\"document.querySelector('.side').classList.toggle('open');"
                    "document.querySelector('.backdrop').classList.toggle('show')\" aria-label='菜单'>☰</button>"
                    f"<div class='logo'>🤖 机器人后台</div>"
                    f"<div class='crumb'>· {html.escape(title)}"
                    + (f" · 群 {html.escape(chat_name_cache.get(_gcid) or str(_gcid))}" if _gcid else "")
                    + "</div>"
                    # 群切换器：切到某群后，所有设置页读写的都是该群的专属值（未单独设置的项继承全局）
                    + ("<form method='get' class='gsel' action='" + _gact + "'>"
                       "<span class='gl'>🌐 正在配置</span>"
                       "<select name='cid' onchange='this.form.submit()' "
                       "title='选择要配置的群；选「全局默认」则改动作用于所有群'>"
                       + "<option value='0'" + (" selected" if not _gcid else "") + ">全局默认（所有群）</option>"
                       + _group_options(_gcid) + "</select></form>")
                    + "<div class='right'>机器人后台"
                    + "".join(f"<a class='dot{' cur' if k == _thm_key else ''}' title='主题：{k}' "
                              f"href='/theme/{k}?back={quote(('/page/' + sidebar_active if sidebar_active else '/') + _gq)}' "
                              f"style='background:{v[0]}'></a>" for k, v in _UI_THEMES.items())
                    + "</div>"
                    "</header>"
                    "<div class='backdrop' onclick=\"document.querySelector('.side').classList.remove('open');"
                    "this.classList.remove('show')\"></div>"
                    "<div class='wrap'>"
                    f"<nav class='side'>{''.join(items)}</nav>"
                    f"<main class='main'>{_gbanner}{body}</main>{_id_picker_js()}{_sort_js()}{_GUARD_JS}{_gjs}</div>"
                    "<footer class='ft'>© 机器人后台</footer>"
                    "</body></html>").encode("utf-8")

        def _sort_js():
            """表格列头点击排序（通用）：带 data-s 的 th 可点，数字列按数值、其余按中文排序。"""
            return ("<script>document.addEventListener('click',function(e){"
                    "var th=e.target.closest('th[data-s]');if(!th)return;"
                    "var tb=th.closest('table');if(!tb)return;"
                    "var idx=Array.prototype.indexOf.call(th.parentNode.children,th);"
                    "var asc=th.dataset.asc!=='1';"
                    "tb.querySelectorAll('th[data-s]').forEach(function(o){"
                    "o.textContent=o.textContent.replace(/[▲▼]\\s*$/,'');delete o.dataset.asc;});"
                    "th.textContent=th.textContent.replace(/[▲▼]\\s*$/,'')+(asc?' ▲':' ▼');"
                    "th.dataset.asc=asc?'1':'0';"
                    "var rows=[].slice.call(tb.rows).filter(function(r){"
                    "return r.cells.length&&r.cells[0].tagName==='TD';});"
                    "rows.sort(function(a,b){"
                    "var x=a.cells[idx].innerText.trim(),y=b.cells[idx].innerText.trim();"
                    "var nx=parseFloat(x.replace(/,/g,'')),ny=parseFloat(y.replace(/,/g,''));"
                    "if(!isNaN(nx)&&!isNaN(ny))return asc?nx-ny:ny-nx;"
                    "return asc?x.localeCompare(y,'zh'):y.localeCompare(x,'zh');});"
                    "rows.forEach(function(r){tb.appendChild(r);});});</script>")

        def _group_options(selected=0):
            """已知群下拉选项（授权群 ∪ 有积分数据的群）；selected=回显选中。"""
            return "".join(f"<option value='{cid}'{' selected' if cid == selected else ''}>{html.escape(chat_name_cache.get(cid) or '')} {cid}</option>"
                           for cid in sorted(set(AUTHORIZED_GROUPS) | set(game_chips.keys())))

        def _all_user_options(selected=0):
            """全部已知用户选项（value=ID，label=昵称；selected=回显选中）。"""
            seen = {}
            for chips in game_chips.values():
                for u in chips: seen[u] = user_names.get(u, str(u))
            return "".join(f"<option value='{u}'{' selected' if u == selected else ''}>{html.escape(n)}</option>" for u, n in sorted(seen.items()))

        def _id_picker_js():
            """群选择联动用户 datalist 的脚本：select[data-users-for] 选中群后自动填充对应成员。"""
            gusers = {str(cid): {str(u): user_names.get(u, str(u)) for u in chips}
                      for cid, chips in game_chips.items()}
            # 安全：昵称是可控输入，直接嵌进 <script> 会形成存储型 XSS（玩家改昵称即可在后台执行 JS）。
            # ① 把 < / 转成 \u003c \u002f（JSON 合法转义，JS 解析后还原，但不会闭合标签）
            # ② 不再用 innerHTML 拼字符串，改用 DOM API 写入
            raw = json.dumps(gusers, ensure_ascii=False).replace("<", "\\u003c").replace("/", "\\u002f")
            return ("<script>var GUSERS=" + raw + ";"
                    "document.addEventListener('DOMContentLoaded',function(){"
                    "function fill(){document.querySelectorAll('select[data-users-for]').forEach(function(sel){"
                    "var dl=document.getElementById(sel.getAttribute('data-users-for'));if(!dl)return;"
                    "var us=GUSERS[sel.value]||{};"
                    "dl.textContent='';"
                    "Object.keys(us).forEach(function(u){var o=document.createElement('option');"
                    "o.value=u;o.textContent=us[u];dl.appendChild(o);});});}"
                    "document.querySelectorAll('select[data-users-for]').forEach(function(sel){sel.addEventListener('change',fill);});fill();});</script>")

        def _otp_page(otp_token, err="", notice=""):
            """二次验证页：密码已通过，等 Telegram 私聊发来的 6 位验证码。"""
            msg = f"<div class='err'>{html.escape(err)}</div>" if err else ""
            msg += f"<div class='ok'>{html.escape(notice)}</div>" if notice else ""
            return ("<!DOCTYPE html><html lang='zh'><head><meta charset='utf-8'>"
                    "<meta name='viewport' content='width=device-width, initial-scale=1'>"
                    "<title>二次验证 - 机器人后台</title><style>"
                    "*{box-sizing:border-box}html,body{height:100%}"
                    "body{background:linear-gradient(135deg,#17181d 0%,#121318 100%);color:#e6e5f0;"
                    "font-family:system-ui,'PingFang SC','Microsoft YaHei',sans-serif;margin:0;display:flex;"
                    "align-items:center;justify-content:center;padding:20px;min-height:100vh}"
                    ".login{background:#1b1c22;border:1px solid #2a2b33;border-radius:14px;padding:32px;"
                    "width:min(380px,100%);box-shadow:0 20px 60px rgba(0,0,0,.4)}"
                    ".login h1{font-size:20px;font-weight:500;margin:0 0 4px;text-align:center;color:#fff}"
                    ".login .desc{font-size:12px;color:#8a89a0;text-align:center;margin-bottom:24px;line-height:1.6}"
                    ".login label{display:block;font-size:13px;color:#a9a8bd;margin:14px 0 6px}"
                    ".login input{width:100%;background:#121318;border:1px solid #2a2b33;color:#e6e5f0;"
                    "border-radius:8px;padding:11px 14px;font-size:14px;transition:border-color .12s;"
                    "letter-spacing:6px;text-align:center;font-size:20px}"
                    ".login input:focus{outline:none;border-color:#7c6cf0;box-shadow:0 0 0 3px rgba(124,108,240,.12)}"
                    ".login button{width:100%;background:linear-gradient(135deg,#7c6cf0 0%,#5d4dd6 100%);"
                    "color:#fff;border:none;border-radius:8px;padding:12px;font-size:15px;cursor:pointer;"
                    "font-weight:500;margin-top:22px;box-shadow:0 4px 14px rgba(124,108,240,.3)}"
                    ".login .err{color:#f09595;font-size:13px;padding:10px 14px;background:rgba(240,149,149,.08);"
                    "border:1px solid rgba(240,149,149,.2);border-radius:8px;margin-bottom:14px;text-align:center}"
                    ".login .ok{color:#6fd08c;font-size:13px;padding:10px 14px;background:rgba(111,208,140,.08);"
                    "border:1px solid rgba(111,208,140,.2);border-radius:8px;margin-bottom:14px;text-align:center}"
                    ".login .resend{margin-top:14px;text-align:center}"
                    ".login .resend button{background:transparent;border:1px solid #2a2b33;color:#a9a8bd;"
                    "box-shadow:none;font-size:13px;padding:8px 16px;margin-top:0}"
                    ".login .ft{padding:14px 0 0;margin-top:20px;border-top:1px solid #26272e;font-size:11px;"
                    "color:#6a6982;text-align:center}"
                    "</style></head><body><div class='login'>"
                    "<h1>🔐 二次验证</h1>"
                    "<div class='desc'>密码已通过<br>验证码已发到你的 Telegram 私聊<br><b>5 分钟内有效</b></div>"
                    + msg +
                    "<form method='post' action='/login2'>"
                    f"<input type='hidden' name='otp_token' value='{html.escape(otp_token)}'>"
                    "<label>6 位验证码</label>"
                    "<input type='text' name='otp' inputmode='numeric' pattern='[0-9]{6}' "
                    "maxlength='6' autocomplete='one-time-code' autofocus required placeholder='——————'>"
                    "<button type='submit'>验 证 并 登 录</button></form>"
                    "<form method='post' action='/login' class='resend'>"
                    f"<input type='hidden' name='resend' value='{html.escape(otp_token)}'>"
                    "<button type='submit'>🔄 重新发送验证码</button></form>"
                    "<div class='ft'>© 机器人后台 · 二次验证保护</div>"
                    "</div></body></html>").encode("utf-8")

        def _admin_receivers():
            """后台通知收件人：ADMIN_USER_ID + 全部 BOT_ADMINS（去重、过滤无效 0）。"""
            ids = {ADMIN_USER_ID}
            ids.update(BOT_ADMINS)
            return sorted(i for i in ids if i)

        def _send_otp_code(ip):
            """生成验证码并私聊发给所有管理员。返回 (otp_token, code, err)。

            任一管理员收到即可完成登录；全部发送失败才返回错误
            （常见原因：管理员从未私聊过机器人，Telegram 禁止 bot 主动发起）。
            """
            code = f"{secrets.randbelow(1000000):06d}"
            otp_token = secrets.token_urlsafe(24)
            with sess_lock:
                web_pending_otp[otp_token] = {"code": code, "exp": time.time() + 300, "ip": ip}
                # 清理过期等待
                for k in [k for k, v in web_pending_otp.items() if v["exp"] < time.time()]:
                    web_pending_otp.pop(k, None)
            if not (_bot_app and _bot_loop):
                return otp_token, code, "bot 未就绪，无法发送验证码"
            text = (f"🔐 <b>后台登录二次验证</b>\n\n"
                    f"验证码：<code>{code}</code>\n"
                    f"来源 IP：<code>{ip}</code>\n"
                    f"5 分钟内有效，一次性使用。\n\n"
                    f"⚠️ 如果不是你本人操作，请立即修改后台密码。")
            async def _send():
                ok_cnt = 0
                for rid in _admin_receivers():
                    try:
                        await _bot_app.bot.send_message(chat_id=rid, text=text, parse_mode="HTML")
                        ok_cnt += 1
                    except Exception:
                        logger.warning("验证码发送给 %s 失败（可能未私聊过机器人）", rid)
                return ok_cnt
            try:
                ok_cnt = asyncio.run_coroutine_threadsafe(_send(), _bot_loop).result(15)
                if ok_cnt <= 0:
                    return otp_token, code, "验证码发送失败：所有管理员均未私聊过机器人（先在 Telegram 私聊发 /start，或用 /网页码 取码）"
                return otp_token, code, ""
            except Exception as exc:
                logger.exception("登录验证码发送失败")
                return otp_token, code, f"发送失败：{type(exc).__name__}: {str(exc)[:120]}"

        def _login_page(err=""):
            msg = "<div class='err'>密码错误，请重试</div>" if err else ""
            # 用户要求：登录页不放任何默认密码提示（安全红线不变：也绝不显示密码本体）
            return ("<!DOCTYPE html><html lang='zh'><head><meta charset='utf-8'>"
                    "<meta name='viewport' content='width=device-width, initial-scale=1'>"
                    "<title>登录 - 机器人后台</title><style>"
                    "*{box-sizing:border-box}"
                    "html,body{height:100%}"
                    "body{background:linear-gradient(135deg,#17181d 0%,#121318 100%);color:#e6e5f0;"
                    "font-family:system-ui,'PingFang SC','Microsoft YaHei',sans-serif;margin:0;display:flex;"
                    "align-items:center;justify-content:center;padding:20px;min-height:100vh}"
                    ".login{background:#1b1c22;border:1px solid #2a2b33;border-radius:14px;padding:32px;"
                    "width:min(380px,100%);box-shadow:0 20px 60px rgba(0,0,0,.4)}"
                    ".login h1{font-size:20px;font-weight:500;margin:0 0 4px;text-align:center;color:#fff}"
                    ".login .desc{font-size:12px;color:#8a89a0;text-align:center;margin-bottom:24px}"
                    ".login label{display:block;font-size:13px;color:#a9a8bd;margin:14px 0 6px}"
                    ".login input{width:100%;background:#121318;border:1px solid #2a2b33;color:#e6e5f0;"
                    "border-radius:8px;padding:11px 14px;font-size:14px;transition:border-color .12s}"
                    ".login input:focus{outline:none;border-color:#7c6cf0;box-shadow:0 0 0 3px rgba(124,108,240,.12)}"
                    ".login button{width:100%;background:linear-gradient(135deg,#7c6cf0 0%,#5d4dd6 100%);"
                    "color:#fff;border:none;border-radius:8px;padding:12px;font-size:15px;cursor:pointer;"
                    "font-weight:500;margin-top:22px;transition:transform .1s,box-shadow .12s;"
                    "box-shadow:0 4px 14px rgba(124,108,240,.3)}"
                    ".login button:hover{transform:translateY(-1px);box-shadow:0 6px 20px rgba(124,108,240,.45)}"
                    ".login .err{color:#f09595;font-size:13px;padding:10px 14px;background:rgba(240,149,149,.08);"
                    "border:1px solid rgba(240,149,149,.2);border-radius:8px;margin-bottom:14px;text-align:center}"
                    ".login .ft{padding:14px 0 0;margin-top:20px;border-top:1px solid #26272e;font-size:11px;"
                    "color:#6a6982;text-align:center}"
                    "</style></head><body><div class='login'>"
                    "<h1>🤖 机器人后台</h1>"
                    "<div class='desc'>管理员登录</div>" + msg +
                    "<form method='post' action='/login'>"
                    "<label>管理密码</label><input type='password' name='password' autofocus required>"
                    "<button type='submit'>登 录</button></form>"
                    "<div class='ft'>💡 推荐：Telegram 发 <b>/后台</b>，点链接免密登录（密码为备用通道）<br>© 机器人后台 · v" + BOT_VERSION + "</div>"
                    "</div></body></html>").encode("utf-8")

        def _savebar(label="保存设置", hint="保存立即生效，无需重启"):
            # 吸底保存条：贴在卡片底部、滚动时始终可见（照阿福的受控保存区）
            return (f"<div class='savebar'><button type='submit'>💾 {label}</button>"
                    f"<span class='hint'>{hint}</span></div>")

        _GUARD_JS = ("<script>function openModal(id){document.getElementById(id).classList.add('open')} "
                     "function closeModal(id){document.getElementById(id).classList.remove('open')} "
                     "document.addEventListener('click',function(e){"
                     "if(e.target.classList&&e.target.classList.contains('modal'))e.target.classList.remove('open')});"
                     "document.addEventListener('keydown',function(e){"
                     "if(e.key==='Escape')document.querySelectorAll('.modal.open').forEach("
                     "function(m){m.classList.remove('open')})});</script>")

        def _guard_badge(on):
            return ("<span style='color:#6fd08c;font-weight:500'>✅ 已启用</span>" if on
                    else "<span style='color:#8a89a0'>⛔ 已停用</span>")

        def _guard_row(name, on, summary, mid):
            """防护类型一览行（照方丈）：名称 + 状态徽章 + 参数摘要 + 编辑按钮。"""
            return (f"<tr><td style='width:32%'><b>{html.escape(name)}</b></td>"
                    f"<td>{_guard_badge(on)}<div class='m-sum' style='font-size:12px;color:#8a89a0;margin-top:3px'>"
                    f"{summary}</div></td>"
                    f"<td style='width:90px'><a class='q' style='cursor:pointer' onclick=\"openModal('{mid}')\">✏️ 编辑</a></td></tr>")

        def _guard_modal(mid, title, sub, group, keys):
            """防护编辑弹窗：内部仍用我们自己的表单排版（_field_rows）；带 _fields 限定提交范围，
            /save 只套用弹窗内的字段，组内其他开关不会被误清零。"""
            from_mark = ",".join(sorted(keys))
            return (f"<div class='modal' id='{mid}'><div class='mbox'>"
                    f"<div class='mhead'><h3>{html.escape(title)}</h3>"
                    f"<button class='mclose' type='button' onclick=\"closeModal('{mid}')\">✕</button></div>"
                    f"<div class='msub'>{sub}</div>"
                    f"<form method='post' action='/save'>"
                    f"<input type='hidden' name='group' value='{group}'>"
                    f"<input type='hidden' name='_fields' value=\"{html.escape(from_mark, quote=True)}\">"
                    + _field_rows(group, keys=keys) +
                    f"<button type='submit' style='margin-top:16px'>💾 保存（{html.escape(title)}）</button></form></div></div>")

        def _field_rows(gkey, keys=None):
            # keys=None 渲染组内全部字段；传键集合则只渲染这些字段（防护弹窗用）
            rows = []
            # 群级页面右上角取值来源小标（仅群页面出现）
            _OV_CSS = ("position:absolute;top:6px;right:0;font-size:11px;padding:1px 7px;"
                       "border-radius:7px;background:rgba(var(--acr),.18);color:#c4b5fd;"
                       "border:1px solid rgba(var(--acr),.35);text-decoration:none;white-space:nowrap")

            def _ov_wrap(key, body):
                """群页面上的取值来源标记：
                   ⚑ 群专属 ↺ = 该群已覆盖（点它清除覆盖、改回继承全局）
                   🌐 全局项   = 全站唯一设置（密码/调度/备份等），按群覆盖无意义，保存只作用于全局
                   无标记     = 继承全局默认
                """
                cid = cur_cid()
                if not cid:
                    return body
                if key in GROUP_SCOPED_KEYS:
                    if key not in (GROUP_SETTINGS.get(cid) or {}):
                        return body
                    badge = ("<a href='/gclear/" + str(cid) + "/" + key + "' style='" + _OV_CSS +
                             "' title='清除该群专属值，改回继承全局默认'>⚑ 群专属 ↺</a>")
                else:
                    badge = ("<span style='" + _OV_CSS + ";opacity:.75' title='全站唯一设置，"
                             "保存会作用于所有群'>🌐 全局项</span>")
                return "<div style='position:relative'>" + body + badge + "</div>"

            if gkey == "tpls":
                # 跨组聚合：全部话术模板按所属模块分区，一次改完
                last = None
                for key, _g, label, ftype, lo, hi, grp in SETTINGS_FIELDS:
                    if ftype != "text" or key not in (_cross_keys("tpls") or set()):
                        continue
                    if grp != last:
                        rows.append(f"<div class='sec'>{html.escape(_grp_title(grp))}</div>")
                        last = grp
                    cur = sget(_g)
                    rows.append(_ov_wrap(key, f"<div style='padding:13px 2px;border-bottom:1px solid var(--border)'>"
                                f"<div class='lbl' style='display:flex;align-items:center;justify-content:space-between'>"
                                f"<span>{html.escape(label)}<small>可用占位符见默认值；支持换行</small></span>"
                                f"<a class='q' href='/tplprev/{key}'>🔍 预览</a></div>"
                                f"<textarea name='{key}' rows='4' style='margin-top:8px'>{html.escape(cur or '')}</textarea></div>"))
                return "".join(rows)

            def _one_raw(key, _g, label, ftype, lo, hi):
                cur = sget(_g)
                if ftype == "multi":
                    picked = {p.strip() for p in str(cur or "").split(",") if p.strip()}
                    boxes = []
                    for val, vlabel in MULTI_OPTIONS.get(key, []):
                        ck = " checked" if val in picked else ""
                        boxes.append(f"<label class='cb'><input type='checkbox' name='{key}' "
                                     f"value='{html.escape(val, quote=True)}'{ck}>"
                                     f"<span>{html.escape(vlabel)}</span></label>")
                    return (f"<div style='padding:13px 2px;border-bottom:1px solid var(--border)'>"
                            f"<div class='lbl'>{html.escape(label)}"
                            f"<small>勾选即生效；未勾选的类型一律放行</small></div>"
                            f"<div class='cbs'>{''.join(boxes)}</div></div>")
                if ftype == "bool":
                    checked = " checked" if cur else ""
                    return (f"<div class='row'><div class='lbl'>{html.escape(label)}</div>"
                            f"<label class='tg'><input type='checkbox' name='{key}'{checked}>"
                            f"<span class='sl'></span></label></div>")
                if ftype in ("levels", "items"):
                    if isinstance(cur, (list, tuple)) and cur and isinstance(cur[0], dict):
                        val = "\n".join(f"{x['name']}:{x['value']}" for x in cur)
                    else:
                        val = str(cur or "")
                    return (f"<div style='padding:13px 2px;border-bottom:1px solid var(--border)'>"
                            f"<div class='lbl'>{html.escape(label)}<small>每行一条：名称:数值</small></div>"
                            f"<textarea name='{key}' rows='5' style='margin-top:8px'>{html.escape(val)}</textarea></div>")
                if ftype == "text":
                    return (f"<div style='padding:13px 2px;border-bottom:1px solid var(--border)'>"
                            f"<div class='lbl' style='display:flex;align-items:center;justify-content:space-between'>"
                            f"<span>{html.escape(label)}<small>可用占位符见默认值；支持换行</small></span>"
                            f"<a class='q' href='/tplprev/{key}'>🔍 预览</a></div>"
                            f"<textarea name='{key}' rows='5' style='margin-top:8px'>{html.escape(cur or '')}</textarea></div>")
                if ftype == "short":
                    return (f"<div class='row'><div class='lbl'>{html.escape(label)}</div>"
                            f"<input type='text' name='{key}' value='{html.escape(cur, quote=True)}' maxlength='8'></div>")
                if ftype == "cmd":
                    return (f"<div class='row'><div class='lbl'>{html.escape(label)}"
                            f"<small>改完立即生效，无需重启；旧指令同时失效</small></div>"
                            f"<input type='text' name='{key}' value='{html.escape(cur, quote=True)}' maxlength='16'></div>")
                if ftype in ("names", "emoji", "bets"):
                    # 词表标签输入（照方丈）：回车/逗号即添加，✕ 删除，退格删末尾；
                    # 底层仍是逗号分隔的 hidden input，提交格式不变，保存逻辑零改动
                    items = ([str(x).strip() for x in cur if str(x).strip()] if isinstance(cur, (list, tuple))
                             else [p.strip() for p in re.split(r"[,，]", str(cur or "")) if p.strip()])
                    chips = "".join(f"<span class='chip'><b>{html.escape(s)}</b><i title='删除'>✕</i></span>" for s in items)
                    ph = "数字 1~100000，回车添加" if ftype == "bets" else "输入后按回车添加"
                    return (f"<div class='row'><div class='lbl'>{html.escape(label)}</div>"
                            f"<div class='tagbox'>{chips}"
                            f"<input type='hidden' name='{key}' value='{html.escape(','.join(items), quote=True)}'>"
                            f"<input type='text' placeholder='{ph}' autocomplete='off'>"
                            "</div>"
                            "<script>if(!window._tbInit){window._tbInit=1;"
                            "function _tbSync(tb){var h=tb.querySelector('input[type=hidden]');if(!h)return;"
                            "h.value=[].map.call(tb.querySelectorAll('.chip b'),function(x){return x.textContent}).join(',')}"
                            "document.addEventListener('click',function(e){"
                            "var i=e.target.closest('.tagbox .chip i');"
                            "if(i){var tb=i.closest('.tagbox');i.parentElement.remove();_tbSync(tb);return}"
                            "var tb=e.target.closest('.tagbox');if(tb){var f=tb.querySelector('input[type=text]');if(f)f.focus()}});"
                            "document.addEventListener('keydown',function(e){"
                            "var inp=e.target.closest('.tagbox input[type=text]');if(!inp)return;"
                            "var tb=inp.closest('.tagbox');"
                            "if(e.key==='Enter'||e.key===','||e.key==='，'){e.preventDefault();"
                            "var v=inp.value.replace(/[,，]/g,'').trim();"
                            "if(v){var c=document.createElement('span');c.className='chip';"
                            "var b=document.createElement('b');b.textContent=v;c.appendChild(b);"
                            "var x=document.createElement('i');x.textContent='✕';x.title='删除';c.appendChild(x);"
                            "tb.insertBefore(c,inp);inp.value='';_tbSync(tb)}}"
                            "else if(e.key==='Backspace'&&!inp.value){"
                            "var cs=tb.querySelectorAll('.chip');if(cs.length){cs[cs.length-1].remove();_tbSync(tb)}}});}"
                            "</script></div>")
                return (f"<div class='row'><div class='lbl'>{html.escape(label)}"
                        f"<small>范围 {lo} ~ {hi}</small></div>"
                        f"<input type='number' name='{key}' value='{cur}' step='{'0.1' if ftype == 'float' else '1'}'></div>")

            def _one(key, _g, label, ftype, lo, hi):
                """渲染单个设置项：取值走 sget（群级覆盖 → 全局），并标记群专属项。"""
                return _ov_wrap(key, _one_raw(key, _g, label, ftype, lo, hi))

            grp_fields = [f for f in SETTINGS_FIELDS if f[6] == gkey and (keys is None or f[0] in keys)]
            if not grp_fields:
                return ""
            if any(f[3] == "sep" for f in grp_fields):
                # ①②③ 结构化页（mod/autodel/schedule）：分节标题就是布局，保持定义顺序原样渲染
                return "".join(f"<div class='sec'>{html.escape(f[2])}</div>" if f[3] == "sep" else _one(*f[:6])
                               for f in grp_fields)
            # 普通页（照阿福）：开关置顶 → 数字/短文本参数双列 → 宽内容（模板/多选/词表）殿后
            # bets 走宽内容区独占整行：它是 tagbox（可换行的标签盒），塞进 grid2 双列必被裁切
            # （用户 2026-09-10 截图：4 个金额标签只显示到「200」右侧就被切掉）
            bools = [f for f in grp_fields if f[3] == "bool"]
            simple = [f for f in grp_fields if f[3] in ("int", "float", "short", "cmd")]
            wide = [f for f in grp_fields if f[3] in ("text", "multi", "levels", "items", "names", "emoji", "bets")]
            parts = []
            if bools and (simple or wide):
                parts.append("<div class='sec'>🎛 开关</div>")
            parts += [_one(*f[:6]) for f in bools]
            if simple:
                if bools:
                    parts.append("<div class='sec'>⚙️ 参数</div>")
                parts.append("<div class='grid2'>" + "".join(_one(*f[:6]) for f in simple) + "</div>")
            if wide:
                if bools or simple:
                    parts.append("<div class='sec'>📝 内容与模板</div>")
                parts += [_one(*f[:6]) for f in wide]
            return "".join(parts)

        def _home_page():
            all_players = {u for users in game_chips.values() for u in users}
            total_chips = sum(sum(users.values()) for users in game_chips.values())
            group_count = len(AUTHORIZED_GROUPS)
            # 今日四个游戏的局数（按日期分组的 profit dict 的 key 数）
            today = datetime.now(BEIJING_TZ).strftime("%Y-%m-%d")
            today_bets = sum(
                sum(len(v) for v in d.get(today, {}).values())
                for d in (poker_profit_by_date, race_profit_by_date, blackjack_profit_by_date, jinhua_profit_by_date)
            )
            season_txt = (season_name + " · 进行中") if season_active else "未开启"
            today_profit = sum(
                sum(users.values())
                for d in (poker_profit_by_date, race_profit_by_date, blackjack_profit_by_date, jinhua_profit_by_date)
                for users in [d.get(today, {}).get(c, {}) for c in d.get(today, {})]
            )
            def stat(label, value, hint=""):
                hint_html = f"<div style='font-size:11px;color:#6a6982;margin-top:4px'>{hint}</div>" if hint else ""
                return f"<div class='stat'><div class='t'>{label}</div><div class='v'>{value}</div>{hint_html}</div>"
            cards = (
                stat("👥 玩家总数", f"{len(all_players):,}", "跨所有授权群去重") +
                stat("💰 积分总量", f"{total_chips:,}", "所有玩家钱包余额之和") +
                stat("🏘️ 授权群数", f"{group_count}", "Bot 服务覆盖的群") +
                stat("🎮 今日局数", f"{today_bets:,}", f"德州+赛车+21点+炸金花 · {today}") +
                stat("📈 今日净盈亏", f"{today_profit:+,}", "正=玩家净赚，负=玩家净输") +
                stat("🏆 赛季", season_txt, f"ID {season_id}" if season_id else "") +
                stat("💾 数据存储", "✔ 持久化" if str(_data_file_status()).startswith("/data") else "⚠ 容器内",
                     _data_file_status())
            )
            quick = "".join(f"<a class='q' href='/page/{g}'>{i} {n}</a>" for g, n, i in SETTINGS_GROUPS if g != "dashboard")
            # 每群活动详情：你说的"分开的活跃度"——每群一行，玩了多少局/邀了多少人/赛车开关一眼看完
            g_rows = []
            for cid in sorted(AUTHORIZED_GROUPS, key=lambda c: (chat_name_cache.get(c) or str(c))):
                gname = chat_name_cache.get(cid) or str(cid)
                g_players = len(game_chips.get(cid, {}))
                g_chips = sum(game_chips.get(cid, {}).values())
                # 今日四游戏局数（按 profit dict 中今日该 cid 的玩家数近似）
                g_bets = sum(
                    1 for d in (poker_profit_by_date, race_profit_by_date, blackjack_profit_by_date, jinhua_profit_by_date)
                    for uid in d.get(today, {}).get(cid, {}))
                # 今日有效邀请
                g_invites = sum(1 for r in invite_records.values()
                                if r.get("cid") == cid and _rec_valid(r)
                                and str(r.get("ts", "")).startswith(today))
                g_race = "⏰ 开启" if hourly_race_enabled.get(cid, True) else "⏸ 关闭"
                g_rows.append(
                    f"<tr><td><code>{cid}</code> {html.escape(gname)}</td>"
                    f"<td>{g_players}</td><td>{g_chips:,}</td>"
                    f"<td>{g_bets}</td><td>{g_invites}</td>"
                    f"<td>{g_race}</td></tr>")
            if not g_rows:
                g_rows = "<tr><td colspan='6' style='text-align:center;color:#6a6982'>还没授权群，群里发 /授权</td></tr>"
            group_detail = ("<div class='card' style='margin-top:18px'>"
                            "<h3>🏘️ 各群活动详情（你要的分开的活跃度）</h3>"
                            "<div class='sub'>玩家/积分为当前余额；今日局数=德州+赛车+21点+炸金花官方局；今日有效邀请=未退群且审核通过；整点赛车=群内默认状态</div>"
                            "<table class='tbl'><tr><th>群</th><th>玩家</th><th>积分余额</th><th>今日局数</th><th>今日有效邀请</th><th>整点赛车</th></tr>"
                            + "".join(g_rows) + "</table></div>")
            # 菜单排序：▲▼ 调整侧边栏顺序（群体总览固定第一），保存进设置
            nav = [g for g in SETTINGS_GROUPS if g[0] != "dashboard"]
            keys_now = [g[0] for g in nav]
            meta = {g[0]: (g[1], g[2]) for g in SETTINGS_GROUPS}
            ordered_keys = [k for k in SIDEBAR_ORDER if k in keys_now] + [k for k in keys_now if k not in SIDEBAR_ORDER]
            sort_rows = ""
            for k in ordered_keys:
                n, i = meta.get(k, (k, "•"))
                sort_rows += ("<div style='display:flex;align-items:center;gap:12px;padding:7px 2px;"
                              "border-bottom:1px solid var(--border)'>"
                              f"<span style='flex:1'>{i} {n}</span>"
                              f"<a href='/menu_move/{k}/-1' style='padding:2px 10px;background:var(--hover);"
                              "border-radius:6px;font-size:12px'>▲ 上移</a>"
                              f"<a href='/menu_move/{k}/1' style='padding:2px 10px;background:var(--hover);"
                              "border-radius:6px;font-size:12px'>▼ 下移</a></div>")
            return _page("群体总览", "dashboard",
                "<h1><span class='ico'>📊</span>群体总览</h1>"
                "<div class='sub'>实时数据快照 · 改设置去左侧菜单 · 数据修改去 Telegram 群用 /命令</div>"
                f"<div class='cards'>{cards}</div>"
                + group_detail +
                "<div class='card' style='margin-top:18px'>"
                "<h3>⚡ 快捷入口</h3>" + quick + "</div>"
                "<div class='card' style='margin-top:18px'>"
                "<h3>🧭 侧边栏菜单排序</h3>"
                "<div class='sub' style='margin-bottom:8px'>点 ▲▼ 调整左侧菜单顺序，立即生效并保存</div>"
                + sort_rows + "</div>")

        def _members_body(mode="ops"):
            """群组管理分页：records=进出记录+入群申请；ops=白名单+操作记录。
            （成员档案已独立成「群组成员列表」mlist 页，这里不再重复展示）"""
            def tbl(headers, rows):
                if not rows:
                    return "<div class='sub' style='margin-top:8px'>暂无记录</div>"
                head = "".join(f"<th>{h}</th>" for h in headers)
                body = "".join("<tr>" + "".join(f"<td>{c}</td>" for c in r) + "</tr>" for r in rows)
                return f"<table class='tbl'><tr>{head}</tr>{body}</table>"
            parts = []
            if mode == "records":
                # 1. 退群/入群记录
                lv_rows = [[r.get("ts", ""), html.escape(chat_name_cache.get(cid) or str(cid)),
                            html.escape(r.get("name", "")), f"<code>{r.get('uid', '')}</code>",
                            "🟢 入群" if r.get("join") else "🔴 退群"]
                           for cid, lst in leave_records.items() for r in reversed(lst[-30:])]
                parts.append("<div class='card'><h1>进出记录（最近 30 条）</h1>"
                             "<div class='sub'>bot 需为群管理员才能收到成员进出事件</div>"
                             + tbl(["时间", "群", "成员", "ID", "类型"], lv_rows[-30:]) + "</div>")
                # 2. 入群申请（可直接网页批准/拒绝）
                def _jr_btn(op, c, u, label):
                    return ("<form style='display:inline;margin:0' method='post' action='/adminops2'>"
                            f"<input type='hidden' name='op' value='{op}'>"
                            f"<input type='hidden' name='cid' value='{c}'>"
                            f"<input type='hidden' name='uid' value='{u}'>"
                            f"<button type='submit' style='padding:2px 10px;cursor:pointer'>{label}</button></form>")
                jq_rows = [[r.get("ts", ""), html.escape(chat_name_cache.get(cid) or str(cid)),
                            html.escape(r.get("name", "")), f"<code>{r.get('uid', '')}</code>",
                            _jr_btn("join_approve", cid, r.get("uid", ""), "✅ 批准") + " " + _jr_btn("join_decline", cid, r.get("uid", ""), "🚫 拒绝")]
                           for cid, lst in join_requests.items() for r in reversed(lst[-30:])]
                parts.append("<div class='card'><h1>📨 入群申请（最近 30 条）</h1>"
                             "<div class='sub'>群需开启「申请加入」；可直接在此批准或拒绝，无需去 Telegram 客户端</div>"
                             + tbl(["时间", "群", "申请人", "ID", "操作"], jq_rows[-30:]) + "</div>")
            else:
                # 白名单
                wl_rows = [[cid, html.escape(user_names.get(u, str(u))), f"<code>{u}</code>"]
                           for cid, us in whitelist.items() for u in sorted(us)]
                parts.append("<div class='card'><h1>🛡️ 白名单</h1>"
                             "<div class='sub'>免疫禁言/群封；群里回复消息发「加白」「删白」管理，或在成员列表页加白</div>"
                             + tbl(["群", "成员", "ID"], wl_rows) + "</div>")
                # 管理员操作记录
                op_rows = [[r.get("ts", ""), f"群 {r.get('cid', '')}", html.escape(r.get("admin", "")),
                            html.escape(r.get("action", "")), html.escape(r.get("target", ""))]
                           for r in reversed(admin_logs[-30:])]
                parts.append("<div class='card'><h1>📜 管理员操作记录（最近 30 条）</h1>"
                             "<div class='sub'>bot 执行的每次禁言/封禁/白名单操作自动留档</div>"
                             + tbl(["时间", "群", "操作人", "动作", "对象"], op_rows[-30:]) + "</div>")
            return "".join(parts)

        def _admin_page(gkey, sub=None, saved=False, bad=False, note="", err="", uid=0, flt=None):
            gname, gicon = next((n, i) for k, n, i in SETTINGS_GROUPS if k == gkey)
            msg = "<div class='ok'>✅ 已保存并立即生效</div>" if saved else ""
            msg += "<div class='err'>部分数值超出范围或非法，已跳过这些项</div>" if bad else ""
            msg += f"<div class='ok'>{html.escape(note)}</div>" if note else ""
            msg += f"<div class='err'>{html.escape(err)}</div>" if err else ""
            sel_flt_cid = int((flt or {}).get("cid", 0) or 0)
            def _flt_bar(action):
                # 数据页通用「群组筛选」条：GET ?cid=，选择即提交
                return ("<form method='get' action='" + action + "' style='margin-bottom:10px'>"
                        "<div class='lbl'>群组筛选</div><select name='cid' onchange='this.form.submit()'>"
                        "<option value='0'>全部群</option>" + _group_options(selected=sel_flt_cid)
                        + "</select><noscript><button style='margin:0'>查看</button></noscript></form>")
            def _perm_boxes(picked, name="perms"):
                # 8 类消息权限勾选（等级新增/编辑共用）
                pk = {p.strip() for p in str(picked or "").split(",") if p.strip()}
                out = []
                for _k, _v in LEVEL_PERM_OPTIONS:
                    ck = " checked" if _k in pk else ""
                    out.append(f"<label class='cb' style='margin:0 14px 6px 0'>"
                               f"<input type='checkbox' name='{name}' value='{_k}'{ck}>"
                               f"<span>{html.escape(_v)}</span></label>")
                return "<div class='cbs' style='flex-wrap:wrap'>" + "".join(out) + "</div>"
            def _perm_summary(picked):
                pk = {p.strip() for p in str(picked or "").split(",") if p.strip()}
                if len(pk) >= len(LEVEL_PERM_OPTIONS):
                    return "<span style='color:#6fd08c'>全部放行</span>"
                if not pk:
                    return "<span style='color:#f09595'>全部禁止</span>"
                names = [LEVEL_PERM_NAMES.get(k, k) for k, _v in LEVEL_PERM_OPTIONS if k in pk]
                return html.escape("、".join(names))
            if gkey == "members" and sub == "mlist":
                fl = flt or {}
                sel_cid = fl.get("cid", 0)
                q = (fl.get("q") or "").strip()
                per = fl.get("per", 20) if fl.get("per", 20) in (10, 20, 50, 100) else 20
                page = max(1, fl.get("page", 1))
                members = []
                if sel_cid:
                    profs = member_profiles.get(sel_cid, {})
                    uids = set(profs) | set(game_chips.get(sel_cid, {})) | set(member_joined_at.get(sel_cid, {}))
                    now = now_bj()
                    for u in uids:
                        pr = profs.get(u, {})
                        joined = member_joined_at.get(sel_cid, {}).get(u, 0)
                        last = str(pr.get("last", "") or "")
                        days = None
                        if last:
                            try:
                                days = (now - datetime.strptime(last, "%Y-%m-%d %H:%M").replace(tzinfo=BEIJING_TZ)).days
                            except ValueError:
                                pass
                        members.append({"uid": u, "name": str(pr.get("name", f"用户{u}")),
                                        "msgs": int(pr.get("msgs", 0) or 0), "last": last or "-",
                                        "days": days, "joined": joined,
                                        "joined_txt": time.strftime("%Y-%m-%d %H:%M", time.localtime(joined)) if joined else "早于机器人进群",
                                        "chips": game_chips.get(sel_cid, {}).get(u, 0),
                                        "warn": warn_counts.get(sel_cid, {}).get(u, 0)})
                    if q:
                        members = [x for x in members if q in x["name"] or q in str(x["uid"])]
                    if fl.get("never"):
                        members = [x for x in members if x["msgs"] == 0]
                    if fl.get("silent"):
                        members = [x for x in members if x["days"] is not None and x["days"] >= fl["silent"]]
                    _d0 = _parse_dt_bj(fl.get("join_from", ""))
                    if _d0:
                        members = [x for x in members if x["joined"] and x["joined"] >= _d0.timestamp()]
                    _d1 = _parse_dt_bj(fl.get("join_to", ""))
                    if _d1:
                        members = [x for x in members if x["joined"] and x["joined"] <= _d1.timestamp()]
                    members.sort(key=lambda x: (-x["joined"], -x["chips"]))
                total = len(members)
                pages = max(1, (total + per - 1) // per)
                page = min(page, pages)
                def _mb(op, uid, label, color="#5b5b76"):
                    return ("<form style='display:inline;margin:0' method='post' action='/memops'>"
                            f"<input type='hidden' name='op' value='{op}'>"
                            f"<input type='hidden' name='cid' value='{sel_cid}'>"
                            f"<input type='hidden' name='uid' value='{uid}'>"
                            f"<button type='submit' class='pbtn' style='background:{color}'>{label}</button></form>")
                admins_map = _group_admins_get(sel_cid) if sel_cid else {}   # 群主/管理员徽章（5 分钟缓存）
                rows_html = ""
                for x in members[(page - 1) * per: page * per]:
                    in_wl = x["uid"] in whitelist.get(sel_cid, set())
                    nm = html.escape(x["name"])
                    av_ch = html.escape((x["name"] or "?")[0].upper())
                    av_bg = _AV_COLORS[x["uid"] % len(_AV_COLORS)]
                    role = admins_map.get(x["uid"])
                    role_html = ("<span class='role owner'>👑 群主</span>" if role == "owner"
                                 else "<span class='role admin'>🛡 管理员</span>" if role == "admin" else "")
                    ops = (_mb("wl_del", x["uid"], "删白", "#8a6d3b") if in_wl
                           else _mb("wl_add", x["uid"], "✅ 加白", "#2f9e5f")) \
                        + " " + _mb("ban", x["uid"], "⛔ 封禁", "#c0392b") \
                        + " " + _mb("kick", x["uid"], "👋 踢出", "#c0392b") \
                        + ("<div class='more'><button type='button' class='pbtn' style='background:#4a4462'>"
                           "更多 ▾</button><div class='menu'>"
                           + _mb("warn_add", x["uid"], "⚠️ 警告 +1", "#b8860b")
                           + " " + _mb("warn_sub", x["uid"], "⚠️ 警告 −1", "#5b5b76")
                           + "</div></div>")
                    rows_html += (f"<tr><td><div style='display:flex;align-items:center;gap:9px;min-width:0'>"
                                  f"<span class='av' style='background:{av_bg}'>{av_ch}</span>"
                                  f"<span style='overflow:hidden;text-overflow:ellipsis;white-space:nowrap'>{nm}{role_html}</span></div></td>"
                                  f"<td><code>{x['uid']}</code></td>"
                                  f"<td>{x['joined_txt']}</td>"
                                  f"<td>{x['last']}</td>"
                                  f"<td>{x['chips']:,}</td>"
                                  f"<td>{x['warn']}</td>"
                                  f"<td style='white-space:nowrap'>{ops}</td></tr>")
                if not rows_html:
                    rows_html = f"<tr><td colspan='7' style='text-align:center;color:#6a6982'>{'左侧选一个群后展示成员' if not sel_cid else '该群暂无成员档案（发过言/进过群才会建档）'}</td></tr>"
                clear_warn_btn = (f"<form style='display:inline;margin:0' method='post' action='/memops'>"
                                  f"<input type='hidden' name='op' value='warn_clear_all'>"
                                  f"<input type='hidden' name='cid' value='{sel_cid}'>"
                                  f"<input type='hidden' name='uid' value='0'>"
                                  "<button type='submit' style='padding:4px 12px;cursor:pointer;background:#8a3b3b;color:#fff;border:none;border-radius:6px'>🧹 清除全部警告</button></form>") if sel_cid else ""
                chips_clear_btn = (f"<form style='display:inline;margin:0' method='post' action='/memops'>"
                                   f"<input type='hidden' name='op' value='chips_clear_all'>"
                                   f"<input type='hidden' name='cid' value='{sel_cid}'>"
                                   f"<input type='hidden' name='uid' value='0'>"
                                   "<button type='submit' onclick=\"return confirm('确定清空该群所有成员的积分？此操作不可恢复！')\" "
                                   "style='padding:4px 12px;cursor:pointer;background:#8a3b3b;color:#fff;border:none;border-radius:6px'>💰 清除全部积分</button></form>") if sel_cid else ""
                impexp_link = ("<a href='/page/points/impexp'><button type='button' style='padding:4px 12px;cursor:pointer;background:#3d6b4f;color:#fff;border:none;border-radius:6px'>📥 积分导入/导出</button></a>") if sel_cid else ""
                body = (f"<h1>{gicon} {gname}</h1><div class='sub'>数据来自成员档案+积分账本+进群事件；封禁/踢出需要 bot 是群管理员</div>{msg}"
                        f"<div class='card'><h3>🧹 批量操作 {chips_clear_btn} {clear_warn_btn} {impexp_link}</h3></div>"
                        "<div class='card' style='margin-top:18px'>"
                        "<form method='get' action='/page/members/mlist' style='display:flex;flex-wrap:wrap;gap:10px;align-items:end'>"
                        f"<div><div class='sub'>群</div><select name='cid' required>{_group_options(selected=sel_cid)}</select></div>"
                        f"<div><div class='sub'>用户名/昵称/ID</div><input type='text' name='q' value='{html.escape(q, quote=True)}'></div>"
                        "<div><label style='font-size:12px'><input type='checkbox' name='never' value='1' "
                        + ("checked" if fl.get("never") else "") + "> 从未发言</label></div>"
                        f"<div><div class='sub'>超过N天未发言</div><input type='number' name='silent' value='{fl.get('silent', 0) or ''}' min='0' style='width:90px'></div>"
                        f"<div><div class='sub'>进群时间从</div><input type='date' name='join_from' value='{html.escape(fl.get('join_from', ''), quote=True)}'></div>"
                        f"<div><div class='sub'>至</div><input type='date' name='join_to' value='{html.escape(fl.get('join_to', ''), quote=True)}'></div>"
                        f"<div><div class='sub'>每页</div><select name='per'>"
                        + "".join(f"<option value='{v}'{' selected' if v == per else ''}>{v}</option>" for v in (10, 20, 50, 100))
                        + "</select></div>"
                        "<button type='submit'>🔍 搜索</button> "
                        "<a href='/page/members/mlist'><button type='button'>♻️ 重置</button></a>"
                        "</form></div>"
                        f"<div class='card' style='margin-top:18px'><div class='sub'>共 {total} 条记录 · 第 {page}/{pages} 页 · 点列头可排序</div>"
                        "<table class='tbl cp'><tr><th data-s>成员</th><th data-s>用户ID</th><th data-s>进群时间</th>"
                        "<th data-s>最近发言</th><th data-s>积分</th><th data-s>警告</th><th>操作</th></tr>"
                        + rows_html + "</table>"
                        "<div style='margin-top:12px;display:flex;gap:10px'>"
                        + (f"<a href='/page/members/mlist?cid={sel_cid}&q={quote(q)}&per={per}&page={page-1}'><button type='button'>‹ 上一页</button></a>" if page > 1 else "")
                        + (f"<a href='/page/members/mlist?cid={sel_cid}&q={quote(q)}&per={per}&page={page+1}'><button type='button'>下一页 ›</button></a>" if page < pages else "")
                        + "</div></div>")
            elif gkey == "members":
                if sub == "join":
                    body = (f"<h1>{gicon} 入群与观察</h1><div class='sub'>新成员观察期与入群欢迎，保存立即生效</div>{msg}"
                            "<div class='card'><form method='post' action='/save'>"
                            "<input type='hidden' name='group' value='members/join'>"
                            + _field_rows("members/join") +
                            _savebar() + "</form></div>")
                else:
                    body = f"<h1>{gicon} {gname}</h1><div class='sub'>数据只读展示，管理操作在群里用命令完成</div>{msg}" + _members_body("records" if sub == "records" else "ops")
            elif gkey == "admin":
                def _btn(action, key, val, label, color="#7c6cf0"):
                    return (f"<form style='display:inline' method='post' action='/adminops2'>"
                            f"<input type='hidden' name='op' value='{action}'>"
                            f"<input type='hidden' name='{key}' value='{val}'>"
                            f"<button style='margin:0;padding:4px 12px;font-size:12px;background:{color};margin-top:0'>{label}</button></form>")
                if sub == "admins":
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
                    body = ("<h1>🛡️ Bot 管理员</h1>"
                            "<div class='sub'>种子管理员来自代码/环境变量，防锁死不可移除；新增的重启不丢。</div>"
                            f"{msg}<div class='card'>"
                            f"<table class='tbl'><tr><th>ID</th><th>操作</th></tr>{admin_rows}</table>"
                            "<form method='post' action='/adminops' style='display:flex;gap:10px;margin-top:14px'>"
                            "<input type='hidden' name='action' value='add'>"
                            "<input type='number' name='uid' list='dl_users_admin' placeholder='用户数字ID' required style='flex:1'>"
                            f"<datalist id='dl_users_admin'>{_all_user_options()}</datalist>"
                            "<button type='submit' style='margin-top:0'>➕ 添加管理员</button></form></div>")
                elif sub == "auth":
                    rows = "".join(f"<tr><td><code>{g}</code> {html.escape(chat_name_cache.get(g) or '（未知群/已解散）')}</td>"
                                   f"<td>{_btn('authdel', 'cid', g, '移除(含数据)', '#e06666')}</td></tr>"
                                   for g in sorted(AUTHORIZED_GROUPS))
                    body = (f"<h1>{gicon} 授权群管理</h1>"
                            f"<div class='sub'>授权群里的玩家才能使用游戏；也可在群里发 /授权</div>{msg}"
                            "<div class='card'><table class='tbl'><tr><th>群</th><th>操作</th></tr>"
                            + (rows or "<tr><td colspan='2'>暂无授权群</td></tr>") + "</table>"
                            "<form method='post' action='/adminops2' style='display:flex;gap:10px;margin-top:14px'>"
                            "<input type='hidden' name='op' value='authadd'>"
                            "<input type='number' name='cid' list='dl_groups_auth' placeholder='群 ID（-100 开头）' required style='flex:1'>"
                            f"<datalist id='dl_groups_auth'>{_group_options()}</datalist>"
                            "<button type='submit' style='margin-top:0'>➕ 添加授权</button></form></div>")
                elif sub == "blacklist":
                    rows = "".join(f"<tr><td><code>{u}</code></td><td>{html.escape(user_names.get(u, ''))}</td>"
                                   f"<td>{_btn('unblack', 'uid', u, '解黑')}</td></tr>"
                                   for u in sorted(BLACKLISTED_USERS))
                    body = (f"<h1>{gicon} 拉黑管理</h1>"
                            f"<div class='sub'>被拉黑的玩家无法使用机器人任何功能；也可群里 /拉黑 /解黑</div>{msg}"
                            "<div class='card'><table class='tbl'><tr><th>ID</th><th>名字</th><th>操作</th></tr>"
                            + (rows or "<tr><td colspan='3'>黑名单为空</td></tr>") + "</table>"
                            "<form method='post' action='/adminops2' style='display:flex;gap:10px;margin-top:14px'>"
                            "<input type='hidden' name='op' value='black'>"
                            "<input type='number' name='uid' list='dl_users_black' placeholder='用户 ID' required style='flex:1'>"
                            f"<datalist id='dl_users_black'>{_all_user_options()}</datalist>"
                            "<button type='submit' style='margin-top:0;background:#e06666'>🔨 拉黑</button></form></div>")
                elif sub == "god":
                    god = next((u for u, ts in user_titles.items() if TITLE_GAMBLING_GOD in ts), None)
                    cur = (f"<code>{god}</code> {html.escape(user_names.get(god, ''))}" if god else "暂无（全局唯一，封新撤旧）")
                    body = (f"<h1>{gicon} 赌神称号</h1><div class='sub'>全局唯一：封新人自动撤销上任</div>{msg}"
                            "<div class='card'><table class='tbl'><tr><th>现任赌神</th></tr>"
                            f"<tr><td>{cur}　{_btn('godrevoke', 'uid', god or 0, '撤销', '#e06666') if god else ''}</td></tr></table>"
                            "<form method='post' action='/adminops2' style='display:flex;gap:10px;margin-top:14px'>"
                            "<input type='hidden' name='op' value='godgrant'>"
                            "<input type='number' name='uid' list='dl_users_god' placeholder='用户 ID' required style='flex:1'>"
                            f"<datalist id='dl_users_god'>{_all_user_options()}</datalist>"
                            "<button type='submit' style='margin-top:0'>👑 封赌神</button></form></div>")
                elif sub == "seasonpts":
                    body = (f"<h1>{gicon} 排位分调整</h1>"
                            f"<div class='sub'>给玩家加/减排位分（正加负减）；赛季未开始时需玩家已在赛季名单</div>{msg}"
                            "<div class='card'><form method='post' action='/adminops2'>"
                            "<input type='hidden' name='op' value='seasonpts'>"
                            "<div class='row'><div class='lbl'>群 ID<small>选群后用户 ID 自动带出该群成员</small></div>"
                            f"<select name='cid' data-users-for='dl_season_uid' required>{_group_options()}</select></div>"
                            "<div class='row'><div class='lbl'>用户 ID</div>"
                            "<input type='number' name='uid' list='dl_season_uid' required>"
                            "<datalist id='dl_season_uid'></datalist></div>"
                            "<div class='row'><div class='lbl'>排位分变动<small>正数=加，负数=减</small></div>"
                            "<input type='number' name='amount' value='100' required></div>"
                            "<button type='submit'>💾 执行调整</button></form></div>")
                elif sub == "fundflow":
                    sel = uid or 0
                    recv_map, send_map = defaultdict(int), defaultdict(int)
                    for e in list(ledger) + list(game_flows):
                        if sel and e.get("to") == sel: recv_map[e.get("frm")] += e.get("amt", 0)
                        if sel and e.get("frm") == sel: send_map[e.get("to")] += e.get("amt", 0)
                    def _ff_rows(m, empty_txt):
                        if not m: return f"<tr><td colspan='3'>{empty_txt}</td></tr>"
                        out = []
                        for peer, total in sorted(m.items(), key=lambda x: -x[1])[:10]:
                            red = " style='color:#ff7b7b;font-weight:700'" if total >= FUND_FLOW_ALERT else ""
                            out.append(f"<tr{red}><td><code>{peer}</code> {html.escape(user_names.get(peer, ''))}</td>"
                                       f"<td>{total}</td><td>{'🚨 超阈值，重点核查' if total >= FUND_FLOW_ALERT else ''}</td></tr>")
                        return "".join(out)
                    _flows = sorted([x for x in list(ledger) + list(game_flows) if sel in (x.get("frm"), x.get("to"))],
                                    key=lambda x: str(x.get("ts", "")))[-15:]
                    detail = "".join(
                        f"<tr><td>{html.escape(str(e.get('ts', '')))}</td>"
                        f"<td><code>{e.get('frm')}</code> → <code>{e.get('to')}</code></td>"
                        f"<td>{html.escape(str(e.get('typ', '')))}</td><td>{e.get('amt', 0)}</td></tr>"
                        for e in reversed(_flows))
                    sel_txt = f"<code>{sel}</code> {html.escape(user_names.get(sel, ''))}" if sel else ""
                    body = (f"<h1>{gicon} 资金流审查</h1>"
                            f"<div class='sub'>红包/转赠/游戏送分（德州·金花·竞猜故意输牌）等人对人转移全部记账；兑换周边前先查一眼，小号一查一个准。累计 ≥ {FUND_FLOW_ALERT} 标红</div>{msg}"
                            "<div class='card'><form method='get' action='/page/admin/fundflow'>"
                            "<div class='row'><div class='lbl'>选择要审查的用户</div>"
                            f"<select name='uid' required>{_all_user_options(sel)}</select></div>"
                            "<button type='submit' style='margin-top:10px'>🔍 审查</button></form></div>"
                            + (f"<div class='card'><h3>给 {sel_txt} 送钱的 TOP（收到）</h3>"
                               f"<table class='tbl'><tr><th>来源</th><th>累计</th><th>警示</th></tr>{_ff_rows(recv_map, '该用户没有收钱记录')}</table>"
                               f"<h3 style='margin-top:16px'>{sel_txt} 送钱的 TOP（转出）</h3>"
                               f"<table class='tbl'><tr><th>去向</th><th>累计</th><th>警示</th></tr>{_ff_rows(send_map, '该用户没有转出记录')}</table>"
                               f"<h3 style='margin-top:16px'>最近明细（15 笔）</h3>"
                               "<table class='tbl'><tr><th>时间</th><th>流向</th><th>类型</th><th>金额</th></tr>"
                               + (detail or "<tr><td colspan='4'>暂无明细</td></tr>") + "</table></div>" if sel else "")
                            + "<div class='card'><form method='post' action='/save'>"
                              "<input type='hidden' name='group' value='admin/fundflow'>"
                              + _field_rows("admin/fundflow") +
                              _savebar("保存阈值") + "</form></div>")
                else:
                    first = SUBPAGES["admin"][0][0]
                    if first == sub:
                        # 防自递归：兜底要跳的子页就是当前子页 → 渲染占位页，绝不能自己跳自己
                        body = f"<h1>{gicon} {gname}</h1><div class='sub'>该子页暂未开通</div>{msg}"
                    else:
                        return _admin_page(gkey, sub=first, saved=saved, bad=bad, note=note, err=err)
            elif gkey == "commands":
                rows = []
                for fn_name in sorted(_HANDLERS_BY_NAME):
                    cur = CMD_ALIAS_OVERRIDES.get(fn_name)
                    if cur is None:
                        cur = ",".join(sorted(a for a, f in BASE_CMD_ALIASES.items() if f.__name__ == fn_name))
                    rows.append("<tr><td style='white-space:nowrap'><code>" + fn_name + "</code></td>"
                                "<td><input type='text' name='" + html.escape(fn_name) +
                                "' value=\"" + html.escape(cur) + "\" style='width:100%'></td></tr>")
                menu_txt = "\n".join(f"{c_} {d_}" for c_, d_ in TG_MENU)
                _cf = cmd_conflicts()
                _cf_html = ""
                if _cf:
                    _li = "".join(f"<tr><td><code>{html.escape(a)}</code></td>"
                                  f"<td>{html.escape('、'.join(fns))}</td></tr>" for a, fns in _cf)
                    _cf_html = ("<div class='err' style='margin-top:14px'>⚠️ 有 %d 个触发词被多个命令占用，"
                                "排在后面的会顶掉前面的（表现为某命令在群里没反应）：</div>"
                                "<table class='tbl'><tr><th style='width:180px'>触发词</th><th>被这些命令占用</th></tr>"
                                % len(_cf) + _li + "</table>")
                else:
                    _cf_html = ("<div class='ok' style='margin-top:14px'>✅ 触发词体检通过：没有重复占用</div>")
                body = (f"<h1>{gicon} 命令管理</h1>"
                        "<div class='sub'>每个命令的触发词随意改（逗号分隔，可中文可英文）；保存后<b>立即生效</b>并持久化。"
                        "这里是触发词的<b>唯一入口</b>，帮助文案里显示的指令名会自动跟着改。"
                        f"Telegram / 菜单每行一条「命令 描述」，命令仅限英文小写/数字/下划线</div>{msg}{err}"
                        "<div class='card'><form method='post' action='/cmdaliases'>"
                        "<h3>⌨️ 命令触发词</h3>"
                        "<table class='tbl'><tr><th style='width:150px'>命令</th><th>触发词（逗号分隔）</th></tr>"
                        + "".join(rows) + "</table>" + _cf_html
                        + "<h3 style='margin-top:20px'>📱 Telegram / 菜单</h3>"
                        "<textarea name='tg_menu' rows='14' style='width:100%;font-family:inherit'>" + html.escape(menu_txt) + "</textarea>" +
                        _savebar("保存全部命令设置") + "</form></div>")
            elif gkey == "security":
                body = (f"<h1>{gicon} {gname}</h1><div class='sub'>修改后台登录密码</div>{msg}"
                        "<form method='post' action='/save'>"
                        "<input type='hidden' name='group' value='security'>"
                        "<label>新密码（至少4位）<input type='password' name='new_password'></label>"
                        "<button type='submit'>💾 保存密码</button></form>")
# 群组抽奖独立组（从积分系统移出，无子页）：必须在 elif sub: 之前拦截
            elif gkey == "lottery":
                sname = gname  # 顶层分支：组名直接取参数（原 elif sub: 内由子页表推导）
                # 群组抽奖页：新增抽奖表单 + 活动列表（可取消）+ 配置表单
                def _fmt_ts(t):
                    try: return time.strftime("%m-%d %H:%M", time.localtime(float(t)))
                    except Exception: return "-"
                def _row(lo):
                    cid = lo.get("chat_id", -1)
                    status = lo.get("status", "?")
                    active = status == "open"
                    badges = {"open": "<span style='color:#6fd08c'>进行中</span>",
                              "drawing": "<span style='color:#f0c060'>开奖中</span>",
                              "finished": "<span style='color:#8a89a0'>已结束</span>",
                              "cancelled": "<span style='color:#f09595'>已取消</span>"}
                    ends_in = ""
                    if active:
                        left = int(lo["end_ts"] - time.time())
                        ends_in = f" · 剩 {left}s" if left > 0 else " · 到点开奖中"
                    winners = lo.get("winners") or []
                    win_txt = f"{len(winners)} 人" if winners else "—"
                    fee_txt = f" {int(lo.get('fee', 0))}分/人" if lo.get("fee") else " 免费"
                    cancel_btn = (f"<a class='q' href='/lottery_cancel?cid={cid}' "
                                  f"onclick=\"return confirm('取消该抽奖并退还参与费？')\">🛑 取消</a>" if active else "")
                    return (f"<tr><td><code>{cid}</code> {html.escape(chat_name_cache.get(cid) or '')}</td>"
                            f"<td>{html.escape(str(lo.get('title', ''))[:24])}</td>"
                            f"<td>{badges.get(status, status)}{ends_in}</td>"
                            f"<td>{len(lo.get('participants', []))}</td>"
                            f"<td>{win_txt}</td>"
                            f"<td>{fee_txt}</td>"
                            f"<td>{_fmt_ts(lo.get('start_ts'))}</td>"
                            f"<td>{cancel_btn}</td></tr>")
                # 进行中优先；其余按 start_ts 倒序
                items = list(lotteries.items())
                items.sort(key=lambda kv: (kv[1].get("status") != "open", -(kv[1].get("start_ts") or 0)))
                rows_html = "".join(_row(lo) for _, lo in items[:20])
                if not rows_html:
                    rows_html = "<tr><td colspan='8' style='text-align:center;color:#6a6982'>暂无活动，用上方表单创建第一个</td></tr>"
                status_html = ("<div class='err'>⚠️ 群组抽奖当前已关闭，先打开下方「群组抽奖总开关」</div>"
                               if not sget("LOTTERY_ENABLED") else "")
                body = (f"<h1>{gicon} {sname}</h1>"
                        f"<div class='sub'>在这里创建抽奖 → 机器人自动发到群里 → 群成员发「{html.escape(sget('LOTTERY_KEYWORD'))}」参与 → 到点自动开奖</div>"
                        f"{msg}{err}{status_html}" +
                        # 新增抽奖表单（照阿福格式：描述/关键词/开奖方式下拉/结构化奖品行）
                        "<div class='card'><h3>➕ 新增抽奖</h3>"
                        "<form method='post' action='/lottery_create' id='lottery_form'>"
                        "<div class='row'><div class='lbl'>发到哪个群 *</div>"
                        f"<select name='cid' required>{_group_options()}</select></div>"
                        "<div class='row'><div class='lbl'>抽奖标题 *</div>"
                        "<input type='text' name='title' maxlength='50' required placeholder='例：群友福利'></div>"
                        "<div style='padding:12px 0;border-bottom:1px solid var(--border)'>"
                        "<div class='lbl'>抽奖描述<small>（可选）显示在公告标题下方</small></div>"
                        "<textarea name='desc' rows='2' placeholder='活动说明、注意事项等（可留空）'></textarea></div>"
                        "<div class='row'><div class='lbl'>参与关键词 *</div>"
                        f"<input type='text' name='keyword' maxlength='20' value='{html.escape(sget('LOTTERY_KEYWORD'))}' placeholder='群友发这个词参与抽奖'></div>"
                        "<div class='row'><div class='lbl'>开奖方式 *</div>"
                        "<select name='mode' id='mode_sel'>"
                        "<option value='time'>定时开奖</option>"
                        "<option value='duration'>倒计时开奖</option></select></div>"
                        "<div class='row' id='row_time'><div class='lbl'>开奖时间 *<small>输入的时间将按北京时间解析执行：20:00 / 09-08 20:00 / 2026-09-08 20:00</small></div>"
                        "<input type='text' name='endtime' id='endtime' placeholder='例：21:30 或 09-08 20:00'></div>"
                        "<div class='row' id='row_duration' style='display:none'><div class='lbl'>持续秒数 *<small>到点自动开奖（10 ~ 604800）</small></div>"
                        f"<input type='number' name='duration' id='duration' value='{max(10, int(sget('LOTTERY_DEFAULT_DURATION')))}' min='10'></div>"
                        "<div style='padding:12px 0;border-bottom:1px solid var(--border)'>"
                        "<div class='lbl'>奖品设置 *</div>"
                        "<div id='prize_rows'>"
                        "<div class='row' style='display:flex;gap:10px'>"
                        "<input type='text' name='prize_name' placeholder='奖品名称 *' required style='flex:2'>"
                        "<input type='number' name='prize_count' value='1' min='1' placeholder='数量' style='flex:1'></div></div>"
                        "<button type='button' onclick='add_prize()' style='margin-top:8px;background:#3b3c5c'>➕ 添加奖品</button></div>"
                        "<div class='row'><div class='lbl'>参与条件（可选）<small>最低持有积分；留空或填 0=不限制</small></div>"
                        "<input type='number' name='min_bal' min='0' placeholder='例：500'></div>"
                        "<button type='submit'>🎉 创建并发布到群</button></form>"
                        "<script>"
                        "function add_prize(){"
                        "var d=document.createElement('div');"
                        "d.className='row';d.style.cssText='display:flex;gap:10px;margin-top:8px';"
                        "d.innerHTML=\"<input type='text' name='prize_name' placeholder='奖品名称' style='flex:2'>"
                        "<input type='number' name='prize_count' value='1' min='1' style='flex:1'>\";"
                        "document.getElementById('prize_rows').appendChild(d);}"
                        "document.getElementById('mode_sel').addEventListener('change',function(){"
                        "var t=this.value==='time';"
                        "document.getElementById('row_time').style.display=t?'':'none';"
                        "document.getElementById('row_duration').style.display=t?'none':'';"
                        "document.getElementById('endtime').required=t;"
                        "document.getElementById('duration').required=!t;"
                        "});"
                        "document.getElementById('mode_sel').dispatchEvent(new Event('change'));"
                        "</script></div>" +
                        # 活动列表
                        _flt_bar("/page/lottery") +
                        "<div class='card'><h3>📋 活动列表（最近 20 条，进行中置顶）</h3>"
                        "<table class='tbl'><tr><th>群</th><th>标题</th><th>状态</th><th>参与</th><th>中奖</th><th>参与费</th><th>开局</th><th>操作</th></tr>"
                        f"{rows_html}</table></div>"
                        # 配置表单
                        f"<div class='card'><h3>⚙️ 配置</h3><form method='post' action='/save'>"
                        f"<input type='hidden' name='group' value='lottery'>"
                        + _field_rows("lottery")
                        + "<div class='sub' style='margin-top:16px'>消息模板支持占位符："
                          f"<code>{'{title}'}</code> <code>{'{nick}'}</code> <code>{'{n}'}</code> <code>{'{balance}'}</code> "
                          f"<code>{'{prize_list}'}</code> <code>{'{keyword}'}</code> <code>{'{duration}'}</code> "
                          f"<code>{'{winners}'}</code> <code>{'{reason}'}</code></div>" +
                        _savebar("保存全部抽奖设置") + "</form></div>")
            elif gkey == "invite":
                # 邀请系统六子页：配置/记录/统计/汇总/前置条件/审核
                subs_inv = {k: n for k, n in SUBPAGES.get("invite", [])}
                sub = sub or "config"
                sname = subs_inv.get(sub, sub)
                sel_icid = (flt or {}).get("cid", 0)
                def _inv_icid(v):   # int 化记录 cid（记录里存的是 int）
                    try: return int(v)
                    except (TypeError, ValueError): return 0
                def _inv_bar(action):
                    return ("<form method='get' action='" + action + "' style='margin-bottom:10px'>"
                            "<div class='lbl'>群组筛选</div><select name='cid' onchange='this.form.submit()'>"
                            "<option value='0'>全部群</option>" + _group_options(selected=sel_icid)
                            + "</select><noscript><button style='margin:0'>查看</button></noscript></form>")
                if sub == "config":
                    warn_html = ("<div class='err'>⚠️ 邀请系统当前已关闭</div>" if not sget("INVITE_ENABLED") else "")
                    body = (f"<h1>{gicon} {gname}</h1>"
                            f"<div class='sub'>群里发「<code>{html.escape(str(INVITE_LINK_CMD))}</code>」领专属邀请链接 → 新朋友经链接进群 → 本群达标后邀请人得奖励"
                            f"（群内发「{html.escape(str(INVITE_RANK_ALL_CMD))}」看排行）</div>{msg}{warn_html}"
                            "<div class='card'><h3>🎟️ 使用说明</h3>"
                            "<div class='sub'>链接经 Telegram 官方 invite_link 事件追踪，进群先记账为「待达标」；"
                            "被邀请人在本群发言/净赚积分达到「合格结算」页的质量要求后自动发奖（也可点群里的「刷新进度」立即重判）；"
                            "每人最多发放次数见下方「每人最多发放奖励次数」；被邀请人退群后不计排行。</div></div>"
                            "<div class='card' style='margin-top:18px'><form method='post' action='/save'>"
                            "<input type='hidden' name='group' value='invite/config'>"
                            + _field_rows("invite/config") +
                            "<div class='sub' style='margin-top:16px'>模板占位符：邀请成功通知 <code>{inviter}</code> <code>{invitee}</code> <code>{reward}</code>；"
                            "链接消息 <code>{link}</code> <code>{reward}</code>；排行行 <code>{i}</code> <code>{name}</code> <code>{count}</code></div>" +
                            _savebar("保存邀请设置") + "</form></div>")
                elif sub == "records":
                    _recs = [(k, r) for k, r in invite_records.items()
                             if not sel_icid or _inv_icid(r.get("cid")) == sel_icid]
                    def _rec_badge(r):
                        if _rec_rejected(r):
                            return "<span style='color:#f09595'>拒绝</span>"
                        if r.get("ad_flag"):
                            return "<span style='color:#f09595'>连坐·发广告</span>"
                        if _rec_qualified(r):
                            return ("<span style='color:#6fd08c'>合格·已发放</span>" if _rec_awarded(r)
                                    else "<span style='color:#f0c060'>合格·超额未发</span>")
                        return "<span style='color:#8a89a0'>待达标</span>"
                    rows_html = ""
                    for k, r in sorted(_recs, key=lambda kv: kv[1].get("ts", ""), reverse=True)[:100]:
                        badge = _rec_badge(r)
                        if r.get("left"):
                            badge += " <span style='color:#8a89a0'>(已退群)</span>"
                        if r.get("note") and _rec_rejected(r):
                            badge += f" <span style='color:#f09595'>{html.escape(str(r.get('note', '')))}</span>"
                        rows_html += (f"<tr><td><code>{k}</code></td>"
                                      f"<td><code>{r.get('inviter', '')}</code></td>"
                                      f"<td><code>{r.get('invitee', '')}</code> {html.escape(str(r.get('invitee_name', '')))}</td>"
                                      f"<td>{r.get('ts', '')}</td><td>{badge}</td>"
                                      f"<td>{r.get('award', 0)}</td>"
                                      f"<td><a class='q' href='/invite_del/{k}' onclick=\"return confirm('删除该邀请记录？')\">🗑 删除</a></td></tr>")
                    if not rows_html:
                        rows_html = "<tr><td colspan='7' style='text-align:center;color:#6a6982'>暂无邀请记录</td></tr>"
                    body = (f"<h1>{gicon} 邀请记录</h1><div class='sub'>最近 100 条邀请记录；待达标=进群未达质量要求，达标后自动转合格；退群自动标失效</div>{msg}"
                            "<div class='card'>" + _inv_bar("/page/invite/records") +
                            "<form method='post' action='/invite_clear' style='margin-bottom:10px' "
                            "onsubmit=\"return confirm('确认清空全部邀请记录与邀请链接？此操作不可恢复！')\">"
                            "<button style='background:#8a3b3b;color:#fff'>🧹 清空全部邀请数据</button></form>"
                            "<form method='post' action='/invite_clear_group' style='margin-bottom:10px;display:flex;gap:8px;align-items:center' "
                            "onsubmit=\"return confirm('确认删除所选群的全部邀请记录？其他群不受影响，此操作不可恢复！')\">"
                            f"<select name='cid' required><option value=''>选择要清记录的群</option>{_group_options(selected=sel_icid)}</select>"
                            "<button style='background:#a3663b;color:#fff'>🗑 删除该群记录</button></form>"
                            "<table class='tbl'><tr><th>记录ID</th><th>邀请人</th><th>被邀请人</th><th>时间</th><th>状态</th><th>奖励</th><th>操作</th></tr>"
                            + rows_html + "</table></div>")
                elif sub == "daily":
                    daily_counts = defaultdict(int)
                    for r in invite_records.values():
                        if _rec_ok(r) and (not sel_icid or _inv_icid(r.get("cid")) == sel_icid):
                            daily_counts[str(r.get("ts", ""))[:10]] += 1
                    rows_html = "".join(f"<tr><td>{d}</td><td>{n}</td></tr>"
                                        for d, n in sorted(daily_counts.items(), reverse=True)[:60])
                    if not rows_html:
                        rows_html = "<tr><td colspan='2' style='text-align:center;color:#6a6982'>暂无数据</td></tr>"
                    body = (f"<h1>{gicon} 统计</h1><div class='sub'>每日合格邀请数（最近 60 天，按进群日计）</div>{msg}"
                            "<div class='card'>" + _inv_bar("/page/invite/daily") +
                            "<table class='tbl'><tr><th>日期</th><th>合格邀请</th></tr>"
                            + rows_html + "</table></div>")
                elif sub == "summary":
                    sums = defaultdict(lambda: {"ok": 0, "award": 0, "pend": 0})
                    for r in invite_records.values():
                        if (not sel_icid or _inv_icid(r.get("cid")) == sel_icid):
                            if _rec_rejected(r) or r.get("left"):
                                continue
                            if _rec_valid(r):
                                sums[r.get("inviter")]["ok"] += 1
                                sums[r.get("inviter")]["award"] += int(r.get("award", 0) or 0)
                            elif not _rec_qualified(r):
                                sums[r.get("inviter")]["pend"] += 1
                            # 合格但发过广告（连坐）→ 既不算合格也不算待达标，只保留已发奖励
                    rows_html = ""
                    for uid, s in sorted(sums.items(), key=lambda kv: -kv[1]["ok"])[:50]:
                        rows_html += (f"<tr><td><code>{uid}</code> {html.escape(user_names.get(uid, ''))}</td>"
                                      f"<td>{s['ok']}</td><td>{s['pend']}</td><td>{s['award']}</td></tr>")
                    if not rows_html:
                        rows_html = "<tr><td colspan='4' style='text-align:center;color:#6a6982'>暂无数据</td></tr>"
                    body = (f"<h1>{gicon} 汇总</h1><div class='sub'>按邀请人汇总（未退群，前 50）：合格=已达标人数，待达标=进群未达标，累计奖励</div>{msg}"
                            "<div class='card'>" + _inv_bar("/page/invite/summary") +
                            "<table class='tbl'><tr><th>邀请人</th><th>合格</th><th>待达标</th><th>累计奖励</th></tr>"
                            + rows_html + "</table></div>")
                elif sub == "qualify":
                    body = (f"<h1>{gicon} 合格结算</h1>"
                            f"<div class='sub'>被邀请人进群先记账，<b>在本群</b>达到下列质量要求才算「合格」并发放邀请奖励"
                            f"（{sget('INVITE_REWARD')} 积分/人，每人上限 {sget('INVITE_REWARD_TIMES')} 次）；发言/积分达标事件驱动自动结算，超额只计合格不再发；"
                            f"头像/用户名要求进群时检查，不满足直接拒绝永不发（防小号白嫖）。</div>{msg}"
                            "<div class='card'><form method='post' action='/save'>"
                            "<input type='hidden' name='group' value='invite/qualify'>"
                            + _field_rows("invite/qualify") +
                            _savebar("保存合格结算设置") + "</form></div>")
                else:
                    body = f"<h1>{gicon} {gname}</h1><div class='sub'>该子页暂未开通</div>{msg}"
            elif sub:
                # 子页面制（照阿福模板：积分相关 → 积分设置/每日签到/…）
                subs = {k: n for k, n in SUBPAGES.get(gkey, [])}
                sname = subs.get(sub, sub)
                if gkey == "points" and sub == "adjust":
                    body = (f"<h1>{gicon} {sname}</h1>"
                            f"<div class='sub'>直接给玩家加/减统一积分（正数加、负数减），立即生效并落盘；等效群里的 /add 命令</div>{msg}"
                            "<div class='card'><form method='post' action='/points_adj'>"
                            "<div class='row'><div class='lbl'>群 ID<small>下拉选择；选群后用户 ID 自动带出该群成员</small></div>"
                            f"<select name='cid' data-users-for='dl_adj_uid' required>{_group_options()}</select></div>"
                            "<div class='row'><div class='lbl'>用户 ID<small>点输入框可从该群成员里选，也可手输</small></div>"
                            "<input type='number' name='uid' list='dl_adj_uid' required>"
                            "<datalist id='dl_adj_uid'></datalist></div>"
                            "<div class='row'><div class='lbl'>积分变动<small>正数=加分，负数=扣分，0 无效</small></div>"
                            "<input type='number' name='amount' value='1000' required></div>"
                            "<button type='submit'>💾 执行加减分</button></form></div>")
                elif gkey == "points" and sub == "impexp":
                    opts = _group_options()
                    body = (f"<h1>{gicon} {sname}</h1>"
                            f"<div class='sub'>按群导出/导入积分。导入会<b>覆盖</b>该群已有积分，务必先用模板核对格式</div>{msg}{err}"
                            "<div class='card'><h3>📥 导出</h3>"
                            "<form method='get' action='/points_export'>"
                            f"<div class='row'><div class='lbl'>选择群</div><select name='cid'>{opts}</select></div>"
                            "<button type='submit'>⬇ 导出 CSV（Excel 可直接打开）</button></form></div>"
                            "<div class='card'><h3>📤 导入</h3>"
                            "<div class='sub'>表头必须包含：用户ID 和 积分（昵称列可选）。同群已有积分将被覆盖</div>"
                            "<p><a href='/points_template'>⬇ 下载模板</a>　请先下载模板，按格式填写</p>"
                            "<form method='post' action='/points_import' enctype='multipart/form-data'>"
                            f"<div class='row'><div class='lbl'>导入到群</div><select name='cid'>{opts}</select></div>"
                            "<div class='row'><div class='lbl'>数据文件<small>.csv / .xls / .xlsx</small></div>"
                            "<input type='file' name='file' accept='.csv,.xls,.xlsx' required></div>"
                            "<div class='row'><div class='lbl'>⚠️ 覆盖确认<small>导入为覆盖式写入，不可撤销</small></div>"
                            "<label style='display:flex;gap:8px;align-items:center'><input type='checkbox' name='confirm' value='1' required style='width:auto'> 我确认覆盖所选群的全部积分</label></div>"
                            "<button type='submit'>✅ 确认导入</button></form></div>")
                elif gkey == "points" and sub == "level":
                    # 等级表：名称 / 最低积分 / 状态 / 消息权限（8 类勾选），支持行内编辑
                    _normalize_levels()
                    edit_i = int((flt or {}).get("edit", -1))
                    if not (0 <= edit_i < len(POINT_LEVELS)):
                        edit_i = -1
                    lv_rows = ""
                    for i, x in enumerate(POINT_LEVELS):
                        on = int(x.get("on", 1) or 0)
                        st = ("<span style='color:#6fd08c'>启用</span>" if on
                              else "<span style='color:#8a89a0'>停用</span>")
                        if i == edit_i:
                            # 编辑态：整行换成表单（权限 8 勾选 + 状态开关）
                            lv_rows += (
                                f"<tr style='background:rgba(120,120,200,.08)'>"
                                f"<td colspan='5'><form method='post' action='/level_edit'>"
                                f"<input type='hidden' name='i' value='{i}'>"
                                f"<div style='display:flex;gap:10px;align-items:flex-end;flex-wrap:wrap'>"
                                f"<div style='flex:2;min-width:140px'><div class='lbl'>等级名称</div>"
                                f"<input type='text' name='name' value='{html.escape(str(x.get('name', '')))}' "
                                f"required maxlength='12' style='width:100%'></div>"
                                f"<div style='flex:1;min-width:110px'><div class='lbl'>最低积分</div>"
                                f"<input type='number' name='value' value='{int(x.get('value', 0) or 0)}' "
                                f"required min='0' style='width:100%'></div>"
                                f"<div style='min-width:110px'><div class='lbl'>状态</div>"
                                f"<label class='tg'><input type='checkbox' name='on' value='1'"
                                f"{' checked' if on else ''}><span class='sl'></span></label></div></div>"
                                f"<div style='margin-top:10px'><div class='lbl'>等级消息权限"
                                f"<small>勾选=允许；未勾选的消息类型会被撤回并提示</small></div>"
                                f"{_perm_boxes(x.get('perms'))}</div>"
                                f"<div style='display:flex;gap:10px;margin-top:10px'>"
                                f"<button style='margin:0'>💾 保存</button>"
                                f"<a href='/page/points/level' style='align-self:center'>取消</a></div>"
                                f"</form></td></tr>")
                        else:
                            lv_rows += (
                                f"<tr><td><b>L{i + 1}</b> {html.escape(str(x.get('name', '?')))}</td>"
                                f"<td>{int(x.get('value', 0) or 0)}</td><td>{st}</td>"
                                f"<td>{_perm_summary(x.get('perms'))}</td>"
                                f"<td><a href='/page/points/level?edit={i}'>编辑</a> · "
                                f"<a href='/level_toggle/{i}'>{'停用' if on else '启用'}</a> · "
                                f"<a href='/level_del/{i}' style='color:#f09595'>删除</a></td></tr>")
                    if not lv_rows:
                        lv_rows = ("<tr><td colspan='5' style='text-align:center;color:#6a6982'>"
                                   "暂无等级数据，先新增等级</td></tr>")
                    body = (f"<h1>{gicon} {sname}</h1><div class='sub'>按「累计获得」判定等级（消费不掉级，只升不降）；"
                            f"停用的等级不参与判定与权限；升级自动群内通知（下方可开关）。保存立即生效</div>{msg}"
                            "<div class='card'><h3>🎖 等级列表（按最低积分升序）</h3>"
                            "<table class='tbl'><tr><th>等级名称</th><th>最低积分</th><th>状态</th>"
                            "<th>消息权限</th><th>操作</th></tr>"
                            + lv_rows + "</table>"
                            "<form method='post' action='/level_add' style='margin-top:16px'>"
                            "<h3 style='margin-bottom:8px'>➕ 新增积分等级</h3>"
                            "<div style='display:flex;gap:10px;align-items:flex-end;flex-wrap:wrap'>"
                            "<div style='flex:2;min-width:140px'><div class='lbl'>等级名称</div>"
                            "<input type='text' name='name' placeholder='≤12字，如 铜牌' required maxlength='12' style='width:100%'></div>"
                            "<div style='flex:1;min-width:110px'><div class='lbl'>最低积分</div>"
                            "<input type='number' name='value' placeholder='如 100' required min='0' style='width:100%'></div>"
                            "<div style='min-width:110px'><div class='lbl'>状态</div>"
                            "<label class='tg'><input type='checkbox' name='on' value='1' checked>"
                            "<span class='sl'></span></label></div></div>"
                            "<div style='margin-top:10px'><div class='lbl'>等级消息权限"
                            "<small>勾选=允许；不勾则拦截。默认全勾（不限制）</small></div>"
                            + _perm_boxes(LEVEL_PERM_DEFAULT) +
                            "</div><button style='margin-top:10px'>➕ 新增等级</button></form></div>"
                            "<div class='card' style='margin-top:18px'><form method='post' action='/save'>"
                            "<input type='hidden' name='group' value='points/level'>"
                            + _field_rows("points/level")
                            + "<div class='sub' style='margin-top:16px'>占位符：<code>{name}</code> <code>{level}</code> <code>{balance}</code>；群内发「"
                              + html.escape(str(LEVEL_CMD)) + "」查询自己的等级"
                            + "（查询触发词在「命令管理」页改，本页不重复配置以免两处打架）</div>" +
                            _savebar("保存通知设置") + "</form></div>")
                elif gkey == "points" and sub == "levelguard":
                    body = (f"<h1>{gicon} {sname}</h1>"
                            f"<div class='sub'>按等级限制群成员可发送的消息类型：越权消息立即撤回并提示，"
                            f"窗口内连续违规按下方规则惩罚。等级权限在「积分等级」页逐级勾选</div>{msg}"
                            "<div class='card'><form method='post' action='/save'>"
                            "<input type='hidden' name='group' value='points/levelguard'>"
                            + _field_rows("points/levelguard")
                            + "<div class='sub' style='margin-top:16px'>占位符：<code>{name}</code> <code>{level}</code> "
                              "<code>{kind}</code>（消息类型）<code>{seconds}</code>（禁言秒数）</div>"
                            + _savebar("保存管控设置") + "</form></div>"
                            "<div class='card' style='margin-top:18px'><h3>📋 当前等级权限一览</h3>"
                            "<div class='sub'>改权限请去「积分等级」页点编辑</div>"
                            + "<table class='tbl'><tr><th>等级</th><th>最低积分</th><th>允许发送</th></tr>"
                            + "".join(
                                f"<tr><td><b>L{i + 1}</b> {html.escape(str(x.get('name', '?')))}</td>"
                                f"<td>{int(x.get('value', 0) or 0)}</td><td>{_perm_summary(x.get('perms'))}</td></tr>"
                                for i, x in enumerate(POINT_LEVELS))
                            + "</table></div>")
                elif gkey == "points" and sub == "mall":
                    mall_rows = ""
                    for i, x in enumerate(MALL_ITEMS):
                        on = bool(x.get("on", True))
                        st = "<span style='color:#6fd08c'>上架</span>" if on else "<span style='color:#8a89a0'>下架</span>"
                        mall_rows += (f"<tr><td>{html.escape(str(x.get('name', '?')))}</td>"
                                      f"<td>{_mall_price(x)}</td>"
                                      f"<td>{html.escape(str(x.get('desc', '') or ''))}</td><td>{st}</td>"
                                      f"<td><a href='/mall_toggle/{i}'>{'下架' if on else '上架'}</a> · "
                                      f"<a href='/mall_del/{i}' style='color:#f09595'>删除</a></td></tr>")
                    if not mall_rows:
                        mall_rows = ("<tr><td colspan='5' style='text-align:center;color:#6a6982'>"
                                     "暂无商品数据，先新增商品</td></tr>")
                    body = (f"<h1>{gicon} {sname}</h1><div class='sub'>玩家发「积分商城」看商品、发「购买 编号」兑换，管理员人工发货。保存立即生效</div>{msg}"
                            "<div class='card'><h3>🛍 商品列表</h3>"
                            "<table class='tbl'><tr><th>商品</th><th>价格(积分)</th><th>说明</th><th>状态</th><th>操作</th></tr>"
                            + mall_rows + "</table>"
                            "<form method='post' action='/mall_add' style='display:flex;gap:10px;margin-top:12px'>"
                            "<input type='text' name='name' placeholder='商品名称' required style='flex:2'>"
                            "<input type='number' name='price' placeholder='价格(积分)' required min='1' style='flex:1'>"
                            "<input type='text' name='desc' placeholder='说明(可选)' style='flex:2'>"
                            "<button style='margin:0'>➕ 新增商品</button></form></div>"
                            "<div class='card' style='margin-top:18px'><form method='post' action='/save'>"
                            "<input type='hidden' name='group' value='points/mall'>"
                            + _field_rows("points/mall") + _savebar("保存商城设置") + "</form></div>")
                elif gkey == "points" and sub == "rule":
                    cap = f"每日上限 {sget('CHAT_DAILY_CAP')} 分" if sget("CHAT_DAILY_CAP") else "不设上限"
                    fee = f"（手续费 {sget('INHERIT_FEE_PERCENT')}%）" if sget("INHERIT_FEE_PERCENT") else "（免手续费）"
                    body = (f"<h1>💰 {sname}</h1><div class='sub'>当前生效规则（改设置自动更新）</div>{msg}"
                            "<div class='card'><table class='tbl'>"
                            f"<tr><th>获取</th><td>聊天：每满 {sget('CHAT_CHARS_PER')} 字符记 {sget('CHAT_REWARD')} 分，{cap}；"
                            f"签到：基础 {sget('SIGN_BASE_REWARD')} 分，连续满 7 天额外 +{sget('SIGN_STREAK_BONUS')} 分；抢积分红包"
                            + (f"；充值：{sget('BUY_MIN')}~{sget('BUY_MAX')}/次（管理员确认到账）" if sget("BUY_ENABLED") else "") + "</td></tr>"
                            "<tr><th>消耗</th><td>发积分红包；积分商城下单（"
                            + ("、".join(f"{x.get('name', '?')} {_mall_price(x)}分" for x in MALL_ITEMS) or "暂无商品")
                            + "）</td></tr>"
                            f"<tr><th>转赠</th><td>{'开启' if sget('INHERIT_ENABLED') else '关闭'}，把积分转给群内成员{fee}</td></tr>"
                            "<tr><th>等级</th><td>"
                            + " ≥ ".join(f"{x['name']} {x['value']}分" for x in POINT_LEVELS)
                            + "<br><span class='sub'>按「累计获得」计算：消费/兑换不掉级，只有真实产出（签到/游戏赢分/邀请/红包等）才涨</span></td></tr>"
                            "</table></div>")
                    # 阿福式聊天积分规则表：逐条「条件→积分」，命中即停；空表回退「每N字符」旧规则
                    def _m_desc(m):
                        m = (m or "").strip()
                        if not m: return "任意消息（兜底）"
                        if m.startswith("len>="): return f"消息 ≥ {m[5:]} 字"
                        return f"包含「{m}」"
                    rule_rows = ""
                    for i, r in enumerate(chat_rules):
                        on = bool(r.get("on"))
                        st = "<span style='color:#6fd08c'>启用</span>" if on else "<span style='color:#8a89a0'>停用</span>"
                        rule_rows += (f"<tr><td>{_m_desc(r.get('match'))}</td>"
                                      f"<td>{int(r.get('points', 0) or 0)}</td><td>{st}</td>"
                                      f"<td><a href='/rule_toggle/{i}'>{'停用' if on else '启用'}</a> · "
                                      f"<a href='/rule_del/{i}' style='color:#f09595'>删除</a></td></tr>")
                    if not rule_rows:
                        rule_rows = ("<tr><td colspan='4' style='text-align:center;color:#6a6982'>"
                                     "暂无自定义规则（聊天按「每N字符」旧规则计分）</td></tr>")
                    body += ("<div class='card' style='margin-top:18px'><h3>📋 聊天积分规则表（命中即停）</h3>"
                             "<div class='sub'>文字=消息包含即命中；<code>len>=5</code>=消息满5字；留空=任意消息兜底。"
                             "规则表有启用的规则时按表计分（都不命中不计分），旧的「每N字符」规则失效</div>"
                             "<table class='tbl'><tr><th>条件</th><th>积分</th><th>状态</th><th>操作</th></tr>"
                             + rule_rows + "</table>"
                             "<form method='post' action='/rule_add' style='display:flex;gap:10px;margin-top:12px'>"
                             "<input type='text' name='match' placeholder='文字或 len>=5（留空=任意消息）' style='flex:2'>"
                             "<input type='number' name='points' placeholder='积分' required style='flex:1'>"
                             "<button style='margin:0'>➕ 新增规则</button></form></div>")
                elif gkey == "points" and sub == "buypkg":
                    pkg_rows = ""
                    for i, p in enumerate(buy_packages):
                        on = bool(p.get("on"))
                        st = "<span style='color:#6fd08c'>启用</span>" if on else "<span style='color:#8a89a0'>停用</span>"
                        pkg_rows += (f"<tr><td>{html.escape(str(p.get('name', '?')))}</td>"
                                     f"<td>¥{p.get('cny', 0)}</td><td>{p.get('points', 0)}</td>"
                                     f"<td>{p.get('sort', 0)}</td><td>{st}</td>"
                                     f"<td><a href='/pkg_toggle/{i}'>{'停用' if on else '启用'}</a> · "
                                     f"<a href='/pkg_del/{i}' style='color:#f09595'>删除</a></td></tr>")
                    if not pkg_rows:
                        pkg_rows = "<tr><td colspan='6' style='text-align:center;color:#6a6982'>暂无套餐</td></tr>"
                    body = (f"<h1>{gicon} {sname}</h1><div class='sub'>玩家发「充值」看套餐列表，发「充值 套餐名」提交申请（管理员确认到账）。排序小的排前面</div>{msg}"
                            "<div class='card'><table class='tbl'><tr><th>名称</th><th>金额(CNY)</th><th>积分</th><th>排序</th><th>状态</th><th>操作</th></tr>"
                            + pkg_rows + "</table>"
                            "<form method='post' action='/pkg_add' style='display:flex;gap:10px;margin-top:12px'>"
                            "<input type='text' name='name' placeholder='套餐名称' required style='flex:2'>"
                            "<input type='number' name='cny' placeholder='金额 ¥' required min='0' style='flex:1'>"
                            "<input type='number' name='points' placeholder='积分' required min='1' style='flex:1'>"
                            "<input type='number' name='sort' value='0' placeholder='排序' style='flex:1'>"
                            "<button style='margin:0'>➕ 新增套餐</button></form></div>")
                elif gkey == "points" and sub == "redeem":
                    rd_rows = ""
                    for i, x in enumerate(redeem_goods):
                        on = bool(x.get("on", True))
                        st = "<span style='color:#6fd08c'>上架</span>" if on else "<span style='color:#8a89a0'>下架</span>"
                        left = int(x.get("left", 0) or 0)
                        tg = x.get("target_groups") or []
                        if not tg:
                            tg_txt = "<span style='color:#6fd08c'>全部授权群</span>"
                        else:
                            tg_txt = "<br>".join(f"<code>{c}</code> {html.escape(chat_name_cache.get(c, '') or str(c))}" for c in tg)
                        rd_rows += (f"<tr><td>{html.escape(str(x.get('name', '?')))}<div style='font-size:11px;color:#8a89a0;margin-top:2px'>作用群：{tg_txt}</div></td>"
                                    f"<td>{int(x.get('price', 0) or 0)}</td>"
                                    f"<td>{'不限' if left <= 0 else left}</td>"
                                    f"<td>{int(x.get('redeemed', 0) or 0)}</td><td>{st}</td>"
                                    f"<td><a href='/redeem_toggle/{i}'>{'下架' if on else '上架'}</a> · "
                                    f"<a href='/redeem_del/{i}' style='color:#f09595'>删除</a></td></tr>")
                    if not rd_rows:
                        rd_rows = ("<tr><td colspan='6' style='text-align:center;color:#6a6982'>"
                                   "暂无兑换商品，先新增商品</td></tr>")
                    ro_rows = ""
                    for o in reversed(redeem_orders[-50:]):
                        _oc = int(o.get("cid", 0) or 0)
                        _oc_txt = f"{html.escape(chat_name_cache.get(_oc) or str(_oc or '—'))}"
                        ro_rows += (f"<tr><td>{html.escape(str(o.get('no', '')))}</td>"
                                    f"<td>{html.escape(str(o.get('ts', '')))}</td>"
                                    f"<td>{_oc_txt}</td>"
                                    f"<td>{html.escape(str(o.get('uid', '')))}</td>"
                                    f"<td>{html.escape(str(o.get('item', '')))}</td>"
                                    f"<td>{int(o.get('price', 0) or 0)}</td></tr>")
                    if not ro_rows:
                        ro_rows = ("<tr><td colspan='6' style='text-align:center;color:#6a6982'>暂无兑换订单</td></tr>")
                    cmd_esc = html.escape(str(REDEEM_CMD))
                    # 作用群多选（空勾 = 全部授权群）
                    tg_checks = ""
                    for cid, cname in sorted(((c, chat_name_cache.get(c, str(c))) for c in AUTHORIZED_GROUPS), key=lambda kv: kv[1]):
                        tg_checks += (f"<label style='display:inline-flex;align-items:center;gap:4px;margin-right:12px;color:#cfcfe8'>"
                                      f"<input type='checkbox' name='cids' value='{cid}' checked> {html.escape(cname)} <code style='font-size:11px;color:#8a89a0'>{cid}</code></label>")
                    body = (f"<h1>{gicon} {sname}</h1><div class='sub'>群内发「{cmd_esc}」看商品列表，发「{cmd_esc} 编号」立即兑换；剩余 0=不限，限量商品兑完自动下架</div>{msg}"
                            "<div class='card'><h3>🛒 兑换商品</h3>"
                            "<table class='tbl'><tr><th>商品</th><th>所需积分</th><th>剩余</th><th>已兑换</th><th>状态</th><th>操作</th></tr>"
                            + rd_rows + "</table>"
                            "<form method='post' action='/redeem_add' style='margin-top:12px'>"
                            "<div style='display:flex;gap:10px'>"
                            "<input type='text' name='name' placeholder='商品名称' required style='flex:2'>"
                            "<input type='number' name='price' placeholder='所需积分' required min='1' style='flex:1'>"
                            "<input type='number' name='left' placeholder='剩余数量(0=不限)' min='0' style='flex:1'>"
                            "<input type='text' name='desc' placeholder='说明(可选)' style='flex:2'>"
                            "<button style='margin:0'>➕ 新增商品</button></div>"
                            "<div style='margin-top:8px;padding:8px;background:#1a1a2e;border-radius:6px'>"
                            "<div style='color:#8a89a0;font-size:12px;margin-bottom:6px'>📍 作用群（不勾 = 全部授权群；只勾部分 = 只在勾选群触发列表）</div>"
                            + tg_checks +
                            "</div></form></div>"
                            "<div class='card' style='margin-top:18px'><h3>🧾 最近兑换订单（防伪核对）</h3>"
                            "<table class='tbl'><tr><th>单号</th><th>时间</th><th>群</th><th>用户ID</th><th>商品</th><th>积分</th></tr>"
                            + ro_rows + "</table></div>"
                            "<div class='card' style='margin-top:18px'><form method='post' action='/save'>"
                            "<input type='hidden' name='group' value='points/redeem'>"
                            + _field_rows("points/redeem")
                            + "<div class='sub' style='margin-top:16px'>商品行占位符：<code>{goodsName}</code> <code>{pointNum}</code> <code>{leftNum}</code>；"
                              "成功通知占位符：<code>{name}</code> <code>{goodsName}</code> <code>{pointNum}</code> <code>{balance}</code>；"
                              "防伪单号由系统自动生成，只发用户私聊和管理员对账（群里不显示，防群友看到别人单号冒领），无需模板配置</div>" +
                            _savebar("保存兑换设置") + "</form></div>")
                elif gkey == "points" and sub == "guess":
                    gs_rows = ""
                    for gc, g in sorted(guesses.items()):
                        locked = bool(g.get("locked"))
                        st = "<span style='color:#e0b040'>已封盘</span>" if locked else "<span style='color:#6fd08c'>下注中</span>"
                        gs_rows += (f"<tr><td>{gc} {html.escape(chat_name_cache.get(gc) or str(gc))}</td>"
                                    f"<td>{html.escape(g['q'])}</td>"
                                    f"<td>🔵 {html.escape(g['a'])}｜{g['side_pots']['A']} 分</td>"
                                    f"<td>🔴 {html.escape(g['b'])}｜{g['side_pots']['B']} 分</td>"
                                    f"<td>{sum(v['A'] + v['B'] for v in g['bets'].values())}（{len(g['bets'])} 人）</td>"
                                    f"<td>{st}</td>"
                                    f"<td><form style='display:inline;margin:0' method='post' action='/guessops'>"
                                    f"<input type='hidden' name='op' value='settle'><input type='hidden' name='cid' value='{gc}'>"
                                    f"<button name='side' value='A' style='padding:2px 10px;cursor:pointer;background:#3b5a8a;color:#fff;border:none;border-radius:6px'>结算 A</button> "
                                    f"<button name='side' value='B' style='padding:2px 10px;cursor:pointer;background:#8a3b3b;color:#fff;border:none;border-radius:6px'>结算 B</button></form> "
                                    f"<form style='display:inline;margin:0' method='post' action='/guessops'>"
                                    f"<input type='hidden' name='op' value='cancel'><input type='hidden' name='cid' value='{gc}'>"
                                    f"<button style='padding:2px 10px;cursor:pointer'>撤销退款</button></form></td></tr>")
                    if not gs_rows:
                        gs_rows = ("<tr><td colspan='7' style='text-align:center;color:#6a6982'>"
                                   "暂无进行中的竞猜；用上方「新增竞猜」直接发起，或群里发「开竞猜 题目/选项A/选项B」</td></tr>")
                    body = (f"<h1>{gicon} {sname}</h1><div class='sub'>管理员群里发「开竞猜 题目/选项A/选项B [时长分钟]」开局，成员点按钮下注托管；"
                            f"到点自动封盘，「竞猜结算 A/B」开出答案后猜中方按注额比例瓜分全部奖池，「竞猜撤销」全额退款</div>{msg}"
                            + _flt_bar("/page/points/guess") +
                            "<div class='card'><h3>🎯 进行中的竞猜</h3>"
                            "<table class='tbl'><tr><th>群</th><th>题目</th><th>选项A</th><th>选项B</th><th>奖池</th><th>状态</th><th>操作</th></tr>"
                            + gs_rows + "</table>"
                            "<div class='sub' style='margin-top:8px'>网页结算/撤销立即生效并群内播报；下注积分已托管，撤销原路退回</div></div>"
                            "<div class='card' style='margin-top:18px'><h3>➕ 新增竞猜（网页直接发起，免群内敲命令）</h3>"
                            "<form method='post' action='/guess_create' style='display:flex;gap:10px;flex-wrap:wrap'>"
                            f"<select name='cid' required style='flex:1;min-width:160px'><option value=''>选择授权群</option>{_group_options()}</select>"
                            "<input type='text' name='q' placeholder='题目' required maxlength='50' style='flex:2;min-width:180px'>"
                            "<input type='text' name='a' placeholder='选项A' required maxlength='20' style='flex:1;min-width:100px'>"
                            "<input type='text' name='b' placeholder='选项B' required maxlength='20' style='flex:1;min-width:100px'>"
                            "<input type='number' name='duration' placeholder='时长(分钟,默认" + str(sget("GUESS_DURATION")) + ")' min='1' max='1440' style='flex:1;min-width:120px'>"
                            "<button style='margin:0'>🎯 发起竞猜</button></form></div>"
                            "<div class='card' style='margin-top:18px'><form method='post' action='/save'>"
                            "<input type='hidden' name='group' value='points/guess'>"
                            + _field_rows("points/guess")
                            + _savebar("保存竞猜设置") + "</form></div>")
                elif gkey == "points" and sub == "mallord":
                    _ord_src = [o for o in reversed(mall_orders[-200:]) if not sel_flt_cid or int(o.get("cid", 0) or 0) == sel_flt_cid]
                    ord_rows = "".join(
                        f"<tr><td>{html.escape(str(o.get('ts', '')))}</td><td>{o.get('cid')} {html.escape(chat_name_cache.get(int(o.get('cid', 0) or 0)) or str(o.get('cid', '')))}</td>"
                        f"<td>{o.get('uid')} {html.escape(user_names.get(o.get('uid'), ''))}</td>"
                        f"<td>{html.escape(str(o.get('item', '')))}</td><td>{o.get('price')}</td></tr>"
                        for o in _ord_src[:50])
                    if not ord_rows:
                        ord_rows = "<tr><td colspan='5' style='text-align:center;color:#6a6982'>还没有兑换订单</td></tr>"
                    body = (f"<h1>{gicon} {sname}</h1><div class='sub'>商城兑换订单（最近 50 条）</div>{msg}"
                            + _flt_bar("/page/points/mallord") +
                            "<div class='card'><table class='tbl'><tr><th>时间</th><th>群</th><th>用户</th><th>商品</th><th>价格</th></tr>"
                            + ord_rows + "</table></div>")
                elif gkey == "points" and sub == "buy":
                    pend_rows = "".join(
                        f"<tr><td><code>{oid}</code></td><td>{o.get('cid')} {html.escape(chat_name_cache.get(int(o.get('cid', 0) or 0)) or str(o.get('cid', '')))}</td>"
                        f"<td>{o.get('uid')} {html.escape(user_names.get(o.get('uid'), ''))}</td>"
                        f"<td>{o.get('amount')}</td><td>{html.escape(str(o.get('ts', '')))}</td></tr>"
                        for oid, o in buy_orders.items()
                        if not sel_flt_cid or int(o.get("cid", 0) or 0) == sel_flt_cid)
                    if not pend_rows:
                        pend_rows = ("<tr><td colspan='5' style='text-align:center;color:#6a6982'>"
                                     "没有待处理的购买申请（群里点按钮处理）</td></tr>")
                    body = (f"<h1>{gicon} {sname}</h1><div class='sub'>保存立即生效 · 套餐在「积分套餐管理」页配置</div>{msg}"
                            + _flt_bar("/page/points/buy") +
                            "<div class='card'><h3>🧾 待处理购买申请</h3>"
                            "<table class='tbl'><tr><th>单号</th><th>群</th><th>用户</th><th>数量</th><th>时间</th></tr>"
                            + pend_rows + "</table></div>"
                            "<div class='card' style='margin-top:18px'><form method='post' action='/save'>"
                            "<input type='hidden' name='group' value='points/buy'>"
                            + _field_rows("points/buy") + _savebar() + "</form></div>")
                else:
                    body = (f"<h1>{gicon} {sname}</h1><div class='sub'>保存立即生效，无需重启</div>{msg}"
                            "<div class='card'><form method='post' action='/save'>"
                            f"<input type='hidden' name='group' value='{gkey}/{sub}'>"
                            + _field_rows(f"{gkey}/{sub}") +
                            _savebar() + "</form></div>")
            else:
                # 无子页分组照旧；有子页分组落到第一个子页
                if gkey in SUBPAGES and SUBPAGES[gkey]:
                    first = SUBPAGES[gkey][0][0]
                    return _admin_page(gkey, sub=first, saved=saved, bad=bad)
                form_open = "<div class='card'>"
                if gkey == "tpls":
                    n_tpl = len(_cross_keys("tpls") or ())
                    form_open = ("<div class='card' style='border-color:#3a3b5a'>"
                                 "<div class='sub' style='margin:0 0 4px'>"
                                 f"全部 <b>{n_tpl}</b> 条话术集中在这里改，按所属模块分区；"
                                 "改完点底部保存，各页面同步生效（原页面里的同一项也已移除，不会两处打架）。"
                                 "点右侧「🔍 预览」看填充后的效果。</div></div>"
                                 "<div class='card' style='margin-top:18px'>")
                _modals = ""
                if gkey == "autodel":
                    # 照方丈「垃圾防护」结合自身排版：顶部防护一览（名称+状态+摘要+编辑），点编辑弹窗内仍是我们的表单
                    def _multi_names(key, val):
                        mp = dict(MULTI_OPTIONS.get(key, []))
                        return ("、".join(mp.get(v.strip(), v.strip()) for v in str(val or "").split(",") if v.strip())
                                or "未勾选任何规则（全部放行）")
                    _K_RECYCLE = {"panel_delete_seconds", "points_delete_seconds", "reply_delete_seconds",
                                  "settle_delete_seconds", "race_notice_delete_seconds"}
                    _K_ANTISPAM = {"antispam_enabled", "antispam_repeat_n", "antispam_window", "antispam_timer_n",
                                   "antispam_timer_tol", "antispam_mute_seconds", "antispam_mute_escalate",
                                   "antispam_notice_seconds"}
                    _K_TEXT = {"autodel_text_rules", "autodel_long_len", "autodel_text_seconds"}
                    _K_MEDIA = {"autodel_media_types", "autodel_media_seconds"}
                    _on_rec = any(globals().get(g) for g in ("PANEL_DELETE_SECONDS", "POINTS_DELETE_SECONDS",
                                                             "REPLY_DELETE_SECONDS", "SETTLE_DELETE_SECONDS",
                                                             "RACE_NOTICE_DELETE_SECONDS"))
                    _sum_rec = (" · ".join(t for t, g in (("面板", "PANEL_DELETE_SECONDS"), ("命令", "POINTS_DELETE_SECONDS"),
                                                           ("回复", "REPLY_DELETE_SECONDS"), ("结算", "SETTLE_DELETE_SECONDS"),
                                                           ("赛车提示", "RACE_NOTICE_DELETE_SECONDS")) if globals().get(g)
                                ) + " 后删除") if _on_rec else "全部为 0（不自动删除）"
                    _sum_anti = (f"复读 {sget('ANTISPAM_REPEAT_N')} 条/{sget('ANTISPAM_WINDOW')}s 内 · 定时器特征 {sget('ANTISPAM_TIMER_N')} 条"
                                 + (f" · 禁言 {sget('ANTISPAM_MUTE_SECONDS')}s" if sget("ANTISPAM_MUTE_SECONDS") else " · 只删不禁")) \
                        if sget("ANTISPAM_ENABLED") else "开关关闭"
                    _rows_g = (_guard_row("消息自动回收", _on_rec, _sum_rec, "md_recycle")
                               + _guard_row("刷屏识别", bool(sget("ANTISPAM_ENABLED")), _sum_anti, "md_antispam")
                               + _guard_row("文本类规则", bool(sget("AUTODEL_TEXT_RULES")), _multi_names("autodel_text_rules", sget("AUTODEL_TEXT_RULES"))
                                            + (f" · 阈值 {sget('AUTODEL_LONG_LEN')} 字" if "long" in str(sget("AUTODEL_TEXT_RULES")) else ""), "md_textrule")
                               + _guard_row("媒体与系统类规则", bool(sget("AUTODEL_MEDIA_TYPES")),
                                            _multi_names("autodel_media_types", sget("AUTODEL_MEDIA_TYPES")), "md_mediarule"))
                    form_open = ("<div class='card'><h3>🛡 防护类型</h3>"
                                 "<div class='sub'>点「✏️ 编辑」调整对应防护；弹窗内保存立即生效，只影响该防护的参数</div>"
                                 "<table class='tbl'><tr><th>防护项</th><th>状态 / 摘要</th><th style='width:90px'>操作</th></tr>"
                                 + _rows_g + "</table></div>")
                    _modals = (_guard_modal("md_recycle", "消息自动回收", "游戏卡片/下注面板、命令、查询回复、结算消息、赛车提示的自动删除（秒，0=不删）",
                                            "autodel", _K_RECYCLE)
                               + _guard_modal("md_antispam", "刷屏识别", "复读机与定时脚本特征识别（管理员豁免）",
                                              "autodel", _K_ANTISPAM)
                               + _guard_modal("md_textrule", "文本类规则", "勾选即删；未勾选的类型一律放行",
                                              "autodel", _K_TEXT)
                               + _guard_modal("md_mediarule", "媒体与系统类规则", "勾选即删；未勾选的类型一律放行",
                                              "autodel", _K_MEDIA))
                if gkey == "mod":
                    _SENS_KEYS = {"sensitive_enabled", "sensitive_words", "sensitive_action",
                                  "sensitive_mute_seconds", "link_whitelist_enabled", "link_whitelist"}
                    _sens_on = bool(sget("SENSITIVE_ENABLED") or sget("LINK_WHITELIST_ENABLED"))
                    _act_cn = ("删除", "删除+禁言", "删除+踢出")
                    _sens_sum = (f"敏感词 {len(sget('SENSITIVE_WORDS'))} 个 · 命中处理 {_act_cn[sget('SENSITIVE_ACTION')] if sget('SENSITIVE_ACTION') in (0, 1, 2) else sget('SENSITIVE_ACTION')}"
                                 + (f" · 白名单 {len(sget('LINK_WHITELIST'))} 个域名" if sget("LINK_WHITELIST_ENABLED") else " · 白名单关闭")
                                 ) if _sens_on else "开关关闭"
                    _sens_card = ("<div class='card' style='margin-top:18px'><h3>🛡 防护类型</h3>"
                                  "<table class='tbl'><tr><th>防护项</th><th>状态 / 摘要</th><th style='width:90px'>操作</th></tr>"
                                  + _guard_row("敏感词与域名白名单", _sens_on, _sens_sum, "md_sensitive")
                                  + "</table></div>")
                    _modals += _guard_modal("md_sensitive", "敏感词与域名白名单",
                                            "检测群里消息包含违禁词时按设置处理（明文子串或 /正则/）；域名白名单内的链接不按「链接消息」规则删",
                                            "mod", _SENS_KEYS)
                    _mod_on = [n for k, n in (("JOIN_VERIFY_ENABLED", "入群验证"), ("SENSITIVE_ENABLED", "敏感词"),
                                              ("LINK_WHITELIST_ENABLED", "域名白名单"),
                                              ("OBSERVE_CHECK_ENABLED", "观察期巡检"),
                                              ("LURKER_ENABLED", "潜水清理"), ("RAID_ENABLED", "防突袭"),
                                              ("JOIN_GATE_USERNAME", "门槛·用户名"),
                                              ("JOIN_GATE_PREMIUM", "门槛·Premium"),
                                              ("JOIN_GATE_BIO", "门槛·简介")) if globals().get(k)]
                    _mod_txt = ("、".join(_mod_on) + " 已开启") if _mod_on else \
                        "以下功能全部默认关闭，打开开关即生效；不想用了关掉开关即可，互不影响"
                    form_open = ("<div class='card' style='border-color:#3a3b5a'>"
                                 "<div class='sub' style='margin:0 0 4px'>🛡️ 群管中心："
                                 f"{html.escape(_mod_txt)}。</div>"
                                 "<div class='sub' style='margin:0'>相关页面："
                                 "<a class='q' href='/page/autodel'>🗑️ 自动删除</a>"
                                 "<a class='q' href='/page/members/join'>👥 入群与观察</a>"
                                 "<a class='q' href='/page/members/ops'>🔒 白名单</a>"
                                 "<a class='q' href='/page/admin/blacklist'>🚫 拉黑管理</a></div></div>"
                                 + _sens_card +
                                 "<div class='card' style='margin-top:18px'>")
                if gkey == "schedule":
                    def _sched_card(title, task, items, selected, subtitle, path):
                        """通用作用对象切换卡：items=(id, 显示名) 列表，selected=当前开启 id 集合。"""
                        if not items:
                            return ("<div class='card' style='margin-top:18px'><h3>" + title + "</h3>"
                                    "<div class='sub'>无可配置对象</div></div>")
                        rows = ""
                        for rid, name in items:
                            on = rid in selected
                            badge = "<span style='color:#6fd08c'>✅ 开</span>" if on else "<span style='color:#8a89a0'>⏸ 关</span>"
                            btn = "<a href='" + path + str(rid) + "/toggle' style='margin-left:8px'>" + ("关闭" if on else "开启") + "</a>"
                            rows += "<tr><td>" + badge + " " + html.escape(str(name)) + " <code style='font-size:11px;color:#8a89a0'>" + str(rid) + "</code>" + btn + "</td></tr>"
                        return ("<div class='card' style='margin-top:18px'><h3>" + title + "</h3>"
                                "<div class='sub'>" + subtitle + "（未勾选的不参与；都未勾=不执行该任务）</div>"
                                "<table class='tbl'>" + rows + "</table></div>")

                    # 4 个调度任务的作用对象
                    sched_cards = ""
                    grp_items = [(cid, chat_name_cache.get(cid, str(cid))) for cid in sorted(AUTHORIZED_GROUPS)]
                    uid_items = [(uid, user_names.get(uid, str(uid))) for uid in sorted({ADMIN_USER_ID, *BOT_ADMINS})]
                    if not daily_reset_groups: daily_reset_groups.update(AUTHORIZED_GROUPS)
                    if not leaderboard_groups: leaderboard_groups.update(AUTHORIZED_GROUPS)
                    if not backup_admins: backup_admins.add(ADMIN_USER_ID)
                    if not admin_report_admins: admin_report_admins.add(ADMIN_USER_ID)
                    sched_cards += _sched_card("🔄 每日重置 · 作用群", "dailyreset", grp_items, daily_reset_groups,
                                               f"每日 {DAILY_RESET_TIME} 清理这些群的排位赛当日分/聊天积分/赛车当日统计", "/sch_dailyreset_toggle/")
                    sched_cards += _sched_card("🏆 德州日榜推送 · 作用群", "leaderboard", grp_items, leaderboard_groups,
                                               f"每日 {LEADERBOARD_TIME} 向这些群推送德州当日排行榜", "/sch_leaderboard_toggle/")
                    sched_cards += _sched_card("💾 自动备份 · 接收私聊的管理员", "backup", uid_items, backup_admins,
                                               f"每 {BACKUP_INTERVAL_HOURS} 小时私聊发送 bot_data.json + bot_settings.json", "/sch_backup_admins_toggle/")
                    sched_cards += _sched_card("📊 经营日报 · 接收私聊的管理员", "report", uid_items, admin_report_admins,
                                               f"每日 {ADMIN_REPORT_TIME} 私聊发送昨日经营数据", "/sch_report_admins_toggle/")

                    # 定时任务状态总览：一眼看出哪些任务在跑（与下方开关实时联动）
                    def _badge(_on):
                        return ("<span style='color:#6fd08c;font-weight:700'>✅ 开启</span>" if _on
                                else "<span style='color:#f09595;font-weight:700'>⛔ 关闭</span>")
                    _rows = ""
                    for _name, _on in (("每日重置", DAILY_RESET_ENABLED), ("德州日榜推送", LEADERBOARD_ENABLED),
                                       ("赛车自动开赛", RACE_AUTO_ENABLED), ("自动备份", BACKUP_ENABLED),
                                       ("经营日报推送", ADMIN_REPORT_ENABLED), ("定时群公告", ANNOUNCE_ENABLED)):
                        _rows += ("<div style='display:flex;justify-content:space-between;padding:7px 2px;"
                                  "border-bottom:1px solid var(--border)'><span>" + _name + "</span>" + _badge(_on) + "</div>")
                    # 整点赛车每群推送明细：一眼看出哪个群没收到 + 网页直接开关每群
                    _race_rows = ""
                    for _cid in sorted(AUTHORIZED_GROUPS):
                        _on = bool(hourly_race_enabled.get(_cid, True))
                        _badge = "<span style='color:#6fd08c'>✅ 开</span>" if _on else "<span style='color:#8a89a0'>⏸ 关</span>"
                        _last = race_last_sent.get(_cid) or "（暂无）"
                        _tg = "<a href='/racegrp/" + str(_cid) + "/toggle' style='margin-left:8px'>" + ("关闭" if _on else "开启") + "</a>"
                        _race_rows += ("<tr><td>" + _badge + " <code>" + str(_cid) + "</code> " + html.escape(chat_name_cache.get(_cid) or str(_cid)) + _tg + "</td>"
                                       "<td>" + _last + "</td></tr>")
                    if not _race_rows:
                        _race_rows = "<tr><td colspan='2' style='text-align:center;color:#6a6982'>无授权群</td></tr>"
                    # 兑换商品作用群
                    _redeem_rows = ""
                    for _i, _x in enumerate(redeem_goods):
                        _tg = _x.get("target_groups") or []
                        if not _tg:
                            _tg_txt = "<span style='color:#6fd08c'>全部授权群</span>"
                        else:
                            _tg_txt = "<br>".join(f"<code>{c}</code> {html.escape(chat_name_cache.get(c) or str(c))}" for c in _tg)
                        _redeem_rows += (f"<tr><td>{html.escape(str(_x.get('name', '?')))}</td><td>{_tg_txt}</td></tr>")
                    if not _redeem_rows:
                        _redeem_rows = "<tr><td colspan='2' style='text-align:center;color:#6a6982'>暂无兑换商品</td></tr>"
                    form_open = ("<div class='card'><h3>📋 当前任务状态</h3>"
                                 "<div class='sub' style='margin-bottom:8px'>与下方开关实时联动；关闭后到点不再执行，"
                                 "重新开启从下一个周期生效（自动备份开关即时生效）</div>" + _rows + "</div>"
                                 "<div class='card' style='margin-top:18px'><h3>⏰ 整点赛车 · 每群推送明细</h3>"
                                 "<div class='sub'>每行一个授权群：状态（开关）/最近成功推送时间；下方红色统计是跳过原因计数（重启清零）</div>"
                                 "<table class='tbl'><tr><th>群（点右侧字开/关本群赛车）</th><th>最近成功推送</th></tr>" + _race_rows + "</table></div>"
                                 + sched_cards +
                                 "<div class='card' style='margin-top:18px'><h3>🎁 兑换商品 · 作用群</h3>"
                                 "<div class='sub'>作用群空=全授权群；不勾选部分=只在该群触发</div>"
                                 "<table class='tbl'><tr><th>商品</th><th>作用群</th></tr>" + _redeem_rows + "</table></div>"
                                 "<div class='card' style='margin-top:18px'>")
                if gkey != "autodel":
                    _field_keys = None
                    if gkey == "mod":   # 敏感词已移入防护弹窗，主表单剔除（含其分节标题）
                        _field_keys = ({f[0] for f in SETTINGS_FIELDS if f[6] == "mod"}
                                       - {"sensitive_enabled", "sensitive_words", "sensitive_action",
                                          "sensitive_mute_seconds", "link_whitelist_enabled", "link_whitelist",
                                          "sep_mod_word"})
                    # 主表单也声明 _fields：被剔除的键（如敏感词已移入弹窗）不进「补 0」名单，
                    # 否则用户只改个验证方式就把敏感词总开关静默清零（2026-09-09 报障真凶）
                    _form_fields = (f"<input type='hidden' name='_fields' value=\""
                                    f"{html.escape(','.join(sorted(_field_keys)), quote=True)}\">"
                                    if _field_keys is not None else "")
                    body = (f"<h1>{gicon} {gname}</h1><div class='sub'>保存立即生效，无需重启</div>{msg}"
                            + form_open +
                            "<form method='post' action='/save'>"
                            f"<input type='hidden' name='group' value='{gkey}'>"
                            + _form_fields
                            + _field_rows(gkey, keys=_field_keys) +
                            _savebar() + "</form>" + _modals + "</div>")
                else:
                    body = (f"<h1>{gicon} {gname}</h1>"
                            "<div class='sub'>点「✏️ 编辑」调整对应防护；弹窗内保存立即生效，只影响该项参数</div>"
                            f"{msg}" + form_open + _modals + "</div>")
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
                    "body{background:#121318;color:#e6e5f0;font-family:system-ui,sans-serif;margin:0;"
                    "display:flex;justify-content:center;padding-top:10vh}"
                    "pre{background:#1b1c22;border:1px solid #2a2b33;border-radius:14px;padding:24px;"
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
                    self._send(200, f"ok {BOT_VERSION} | data={_data_file_status()}".encode(),
                               [("Content-Type", "text/plain")]); return
                if path == "/magic":
                    """Telegram 一键登录：校验一次性 token → 直接建会话 → 302 进后台。"""
                    qs_m = parse_qs(urlparse(self.path).query)
                    tok = (qs_m.get("token", [""])[0] or "").strip()
                    with sess_lock:
                        rec = web_magic_tokens.pop(tok, None)  # pop 即一次性
                    if not rec or rec["exp"] < time.time():
                        self._send(200, _login_page(err=1)); return
                    session = secrets.token_urlsafe(32)
                    with sess_lock:
                        sessions[session] = time.time() + 7 * 86400
                    # 通知所有管理员：有人通过一键链接进入后台
                    try:
                        ip = _client_ip(self)
                        ua = (self.headers.get("User-Agent") or "")[:120]
                        if _bot_app and _bot_loop:
                            async def _notify():
                                ntxt = (f"✅ <b>后台登录成功（一键链接）</b>\n\n"
                                        f"来源 IP：<code>{ip}</code>\n"
                                        f"时间：{datetime.now(BEIJING_TZ).strftime('%Y-%m-%d %H:%M:%S')}\n"
                                        f"设备：<code>{html.escape(ua)}</code>")
                                for rid in _admin_receivers():
                                    try:
                                        await _bot_app.bot.send_message(chat_id=rid, text=ntxt, parse_mode="HTML")
                                    except Exception:
                                        pass
                            asyncio.run_coroutine_threadsafe(_notify(), _bot_loop).result(8)
                    except Exception:
                        pass
                    self._redirect("/", cookie=f"wb_session={session}; Path=/; HttpOnly; SameSite=Lax; Max-Age=604800")
                    return
                if not _check_session(self.headers.get("Cookie")):
                    self._send(200, _login_page()); return
                qs = parse_qs(urlparse(self.path).query)
                # 群级上下文：URL 带 ?cid=<群ID> 时，本请求渲染的取值/回显都按该群解析
                # （ThreadingHTTPServer 每请求一个线程，contextvar 天然按请求隔离，无需复位）
                try: _CUR_CID.set(int(qs.get("cid", ["0"])[0] or 0))
                except (TypeError, ValueError): _CUR_CID.set(0)
                saved, bad = "saved" in qs, "bad" in qs
                note = qs.get("note", [""])[0]
                err = qs.get("err", [""])[0]
                if path == "/":
                    self._send(200, _home_page()); return
                if path == "/lottery_cancel":
                    """网页取消抽奖：退参与费、标记取消、群里通知。"""
                    def _lc_back(note="", err=""):
                        q = ("?note=" + quote(note)) if note else ("?err=" + quote(err) if err else "")
                        self._redirect("/page/lottery" + q)
                    try: cid = int(qs.get("cid", ["0"])[0] or 0)
                    except ValueError: cid = 0
                    lo = _lottery_active(cid)
                    if not lo:
                        _lc_back(err="该群没有进行中的抽奖"); return
                    fee = int(lo.get("fee", 0))
                    if fee > 0:
                        for u, _ts, _n in lo["participants"]:
                            game_chips[cid][u] = game_chips[cid].get(u, 0) + fee
                    lo["status"] = "cancelled"
                    save_data()
                    if _bot_app and _bot_loop:
                        async def _notify():
                            tail = f"，已退还 {fee} 积分/人" if fee > 0 else ""
                            await safe_send(_bot_app.bot, cid,
                                f"🛑 抽奖活动「<b>{html.escape(lo['title'])}</b>」已被管理员取消{tail}",
                                parse_mode="HTML")
                        try: asyncio.run_coroutine_threadsafe(_notify(), _bot_loop).result(8)
                        except Exception: pass
                    _lc_back(note=f"✅ 已取消「{lo['title'][:20]}」" + (f"，退还 {fee} 分/人" if fee > 0 else ""))
                    return
                mm = re.fullmatch(r"/(rule|pkg|level|mall|redeem)_(del|toggle)/(\d+)", path)
                if mm:
                    kind, act, idx = mm.group(1), mm.group(2), int(mm.group(3))
                    lst = {"rule": chat_rules, "pkg": buy_packages,
                           "level": POINT_LEVELS, "mall": MALL_ITEMS, "redeem": redeem_goods}[kind]
                    back = {"rule": "/page/points/rule", "pkg": "/page/points/buypkg",
                            "level": "/page/points/level", "mall": "/page/points/mall",
                            "redeem": "/page/points/redeem"}[kind]
                    if 0 <= idx < len(lst):
                        if act == "del":
                            lst.pop(idx)
                        else:
                            # 2026-09-09：等级也有启停（用户截图「状态」列），不再一律当删除
                            lst[idx]["on"] = 0 if int(lst[idx].get("on", 1) or 0) else 1
                        save_settings({})
                    self._redirect(back); return
                mm = re.fullmatch(r"/gclear/(-?\d+)/([a-z0-9_]+)", path)
                if mm:  # 群页面点「⚑ 群专属 ↺」：清除该群对该项的覆盖，改回继承全局默认
                    _gc, _gk = int(mm.group(1)), mm.group(2)
                    group_set(_gc, _gk, None)
                    save_settings({})   # 立即落盘（含 group_settings）
                    _u = urlparse(self.headers.get("Referer") or "")
                    _back = (_u.path if _u.path.startswith("/") else "/page/dashboard")
                    if _u.query:
                        _back += "?" + _u.query
                    self._redirect(_back + ("&" if "?" in _back else "?") + "note="
                                   + quote("↺ 已恢复继承全局默认"))
                    return
                mm = re.fullmatch(r"/racegrp/(-?\d+)/toggle", path)
                if mm:  # 网页直接开/关某群整点自动赛车
                    rcid = int(mm.group(1))
                    if rcid in AUTHORIZED_GROUPS:
                        hourly_race_enabled[rcid] = not hourly_race_enabled.get(rcid, True)
                        save_data()
                    self._redirect("/page/schedule"); return
                # 4 个调度任务的作用对象切换：/sch_<task>_toggle/<id>（卡片链接带 /toggle 后缀，两者都收）
                mm = re.fullmatch(r"/sch_(dailyreset|leaderboard)_toggle/(-?\d+)(?:/toggle)?", path)
                if mm:
                    task, rid = mm.group(1), int(mm.group(2))
                    target = daily_reset_groups if task == "dailyreset" else leaderboard_groups
                    if rid in AUTHORIZED_GROUPS:
                        if rid in target: target.discard(rid)
                        else: target.add(rid)
                        save_settings({})
                    self._redirect("/page/schedule"); return
                mm = re.fullmatch(r"/sch_(backup|report)_admins_toggle/(-?\d+)(?:/toggle)?", path)
                if mm:
                    task, rid = mm.group(1), int(mm.group(2))
                    target = backup_admins if task == "backup" else admin_report_admins
                    if rid in target: target.discard(rid)
                    else: target.add(rid)
                    save_settings({})
                    self._redirect("/page/schedule"); return
                mm = re.fullmatch(r"/theme/([a-z]+)", path)
                if mm and mm.group(1) in _UI_THEMES:   # 顶栏主题色点：切换并持久化，回跳原页面
                    SETTINGS_SNAPSHOT["ui_theme"] = mm.group(1)
                    save_data()
                    self._redirect(qs.get("back", ["/"])[0] or "/"); return
                mm = re.fullmatch(r"/menu_move/([a-z0-9_]+)/(-?1)", path)
                if mm:
                    g, d = mm.group(1), int(mm.group(2))
                    keys_now = [gk for gk, _n, _i in SETTINGS_GROUPS if gk != "dashboard"]
                    order = [k for k in SIDEBAR_ORDER if k in keys_now] + [k for k in keys_now if k not in SIDEBAR_ORDER]
                    if g in order:
                        i = order.index(g)
                        j = max(0, min(len(order) - 1, i + d))
                        order[i], order[j] = order[j], order[i]
                        SIDEBAR_ORDER.clear(); SIDEBAR_ORDER.extend(order)
                        SETTINGS_SNAPSHOT["sidebar_order"] = list(SIDEBAR_ORDER)  # 供 _write_settings_file 带出
                        save_settings({})  # 走统一保存通道：套用+合并写盘+快照同步
                    self._redirect("/page/dashboard"); return
                mm = re.fullmatch(r"/tplprev/([a-z0-9_]+)", path)
                if mm:
                    self._send(200, _tpl_preview(mm.group(1))); return
                if path == "/points_template":
                    self._send(200, "用户ID,昵称,积分\n123456789,示例玩家,1000\n".encode("utf-8-sig"),
                               [("Content-Type", "text/csv; charset=utf-8"),
                                ("Content-Disposition", "attachment; filename=points_template.csv")]); return
                if path == "/points_export":
                    try: cid = int(qs.get("cid", ["0"])[0])
                    except ValueError: cid = 0
                    if not cid: self._send(400, b"bad cid", [("Content-Type", "text/plain")]); return
                    lines = ["用户ID,昵称,积分"]
                    for uid, value in sorted(game_chips.get(cid, {}).items()):
                        lines.append(f"{uid},{user_names.get(uid, '')},{value}")
                    self._send(200, "\n".join(lines).encode("utf-8-sig"),
                               [("Content-Type", "text/csv; charset=utf-8"),
                                ("Content-Disposition", f"attachment; filename=points_{cid}.csv")]); return
                mm = re.fullmatch(r"/invite_del/(-?\d+):(\d+)", path)
                if mm:
                    key = f"{mm.group(1)}:{mm.group(2)}"
                    invite_records.pop(key, None)
                    save_data()
                    self._redirect("/page/invite/records?note=" + quote("🗑 已删除记录 " + key)); return
                m = re.fullmatch(r"/page/([a-z]+)(?:/([a-z0-9_]+))?", path)
                if m and m.group(1) in {g for g, _n, _i in SETTINGS_GROUPS}:
                    if m.group(1) == "dashboard":   # 群体总览是定制页（统计卡+排序），无通用表单，别落空壳
                        self._send(200, _home_page()); return
                    try: sel_uid = int(qs.get("uid", ["0"])[0])
                    except ValueError: sel_uid = 0
                    def _qi(k, dflt):
                        try: return int(qs.get(k, [str(dflt)])[0] or dflt)
                        except ValueError: return dflt
                    flt = {"cid": _qi("cid", 0), "q": (qs.get("q", [""])[0] or "")[:50],
                           "edit": _qi("edit", -1),   # 等级页：点「编辑」带 ?edit=序号
                           "never": 1 if qs.get("never", [""])[0] else 0, "silent": _qi("silent", 0),
                           "join_from": (qs.get("join_from", [""])[0] or "")[:16],
                           "join_to": (qs.get("join_to", [""])[0] or "")[:16],
                           "page": max(1, _qi("page", 1)), "per": _qi("per", 20)}
                    try:
                        self._send(200, _admin_page(m.group(1), sub=m.group(2), saved=saved, bad=bad, note=note, err=err, uid=sel_uid, flt=flt)); return
                    except Exception as _pg_exc:
                        # 渲染出错返回可读错误页（带异常信息），绝不静默断连让用户看到"上游连接错误"
                        logger.exception("后台页面渲染失败：%s", path)
                        self._send(500, ("<h1>页面渲染出错</h1><p>" + html.escape(str(_pg_exc))
                                         + "</p><p>请截图本页反馈给开发者排查</p>").encode("utf-8"),
                                   [("Content-Type", "text/html; charset=utf-8")]); return
                self._send(404, b"not found", [("Content-Type", "text/plain")])

            def do_POST(self):
                try:
                    length = int(self.headers.get("Content-Length", 0))
                    raw = self.rfile.read(length) if length else b""
                except Exception:
                    raw = b""
                path = urlparse(self.path).path
                if path == "/points_import":
                    if not _check_session(self.headers.get("Cookie")):
                        self._redirect("/"); return
                    def _imp_back(note="", err=""):
                        q = ("?note=" + quote(note)) if note else ("?err=" + quote(err) if err else "")
                        self._redirect("/page/points/impexp" + q)
                    fields = _parse_multipart(raw, self.headers.get("Content-Type", ""))
                    try: cid = int(fields.get("cid", 0))
                    except (TypeError, ValueError): cid = 0
                    if not cid: _imp_back(err="群 ID 无效"); return
                    # ⑱ 二次确认：导入是覆盖式写入，未显式勾选确认一律拒绝（防选错群整群余额被覆盖）
                    if str(fields.get("confirm", "")).strip() not in ("1", "on", "true"):
                        _imp_back(err="未勾选「我确认覆盖所选群的全部积分」，导入已取消（不影响现有数据）"); return
                    file_field = fields.get("file")
                    if not isinstance(file_field, tuple) or not file_field[1]:
                        _imp_back(err="未收到文件"); return
                    fname, data = file_field
                    parsed, perr = _parse_points_rows(data, fname)
                    if perr: _imp_back(err=perr); return
                    rows, skipped = parsed
                    if not rows:
                        _imp_back(err="没有可导入的有效行（需 用户ID 和 积分 两列数字）"); return
                    for uid, pts, nick in rows:
                        game_chips[cid][uid] = pts          # 阿福语义：覆盖该群已有积分
                        if nick: user_names[uid] = nick
                    force_save_now()
                    _imp_back(note=f"✅ 导入完成：成功 {len(rows)} 条，跳过 {skipped} 条（群 {cid}，已覆盖式写入并落盘）")
                    return
                try:
                    form = parse_qs(raw.decode("utf-8"))
                except Exception:
                    form = {}
                # 群级上下文：表单带 cid（群页面保存时由页面自动注入的隐藏字段）→ 本请求按该群解析
                try: _CUR_CID.set(int((form.get("cid", [""])[0] or "0") or 0))
                except (TypeError, ValueError): _CUR_CID.set(0)
                if path == "/login":
                    ip = _client_ip(self)
                    with sess_lock:
                        _cnt, lock_until = login_fails.get(ip, [0, 0])
                    if time.time() < lock_until:
                        self._send(429, b"too many failed logins, try again in 10 minutes", [("Content-Type", "text/plain")]); return
                    pwd = (form.get("password", [""])[0] or "").strip()
                    # 重新发送验证码（OTP 页上的「重新发送」按钮）
                    resend_tok = form.get("resend", [""])[0]
                    if resend_tok:
                        with sess_lock:
                            old = web_pending_otp.pop(resend_tok, None)
                        if old and secrets.compare_digest(pwd, _web_password):
                            tok, _code, serr = _send_otp_code(ip)
                            if serr:
                                self._send(200, _otp_page(tok, err=serr + "（请检查是否已私聊过机器人 /start）"))
                            else:
                                self._send(200, _otp_page(tok, notice="✅ 新的验证码已发送"))
                        else:
                            self._send(200, _login_page(err=1))
                        return
                    if _pwd_ok(pwd):
                        # 二次验证：密码对了还不够，还要 Telegram 私聊验证码
                        if globals().get("WEB_OTP_ENABLED", True):
                            tok, _code, serr = _send_otp_code(ip)
                            self._send(200, _otp_page(tok,
                                err=(serr + "（请先在 Telegram 私聊机器人发 /start）") if serr else ""))
                            return
                        token = secrets.token_urlsafe(32)
                        with sess_lock:
                            sessions[token] = time.time() + 7 * 86400
                            login_fails.pop(ip, None)
                        self._redirect("/", cookie=f"wb_session={token}; Path=/; HttpOnly; SameSite=Lax; Max-Age=604800")
                    else:
                        with sess_lock:
                            new_cnt = _cnt + 1
                            login_fails[ip] = [new_cnt, time.time() + 600 if new_cnt >= 5 else 0]
                        self._send(200, _login_page(err=1))
                    return
                if path == "/login2":
                    """二次验证提交：校验 Telegram 验证码，通过才建会话。"""
                    ip = _client_ip(self)
                    with sess_lock:
                        _c2, lock2 = otp_fails.get(ip, [0, 0])
                    if time.time() < lock2:
                        self._send(429, b"too many failed otp attempts", [("Content-Type", "text/plain")]); return
                    tok = (form.get("otp_token", [""])[0] or "").strip()
                    code = (form.get("otp", [""])[0] or "").strip()
                    with sess_lock:
                        rec = web_pending_otp.get(tok)
                    if not rec or rec["exp"] < time.time() or rec["ip"] != ip:
                        web_pending_otp.pop(tok, None)
                        self._send(200, _login_page(err=1))  # 超时/失效 → 回密码页重来
                        return
                    if secrets.compare_digest(code, rec["code"]):
                        web_pending_otp.pop(tok, None)
                        token = secrets.token_urlsafe(32)
                        with sess_lock:
                            sessions[token] = time.time() + 7 * 86400
                            login_fails.pop(ip, None)
                            otp_fails.pop(ip, None)
                        # 登录成功通知：发给所有管理员，让全员知道有人进了后台
                        try:
                            ua = (self.headers.get("User-Agent") or "")[:120]
                            if _bot_app and _bot_loop:
                                async def _notify():
                                    ntxt = (f"✅ <b>后台登录成功</b>\n\n"
                                            f"来源 IP：<code>{ip}</code>\n"
                                            f"时间：{datetime.now(BEIJING_TZ).strftime('%Y-%m-%d %H:%M:%S')}\n"
                                            f"设备：<code>{html.escape(ua)}</code>")
                                    for rid in _admin_receivers():
                                        try:
                                            await _bot_app.bot.send_message(chat_id=rid, text=ntxt, parse_mode="HTML")
                                        except Exception:
                                            pass
                                asyncio.run_coroutine_threadsafe(_notify(), _bot_loop).result(8)
                        except Exception:
                            pass  # 通知失败不影响登录
                        self._redirect("/", cookie=f"wb_session={token}; Path=/; HttpOnly; SameSite=Lax; Max-Age=604800")
                    else:
                        with sess_lock:
                            new_cnt = _c2 + 1
                            otp_fails[ip] = [new_cnt, time.time() + 600 if new_cnt >= 5 else 0]
                        self._send(200, _otp_page(tok, err="验证码错误，请重试"))
                    return
                # 其余全部 POST 操作（管理员/加减分/排位分/保存…）必须已登录，防止未授权调用
                if not _check_session(self.headers.get("Cookie")):
                    self._redirect("/"); return
                if path == "/cmdaliases":
                    def _cb_back(note="", err=""):
                        q = ("?note=" + quote(note)) if note else ("?err=" + quote(err) if err else "")
                        self._redirect("/page/commands" + q)
                    new_over = {}
                    for key, vals in form.items():
                        if key in _HANDLERS_BY_NAME:  # 字段名=处理函数名（如 cmd_ph）
                            new_over[key] = vals[0].replace("，", ",").strip()
                    CMD_ALIAS_OVERRIDES.clear()
                    CMD_ALIAS_OVERRIDES.update(new_over)
                    apply_command_aliases()
                    menu_rows = []
                    for line in form.get("tg_menu", [""])[0].splitlines():
                        line = line.strip()
                        if not line: continue
                        parts_ = line.split(None, 1)
                        if len(parts_) != 2 or not re.fullmatch(r"[a-z0-9_]{1,32}", parts_[0]):
                            _cb_back(err=f"菜单行格式错误：「{line[:30]}」— 命令仅限英文小写/数字/下划线，后跟一个空格和描述"); return
                        menu_rows.append([parts_[0], parts_[1]])
                    if not menu_rows:
                        _cb_back(err="/ 菜单不能为空"); return
                    TG_MENU.clear(); TG_MENU.extend(menu_rows)
                    with _settings_lock:
                        try:
                            with open(SETTINGS_FILE, "r", encoding="utf-8") as f:
                                raw2 = json.load(f)
                        except Exception:
                            raw2 = {}
                        _write_settings_file(raw2.get("fields", {}), _web_password,
                                             dict(CMD_ALIAS_OVERRIDES), [list(t) for t in TG_MENU])
                    if _bot_app and _bot_loop:  # 热更新 Telegram 菜单
                        async def _set_menu():
                            await _bot_app.bot.set_my_commands([BotCommand(cc, dd) for cc, dd in TG_MENU])
                        try: asyncio.run_coroutine_threadsafe(_set_menu(), _bot_loop).result(10)
                        except Exception: pass
                    _cb_back(note=f"✅ 已保存并生效：{len(new_over)} 个命令触发词 + {len(TG_MENU)} 项 / 菜单")
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
                        AUTHORIZED_GROUPS.add(cid_); save_data()
                        try:   # 顺手拉群名进缓存，授权列表不再显示裸 ID
                            if _bot_app and _bot_loop:
                                _ch = asyncio.run_coroutine_threadsafe(
                                    _bot_app.bot.get_chat(cid_), _bot_loop).result(8)
                                if getattr(_ch, "title", None):
                                    chat_name_cache[cid_] = _ch.title
                        except Exception:
                            pass
                        _back(note=f"✅ 已授权群 {cid_}")
                    elif op == "authdel" and cid_:
                        # 移除群 = 取消授权 + 清掉该群所有残留数据（邀请记录/链接、各群开关、进出群缓存），
                        # 群解散后不再在下拉里留裸数字
                        AUTHORIZED_GROUPS.discard(cid_)
                        n_inv = sum(1 for k in list(invite_records) if k.startswith(f"{cid_}:"))
                        for k in [k for k in list(invite_records) if k.startswith(f"{cid_}:")]:
                            invite_records.pop(k, None)
                        invite_links.pop(cid_, None)
                        invite_pending.pop(f"{cid_}:", None)
                        for k in [k for k in list(invite_pending) if k.startswith(f"{cid_}:")]:
                            invite_pending.pop(k, None)
                        hourly_race_enabled.pop(cid_, None)
                        join_requests.pop(cid_, None); leave_records.pop(cid_, None)
                        member_joined_at.pop(cid_, None)
                        chat_name_cache.pop(cid_, None)
                        game_chips.pop(cid_, None)   # 群已解散积分数据无用；下拉(授权∪有积分群)不再出现裸数字
                        save_data()
                        _back(note=f"✅ 已移除群 {cid_}（含 {n_inv} 条邀请记录及全部群数据）")
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
                    elif op in ("join_approve", "join_decline") and cid_ and uid_:
                        if not (_bot_app and _bot_loop):
                            _back(err="bot 尚未启动完成，请稍后再试"); return
                        async def _jr():
                            if op == "join_approve":
                                await _bot_app.bot.approve_chat_join_request(cid_, uid_)
                            else:
                                await _bot_app.bot.decline_chat_join_request(cid_, uid_)
                        try:
                            asyncio.run_coroutine_threadsafe(_jr(), _bot_loop).result(15)
                            join_requests[cid_] = [r for r in join_requests.get(cid_, []) if r.get("uid") != uid_]
                            save_data()
                            self._redirect("/page/members?" + ("note=" if op == "join_approve" else "err=")
                                           + quote(("✅ 已批准入群 " if op == "join_approve" else "🚫 已拒绝入群 ") + str(uid_)))
                        except Exception as e:
                            self._redirect("/page/members?err=" + quote(f"操作失败：{e}（申请可能已被处理）"))
                    else:
                        _back(err="参数错误"); return
                    return
                if path == "/memops":
                    # 成员列表页操作：警告加减/清零、加白删白、封禁、踢出
                    op = form.get("op", [""])[0]
                    try:
                        cid_ = int(form.get("cid", ["0"])[0] or 0)
                        uid_ = int(form.get("uid", ["0"])[0] or 0)
                        amt = int(form.get("amount", ["1"])[0] or 1)
                    except ValueError:
                        self._redirect(f"/page/members/mlist?cid={cid_}&err=" + quote("参数必须是数字")); return
                    def _mb(note="", err=""):
                        q = ("note=" + quote(note)) if note else ("err=" + quote(err) if err else "")
                        self._redirect(f"/page/members/mlist?cid={cid_}&per=20" + ("&" + q if q else ""))
                    if op in ("warn_add", "warn_sub") and cid_ and uid_:
                        delta = amt if op == "warn_add" else -amt
                        cur = warn_counts[cid_][uid_]
                        warn_counts[cid_][uid_] = max(0, cur + delta)
                        if not warn_counts[cid_][uid_]: warn_counts[cid_].pop(uid_, None)
                        save_data()
                        _mb(note=f"✅ 用户 {uid_} 警告 {delta:+d}，当前 {warn_counts[cid_].get(uid_, 0)}")
                    elif op == "warn_clear_all" and cid_:
                        n = len(warn_counts.get(cid_, {}))
                        warn_counts.pop(cid_, None)
                        save_data()
                        _mb(note=f"🧹 已清除群 {cid_} 全部警告（{n} 人）")
                    elif op == "chips_clear_all" and cid_:
                        n = len(game_chips.get(cid_, {}))
                        game_chips.pop(cid_, None)
                        save_data()
                        _mb(note=f"🧹 已清空群 {cid_} 全部成员积分（{n} 人）")
                    elif op == "wl_add" and cid_ and uid_:
                        whitelist.setdefault(cid_, set()).add(uid_); save_data()
                        admin_logs.append({"ts": now_bj().strftime("%Y-%m-%d %H:%M"), "cid": cid_,
                                           "admin": "网页后台", "action": "加白", "target": str(uid_)})
                        _mb(note=f"✅ 已将 {uid_} 加入白名单")
                    elif op == "wl_del" and cid_ and uid_:
                        whitelist.get(cid_, set()).discard(uid_); save_data()
                        _mb(note=f"✅ 已将 {uid_} 移出白名单")
                    elif op in ("ban", "kick") and cid_ and uid_:
                        if not (_bot_app and _bot_loop):
                            _mb(err="bot 尚未启动完成，请稍后再试"); return
                        async def _bk():
                            await _bot_app.bot.ban_chat_member(cid_, uid_)
                            if op == "kick":  # 踢出=先封再解封，人已离群且可重新加入
                                await _bot_app.bot.unban_chat_member(cid_, uid_, only_if_banned=True)
                        try:
                            asyncio.run_coroutine_threadsafe(_bk(), _bot_loop).result(15)
                            admin_logs.append({"ts": now_bj().strftime("%Y-%m-%d %H:%M"), "cid": cid_,
                                               "admin": "网页后台", "action": "封禁" if op == "ban" else "踢出",
                                               "target": str(uid_)})
                            save_data()
                            _mb(note=("⛔ 已封禁 " if op == "ban" else "👋 已踢出 ") + str(uid_))
                        except Exception as e:
                            _mb(err=f"操作失败：{e}（bot 需为群管理员且有封禁权限）")
                    else:
                        _mb(err="参数错误")
                    return
                if path == "/guess_create":
                    # 竞猜网页直接发起：免群内敲命令
                    try: cid_ = int(form.get("cid", ["0"])[0] or 0)
                    except ValueError: cid_ = 0
                    q_ = form.get("q", [""])[0]; a_ = form.get("a", [""])[0]; b_ = form.get("b", [""])[0]
                    dur_ = form.get("duration", [""])[0] or sget("GUESS_DURATION")
                    if not cid_ or cid_ not in AUTHORIZED_GROUPS:
                        self._send(400, f"err=无效群ID（{cid_ or '未填'}）".encode("utf-8")); return
                    if not (_bot_app and _bot_loop):
                        self._send(400, "err=bot 尚未启动完成，请稍后再试".encode("utf-8")); return
                    async def _gmk():
                        return await _guess_do_create(_bot_app, cid_, q_, a_, b_, dur_)
                    try:
                        err = asyncio.run_coroutine_threadsafe(_gmk(), _bot_loop).result(20)
                    except Exception as e:
                        err = f"操作失败：{e}"
                    if err:
                        self._send(400, ("err=" + err).encode("utf-8")); return
                    self._redirect("/page/points/guess?note=" + quote("🎯 竞猜已发起并群内播报")); return
                if path == "/invite_clear":
                    invite_records.clear(); invite_links.clear()
                    save_data()
                    self._redirect("/page/invite/records?note=" + quote("🧹 已清空全部邀请数据")); return
                if path == "/invite_clear_group":
                    # 按群删除：只清选中群的邀请记录（不动其他群，不动链接）
                    try: cid_ = int(form.get("cid", ["0"])[0] or 0)
                    except ValueError: cid_ = 0
                    if cid_:
                        n = sum(1 for k in list(invite_records) if k.startswith(f"{cid_}:"))
                        for k in [k for k in list(invite_records) if k.startswith(f"{cid_}:")]:
                            invite_records.pop(k, None)
                        save_data()
                        self._redirect("/page/invite/records?cid=" + str(cid_) + "&note=" + quote(f"🗑 已删除该群 {n} 条邀请记录"))
                    else:
                        self._redirect("/page/invite/records?note=" + quote("请先选择要删除的群"))
                    return
                if path == "/guessops":
                    # 竞猜网页操作：结算 A/B 或撤销退款
                    op = form.get("op", [""])[0]
                    try: cid_ = int(form.get("cid", ["0"])[0] or 0)
                    except ValueError: cid_ = 0
                    def _gb(note="", err=""):
                        q = ("note=" + quote(note)) if note else ("err=" + quote(err) if err else "")
                        self._redirect("/page/points/guess" + ("?" + q if q else ""))
                    if op not in ("settle", "cancel") or not cid_:
                        _gb(err="参数错误"); return
                    if not (_bot_app and _bot_loop):
                        _gb(err="bot 尚未启动完成，请稍后再试"); return
                    async def _gop():
                        if op == "settle":
                            return await _guess_do_settle(_bot_app, cid_, form.get("side", [""])[0])
                        return await _guess_do_cancel(_bot_app, cid_)
                    try:
                        err = asyncio.run_coroutine_threadsafe(_gop(), _bot_loop).result(20)
                        _gb(err=err) if err else _gb(note="🎯 已结算并群内播报" if op == "settle" else "✅ 已撤销并全额退款")
                    except Exception as e:
                        _gb(err=f"操作失败：{e}")
                    return
                if path == "/rule_add":
                    try:
                        pts = int(form.get("points", ["0"])[0] or 0)
                    except ValueError:
                        pts = 0
                    match = (form.get("match", [""])[0] or "").strip()[:100]
                    chat_rules.append({"match": match, "points": pts, "on": True})
                    save_settings({})
                    self._redirect("/page/points/rule"); return
                if path == "/pkg_add":
                    def _ipkg(k, dflt):
                        try: return int(form.get(k, [str(dflt)])[0] or dflt)
                        except ValueError: return dflt
                    name = (form.get("name", [""])[0] or "").strip()[:30]
                    if name:
                        buy_packages.append({"name": name, "cny": max(0, _ipkg("cny", 0)),
                                             "points": max(1, _ipkg("points", 1)),
                                             "sort": _ipkg("sort", 0), "on": True})
                        save_settings({})
                    self._redirect("/page/points/buypkg"); return
                if path in ("/level_add", "/level_edit"):
                    def _ilv(k, dflt=0):
                        try: return int(form.get(k, [str(dflt)])[0] or dflt)
                        except ValueError: return dflt
                    def _lv_perms():
                        raw = form.getlist("perms") if hasattr(form, "getlist") else form.get("perms", [])
                        picked = {str(p).strip() for p in raw if str(p).strip()}
                        # 只留合法键，按定义顺序排列
                        return ",".join(k for k, _v in LEVEL_PERM_OPTIONS if k in picked)
                    def _lv_on():
                        v = form.get("on", [""])
                        return 1 if str(v[0] if v else "").strip() in ("1", "on", "true") else 0
                    name = (form.get("name", [""])[0] or "").strip()[:12]
                    val = max(0, _ilv("value"))
                    if path == "/level_edit":
                        try: idx = int(form.get("i", ["-1"])[0])
                        except ValueError: idx = -1
                        if 0 <= idx < len(POINT_LEVELS) and name and not any(ch in name for ch in "<>&"):
                            it = POINT_LEVELS[idx]
                            it["name"], it["value"] = name, val
                            it["perms"], it["on"] = _lv_perms(), _lv_on()
                            POINT_LEVELS.sort(key=lambda x: int(x.get("value", 0) or 0))
                            save_settings({})
                        self._redirect("/page/points/level?note=" + quote("✅ 等级已更新")); return
                    if name and not any(ch in name for ch in "<>&"):
                        POINT_LEVELS.append({"name": name, "value": val,
                                             "perms": _lv_perms(), "on": _lv_on()})
                        POINT_LEVELS.sort(key=lambda x: int(x.get("value", 0) or 0))
                        save_settings({})
                    self._redirect("/page/points/level"); return
                if path == "/mall_add":
                    def _iml(k, dflt=0):
                        try: return int(form.get(k, [str(dflt)])[0] or dflt)
                        except ValueError: return dflt
                    name = (form.get("name", [""])[0] or "").strip()[:30]
                    if name:
                        MALL_ITEMS.append({"name": name, "price": max(1, _iml("price", 1)),
                                           "desc": (form.get("desc", [""])[0] or "").strip()[:60], "on": True})
                        save_settings({})
                    self._redirect("/page/points/mall"); return
                if path == "/redeem_add":
                    def _ird(k, dflt=0):
                        try: return int(form.get(k, [str(dflt)])[0] or dflt)
                        except ValueError: return dflt
                    name = (form.get("name", [""])[0] or "").strip()[:30]
                    if name:
                        # 作用群：空列表 = 所有授权群（默认全群上架）；勾选则只发到这些群
                        cids_raw = form.getlist("cids") if hasattr(form, "getlist") else form.get("cids", [])
                        target_groups = []
                        for c in cids_raw:
                            try:
                                x = int(c)
                                if x in AUTHORIZED_GROUPS: target_groups.append(x)
                            except (ValueError, TypeError): pass
                        redeem_goods.append({"name": name, "price": max(1, _ird("price", 1)),
                                             "left": max(0, _ird("left", 0)),
                                             "redeemed": 0,
                                             "target_groups": target_groups,
                                             "desc": (form.get("desc", [""])[0] or "").strip()[:60], "on": True})
                        save_settings({})
                    self._redirect("/page/points/redeem"); return
                if path == "/lottery_create":
                    """网页创建抽奖（阿福格式）：解析 → 落库 + bot 发公告到群。"""
                    def _lc_back(note="", err=""):
                        q = ("?note=" + quote(note)) if note else ("?err=" + quote(err) if err else "")
                        self._redirect("/page/lottery" + q)
                    try: cid = int(form.get("cid", ["0"])[0] or 0)
                    except ValueError: cid = 0
                    if not cid or cid not in (set(AUTHORIZED_GROUPS) | set(game_chips.keys())):
                        _lc_back(err="请选择有效的群"); return
                    if _lottery_active(cid):
                        _lc_back(err="该群已有进行中的抽奖，请先取消或等开奖"); return
                    fields, ferr = _lottery_form_parse(form)
                    if ferr:
                        _lc_back(err=ferr); return
                    lotteries[cid] = {
                        "title": fields["title"], "desc": fields["desc"], "prizes": fields["prizes"],
                        "fee": int(sget("LOTTERY_FEE")), "keyword": fields["keyword"],
                        "min_bal": fields["min_bal"], "start_ts": time.time(),
                        "end_ts": fields["end_ts"], "msg_id": None,
                        "participants": [], "status": "open", "winners": [],
                        "creator": 0, "chat_id": cid,
                    }
                    save_data()
                    # 跨线程让 bot 把公告发到群（网页线程 → bot 主事件循环）
                    pub_err = ""
                    if _bot_app and _bot_loop:
                        async def _pub():
                            await _lottery_publish(_bot_app, cid, lotteries[cid])
                        try:
                            asyncio.run_coroutine_threadsafe(_pub(), _bot_loop).result(10)
                        except Exception as exc:
                            logger.exception("网页创建抽奖：公告发送失败")
                            pub_err = f"（公告发送失败：{type(exc).__name__}，活动已创建，可在群内发 /开奖 触发参与）"
                    _lc_back(note=f"✅ 抽奖「{fields['title'][:20]}」已创建并发到群 {cid}{pub_err}")
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
                    _before_bal = int(game_chips[cid][uid] or 0)
                    game_chips[cid][uid] += amount
                    if amount > 0:
                        _earn_add(cid, uid, amount)   # 网页加分同样计入累计获得
                    force_save_now()
                    if amount < 0 and _bot_app and _bot_loop:
                        # 开启「允许降级」时扣分可能掉级 → 发降级通知（开关内自判，零开销）
                        try:
                            asyncio.run_coroutine_threadsafe(
                                _check_level_drop_on_spend(_bot_app, cid, uid, _before_bal), _bot_loop).result(8)
                        except Exception:
                            logger.exception("网页扣分降级通知失败（已吞并）")
                    _back(note=f"✅ 已{'给' if amount > 0 else '扣除'} 用户 {uid} {abs(amount)} 积分，当前余额 {game_chips[cid][uid]}（群 {cid}）")
                    return
                if path == "/save":
                    if not _check_session(self.headers.get("Cookie")):
                        self._redirect("/"); return
                    group = form.get("group", [""])[0]
                    if group == "security":
                        _np = (form.get("new_password", [""])[0] or "").strip()
                        if len(_np) < 4:   # 此前不足 4 位被 save_settings 静默跳过，却仍提示"已保存"
                            self._redirect("/page/security?err=" + quote("密码至少 4 位，未做任何修改")); return
                        save_settings({}, _np)
                        # 改密后作废其他会话，只保留当前这个（旧会话继续可用等于白改）
                        try:
                            _mm = re.search(r"wb_session=([^;\s]+)", self.headers.get("Cookie") or "")
                            _cur = _mm.group(1) if _mm else ""
                            with sess_lock:
                                for _s in [s for s in list(sessions) if s != _cur]:
                                    sessions.pop(_s, None)
                        except Exception:
                            pass
                        self._redirect("/page/security?saved=1"); return
                    valid_keys = _cross_keys(group) or {k for k, _g, _l, _t, _lo, _hi, grp in SETTINGS_FIELDS if grp == group}
                    # _fields：弹窗表单声明本次只提交这些键 → bool 补 0 / multi 清空只作用于声明的键，
                    # 组内其他开关参数不受影响（不然保存一个弹窗会把没提交的开关全部关掉）
                    _only_raw = form.get("_fields", [""])[0]
                    only_set = ({s.strip() for s in _only_raw.split(",") if s.strip()} or None)
                    cfg = {}
                    for k, v in form.items():
                        if k not in valid_keys or (only_set and k not in only_set):
                            continue
                        ft = next((t for kk, _g, _l, t, _lo, _hi, _grp in SETTINGS_FIELDS if kk == k), "")
                        if ft == "sep":
                            continue          # 分组标题行不落盘
                        cfg[k] = ",".join(v) if ft == "multi" else v[0]
                    for k, _g, _l, ft, _lo, _hi, _grp in SETTINGS_FIELDS:  # checkbox 未勾选时表单不含该键 → 显式补 0（仅 bool）
                        if k in valid_keys and (only_set is None or k in only_set):
                            if ft == "bool":
                                cfg.setdefault(k, "0")
                            elif ft == "multi":
                                cfg.setdefault(k, "")   # 全不勾 = 关闭全部规则
                    try:
                        _gcid = int((form.get("cid", [""])[0] or "0") or 0)
                    except (TypeError, ValueError):
                        _gcid = 0
                    # 带 cid = 群级保存（只存与该群全局默认不同的项）；不带 = 原来的全局保存
                    applied = save_group_settings(_gcid, cfg) if _gcid else save_settings(cfg)
                    skipped = [k for k in cfg if k not in applied]
                    self._redirect(f"/page/{group}?saved=1" + (f"&cid={_gcid}" if _gcid else "")
                                   + ("&bad=1" if skipped else ""))
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
    """定时把数据文件发给配置的目标管理员私聊，当作云端持久化备份。

    无持久磁盘的平台容器重启会清空磁盘，有这份备份就能用 /restore 恢复，
    最坏只丢一个备份周期（30 分钟）的积分变动。
    """
    if not sget("BACKUP_ENABLED"):  # 后台「定时任务」开关：关了就不备份，保存即时生效
        return
    if not backup_admins: backup_admins.add(ADMIN_USER_ID)
    try:
        ok = await asyncio.to_thread(force_save_now)
        if not ok:
            logger.warning("自动备份：写盘失败，跳过本次")
            return
        if not os.path.exists(DATA_FILE):
            logger.warning("自动备份：数据文件不存在，跳过本次")
            return
        for _uid in list(backup_admins):
            try:
                with open(DATA_FILE, "rb") as f:
                    sent = await context.bot.send_document(
                        chat_id=_uid,
                        document=f,
                        filename=f"auto_backup_{datetime.now().strftime('%Y%m%d_%H%M')}.json",
                        caption="🤖 每日自动备份（需要恢复时：回复此文件发 /restore）",
                    )
                if sent and _uid == ADMIN_USER_ID:
                    backup_msg_ids.append(sent.message_id)
                    while len(backup_msg_ids) > 7:
                        old = backup_msg_ids.pop(0)
                        try: await context.bot.delete_message(chat_id=ADMIN_USER_ID, message_id=old)
                        except Exception: pass  # 消息可能已被手动删除，忽略
            except Exception as exc:
                logger.warning("自动备份推送 %s 失败: %s", _uid, exc)
        if os.path.exists(SETTINGS_FILE):
            for _uid in list(backup_admins):
                try:
                    with open(SETTINGS_FILE, "rb") as f:
                        sent_cfg = await context.bot.send_document(
                            chat_id=_uid,
                            document=f,
                            filename=f"bot_settings_{datetime.now().strftime('%Y%m%d_%H%M')}.json",
                            caption="⚙️ 网页设置备份（只需恢复设置：回复此文件发 /restore）",
                        )
                    if sent_cfg and _uid == ADMIN_USER_ID:
                        settings_backup_msg_ids.append(sent_cfg.message_id)
                        while len(settings_backup_msg_ids) > 7:
                            old = settings_backup_msg_ids.pop(0)
                            try: await context.bot.delete_message(chat_id=ADMIN_USER_ID, message_id=old)
                            except Exception: pass
                except Exception as exc:
                    logger.warning("设置备份推送 %s 失败: %s", _uid, exc)
        logger.info("自动备份完成")
    except Exception:
        logger.exception("自动备份失败")


_net_err_log = []   # 最近网络类异常的时间戳（5 分钟滑动窗口，用于告警降噪）

_NET_ERR_NAMES = ("NetworkError", "TimedOut", "ReadError", "ConnectError", "WriteError",
                  "ReadTimeout", "ConnectTimeout", "PoolTimeout", "RemoteProtocolError")

def _is_network_error(err):
    """判断是否为网络层异常（平台抖动/容器重启瞬断，PTB 会自动重连，属无害噪音）。"""
    if err is None:
        return False
    if type(err).__name__ in _NET_ERR_NAMES:
        return True
    s = f"{err!r}"
    return any(k in s for k in ("httpx", "ReadError", "ConnectError", "Connection aborted",
                                "Connection reset", "Server disconnected"))

def _net_error_tick(window=300, threshold=3):
    """记录一次网络异常，返回 True 表示达到告警门槛（窗口内第 threshold 次）。"""
    now = time.time()
    _net_err_log[:] = [t for t in _net_err_log if now - t < window]
    _net_err_log.append(now)
    return len(_net_err_log) >= threshold


async def on_app_error(update, context):
    """全局错误兜底：任何 handler 抛出的未捕获异常都会进入这里。

    记录完整堆栈日志，给当事人一条可感知的提示（不再静默失败），并推送管理员。
    网络类错误（httpx.ReadError / 平台抖动 / 容器重启瞬断）会自动重连，属无害噪音，
    默认只写日志，5 分钟窗口内累计 3 次以上才私聊管理员，避免刷屏。
    自身全程吞异常——错误处理器绝不能二次抛错。
    """
    err = context.error
    logger.exception("未处理异常", exc_info=err)
    net = _is_network_error(err)
    if net:
        hit = _net_error_tick()
        if not hit:
            logger.warning("网络类异常（自动重连，未打扰管理员）：%r（5分钟内第 %d 次）", err, len(_net_err_log))
            return
    try:
        chat = getattr(update, "effective_chat", None) if update is not None else None
        if chat is not None and not net:
            await context.bot.send_message(chat.id, "⚠️ 处理该操作时出错，请稍后重试；已通知管理员排查。")
    except Exception:
        pass
    try:
        if net:
            await context.bot.send_message(
                ADMIN_USER_ID,
                f"⚠️ 网络异常持续发生（5 分钟内第 {len(_net_err_log)} 次）：{err!r}\n"
                "多为平台网络抖动或容器重启，bot 一般会自动重连；若群内命令也无反应，请检查平台实例状态。")
        else:
            await context.bot.send_message(ADMIN_USER_ID, f"⚠️ bot 发生未处理异常：{err!r}")
    except Exception:
        pass


def main():
    global save_event
    load_settings()  # 先套用网页端保存的设置，再启动 bot
    token = os.environ.get("BOT_TOKEN")
    if not token: logger.error("未设置 BOT_TOKEN"); return
    
    # 在主循环启动前初始化 Event
    save_event = asyncio.Event()
    
    # 资金系统：关闭并发更新，串行处理所有 update handler，消除「检查余额→扣款」之间的竞态
    # （后台任务如赛车动画、定时调度仍为并发；仅 handler 之间不再交错，杜绝并发负分）。
    # 超时放大到 30s：默认 5s 在部分云平台（Railway 美西等）首次连 api.telegram.org 会
    # 直接 ReadTimeout 导致启动即崩；get_updates_read_timeout 必须 > getUpdates 的 timeout(10s)
    builder = (Application.builder().token(token)
               .concurrent_updates(False)
               .connect_timeout(30.0)
               .read_timeout(30.0)
               .write_timeout(30.0)
               .get_updates_read_timeout(42)
               .pool_timeout(10.0)
               .post_init(post_init)
               .post_shutdown(post_shutdown))
    app = builder.build()

    # 云平台保活：健康检查服务，供 UptimeRobot 定时 ping 防止休眠
    start_health_server()

    # 云端持久化：每 24 小时自动把数据备份发给管理员，容器重启可用 /restore 恢复
    if getattr(app, "job_queue", None) is not None:
        app.job_queue.run_repeating(auto_backup, interval=max(1, int(sget("BACKUP_INTERVAL_HOURS"))) * 3600, first=60)
        logger.info("自动备份任务已注册：每 %s 小时一次", sget("BACKUP_INTERVAL_HOURS"))
        # 群管中心：入群验证超时巡检（60s）+ 观察期到期巡检（10 分钟）
        app.job_queue.run_repeating(join_verify_sweep, interval=60, first=90)
        app.job_queue.run_repeating(observe_check_sweep, interval=600, first=180)
        app.job_queue.run_repeating(announce_sweep, interval=60, first=30)      # 定时群公告（每分钟对表，一天一次）
        app.job_queue.run_repeating(lurker_sweep, interval=6 * 3600, first=600)  # 潜水号清理（每 6 小时）
        logger.info("群管巡检任务已注册：入群验证超时(60s) / 观察期到期(10min) / 定时公告(60s) / 潜水清理(6h)")
    else:
        logger.warning("JobQueue 不可用，自动备份未启用（需安装 python-telegram-bot[job-queue]）")

    # 关键：handler 分组（PTB 语义「每个 group 内最多只有一个 handler 被调用，先匹配者 break，
    # 但不同 group 之间都会执行」）。此前全部注册在 group 0，而 on_media 的
    # ~TEXT & ~COMMAND 会先匹配「入群服务消息」并 break，导致注册在其后的 on_new_members_msg
    # 永远不触发 → 普通群入群验证/硬门槛/防突袭/观察期起点全部静默失效（无报错、无日志，
    # 用户只能看到「开关开了没用」）。
    # 现在：group 0=文本命令与按钮，group 1=媒体类自动删除，group 2=成员/入群事件。
    app.add_handler(MessageHandler(filters.TEXT & filters.Regex(r'^/'), route_command))
    app.add_handler(CallbackQueryHandler(on_button))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND & ~filters.Regex(r'^/'), on_text))
    app.add_handler(MessageHandler(~filters.TEXT & ~filters.COMMAND, on_media), group=1)  # 自动删除规则中心：媒体类
    # 关键：chat_member_types 必须显式传 ANY_CHAT_MEMBER（默认 -1=MY_CHAT_MEMBER 只听 bot 自身状态变化，
    # 普通新成员入群/退群触发的 chat_member 更新会被静默丢弃，调试里"最近事件"无埋点）
    app.add_handler(ChatMemberHandler(on_member_event, chat_member_types=ChatMemberHandler.ANY_CHAT_MEMBER), group=2)
    app.add_handler(MessageHandler(filters.StatusUpdate.NEW_CHAT_MEMBERS, on_new_members_msg), group=2)  # 普通群入群兜底
    app.add_handler(ChatJoinRequestHandler(on_join_request), group=2)  # 入群申请事件（群需开「申请加入」）
    app.add_error_handler(on_app_error)  # 全局错误兜底：handler 异常不再静默
    app.run_polling(allowed_updates=Update.ALL_TYPES, drop_pending_updates=True)

if __name__ == "__main__": main()
