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
# 4 游戏总开关/仅管理员开局（后台各游戏分组可调，保存立即生效）
TEXAS_ENABLED, TEXAS_ADMIN_ONLY = 1, 0
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
    ("race",      "赛车",       "🏎️"),
    ("rake",      "游戏抽水",   "💸"),
    ("points",    "积分系统",   "💰"),
    ("lottery",   "群组抽奖",   "🎉"),
    ("invite",    "邀请系统",   "🎟️"),
    ("season",    "排位赛",     "🏆"),
    ("members",   "群组管理",   "👥"),
    ("autodel",   "自动删除",   "🗑️"),
    ("schedule",  "定时任务",   "⏰"),
    ("commands",  "命令管理",   "⌨️"),
    ("general",   "通用与应急", "⚙️"),
    ("admin",     "管理员中心", "🛡️"),
    ("security",  "安全",       "🔒"),
]
# 子页面制：有子页的分组在侧边栏折叠展开（照阿福模板）。None=未开通占位页
SIDEBAR_ORDER = []   # 侧边栏自定义排序（组键列表，网页「群体总览」可 ▲▼ 调整，随设置持久化）
SIDEBAR_CHILDREN = {"texas": ["season"]}  # 把某些独立组折叠进父组显示（路由不变）：排位赛归入德州
# 侧边栏三大节（照阿福：节标题 + 节内菜单项）。不在任何节里的组保持原样渲染在最后。
SIDEBAR_SECTIONS = [
    ("🤖 机器人设置", ["dashboard", "schedule", "commands", "general", "admin", "security"]),
    ("👥 群组设置",   ["members", "autodel", "points", "lottery", "invite"]),
    ("🎲 娱乐功能",   ["texas", "blackjack", "jinhua", "race", "rake"]),
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
        ("pre",     "前置条件"),
        ("audit",   "审核"),
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
        ("orders",    "商城订单"),
        ("fundflow",  "资金流审查"),
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
    ("race_auto_start",         "RACE_AUTO_START",         "自动开赛时间(秒)",          "int",   10,  600,     "race"),
    ("race_animation_interval", "RACE_ANIMATION_INTERVAL", "动画帧间隔(秒)",            "float", 0.5, 30,      "race"),
    ("horse_count",             "HORSE_COUNT",             "赛马数量(匹)",              "int",   2,   8,       "race"),
    ("horse_names",             "HORSE_NAMES",             "赛马名称(逗号分隔)",        "names", 0,   0,       "race"),
    ("horse_emoji",             "HORSE_EMOJI",             "赛马表情(逗号分隔)",        "emoji", 0,   0,       "race"),
    ("race_track_length",       "RACE_TRACK_LENGTH",       "赛道长度(格)",              "int",   5,   50,      "race"),
    ("fixed_bet_amounts",       "FIXED_BET_AMOUNTS",       "下注按钮金额(逗号分隔)",    "bets",  0,   0,       "race"),
    ("race_odds_cap",           "RACE_ODDS_CAP",           "赔率上限(倍,0=无上限)",     "float", 0,   100,     "race"),
    ("race_enabled",            "RACE_ENABLED",            "赛车开关",                  "bool",  0,   1,       "race"),
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
    ("texas_admin_only",        "TEXAS_ADMIN_ONLY",        "德州仅管理员开局",          "bool",  0,   1,       "texas"),
    ("stale_text_command_seconds","STALE_TEXT_COMMAND_SECONDS","过期消息忽略(秒,防翻旧账命令)", "int", 5, 3600, "general"),
    # ---------- 定时任务（时间可自行设置） ----------
    ("daily_reset_time",        "DAILY_RESET_TIME",        "每日重置时间(时:分,排位分重置等)", "short", 0, 0, "schedule"),
    ("daily_reset_enabled",     "DAILY_RESET_ENABLED",     "每日重置开关",              "bool",  0,   1,       "schedule"),
    ("leaderboard_time",        "LEADERBOARD_TIME",        "德州日榜推送时间(时:分)",   "short", 0, 0,      "schedule"),
    ("leaderboard_enabled",     "LEADERBOARD_ENABLED",     "德州日榜推送开关",          "bool",  0,   1,       "schedule"),
    ("race_hourly_minute",      "RACE_HOURLY_MINUTE",      "赛车每小时自动开赛(第几分钟)", "int", 0, 59,    "schedule"),
    ("race_auto_enabled",       "RACE_AUTO_ENABLED",       "赛车自动开赛开关(仍受时段限制)", "bool", 0, 1,    "schedule"),
    ("race_hourly_start",       "RACE_HOURLY_START",       "自动开赛时段-从几点(含)",   "int",   0,   23,      "schedule"),
    ("race_hourly_end",         "RACE_HOURLY_END",         "自动开赛时段-到几点(含)",   "int",   0,   23,      "schedule"),
    ("backup_interval_hours",   "BACKUP_INTERVAL_HOURS",   "自动备份间隔(小时,改间隔重启后生效)", "int", 1, 168,   "schedule"),
    ("backup_enabled",          "BACKUP_ENABLED",          "自动备份开关(保存即时生效)", "bool",  0,   1,       "schedule"),
    ("admin_report_time",       "ADMIN_REPORT_TIME",       "经营日报推送时间(时:分,私聊管理员)", "short", 0, 0, "schedule"),
    ("admin_report_enabled",    "ADMIN_REPORT_ENABLED",    "经营日报推送开关",          "bool",  0,   1,       "schedule"),
    ("panel_delete_seconds",    "PANEL_DELETE_SECONDS",    "游戏卡片/下注面板删除(秒,0=不删)", "int", 0, 86400, "autodel"),
    ("web_base_url",            "WEB_BASE_URL",            "后台公网地址(/后台一键登录用)",          "text", 0,   0,    "general"),
    ("observe_enabled",         "OBSERVE_ENABLED",         "新成员观察期开关(入群未满时长禁言)", "bool", 0, 1, "members/join"),
    ("observe_seconds",         "OBSERVE_SECONDS",         "新成员观察期时长(秒,0=不限制)", "int", 0, 86400, "members/join"),
    ("antispam_enabled",        "ANTISPAM_ENABLED",        "定时刷屏识别开关(复读+定时器特征)", "bool", 0,   1,    "autodel"),
    ("antispam_repeat_n",       "ANTISPAM_REPEAT_N",       "复读命中条数(窗口内同内容)", "int",  2,   10,   "autodel"),
    ("antispam_window",         "ANTISPAM_WINDOW",         "复读检测窗口(秒)", "int",  10,  3600, "autodel"),
    ("antispam_timer_n",        "ANTISPAM_TIMER_N",        "定时器特征最少累计条数", "int",  3,   20,   "autodel"),
    ("antispam_timer_tol",      "ANTISPAM_TIMER_TOL",      "定时器间隔偏差容忍(%)", "int",  5,   90,   "autodel"),
    ("antispam_mute_seconds",   "ANTISPAM_MUTE_SECONDS",   "命中禁言基础时长(秒,0=只删不禁)", "int",  0,   86400,"autodel"),
    ("antispam_mute_escalate",  "ANTISPAM_MUTE_ESCALATE",  "累犯禁言翻倍", "bool", 0,   1,    "autodel"),
    # ===== 自动回收时长（全部集中在这个菜单，用户自己调数值） =====
    ("points_delete_seconds",  "POINTS_DELETE_SECONDS",  "你发的命令消息删除(秒,0=不删)", "int", 0, 86400, "autodel"),
    ("reply_delete_seconds",   "REPLY_DELETE_SECONDS",   "查询类回复删除(秒,0=不删)", "int", 0, 86400, "autodel"),
    ("settle_delete_seconds",  "SETTLE_DELETE_SECONDS",  "游戏结算消息删除(秒,0=不删)", "int", 0, 86400, "autodel"),
    ("race_notice_delete_seconds", "RACE_NOTICE_DELETE_SECONDS", "赛车倒计时提示删除(秒,0=不删)", "int", 0, 86400, "autodel"),
    ("antispam_notice_seconds", "ANTISPAM_NOTICE_SECONDS", "刷屏命中通告删除(秒,0=不删)", "int", 0, 86400, "autodel"),
    # ===== 自动删除规则中心（照阿福：按消息类型开关，命中即静默撤删，管理员豁免） =====
    ("autodel_links",         "AUTODEL_LINKS",         "链接消息(http/t.me/链接实体)", "bool", 0, 1, "autodel"),
    ("autodel_long_enabled",  "AUTODEL_LONG_ENABLED",  "超长消息", "bool", 0, 1, "autodel"),
    ("autodel_long_len",      "AUTODEL_LONG_LEN",      "超长消息长度阈值", "int", 50, 4096, "autodel"),
    ("autodel_photo",         "AUTODEL_PHOTO",         "图片消息", "bool", 0, 1, "autodel"),
    ("autodel_video",         "AUTODEL_VIDEO",         "视频消息", "bool", 0, 1, "autodel"),
    ("autodel_sticker",       "AUTODEL_STICKER",       "贴纸消息", "bool", 0, 1, "autodel"),
    ("autodel_gif",           "AUTODEL_GIF",           "动图消息", "bool", 0, 1, "autodel"),
    ("autodel_voice",         "AUTODEL_VOICE",         "语音/视频圆消息", "bool", 0, 1, "autodel"),
    ("autodel_document",      "AUTODEL_DOCUMENT",      "文档文件", "bool", 0, 1, "autodel"),
    ("autodel_archive",       "AUTODEL_ARCHIVE",       "压缩文件(zip/rar/7z等)", "bool", 0, 1, "autodel"),
    ("autodel_executable",    "AUTODEL_EXECUTABLE",    "可执行文件(exe/apk/bat等)", "bool", 0, 1, "autodel"),
    ("autodel_contact",       "AUTODEL_CONTACT",       "删除分享联系人", "bool", 0, 1, "autodel"),
    ("autodel_service",       "AUTODEL_SERVICE",       "删除系统消息(入退群/改群名等)", "bool", 0, 1, "autodel"),
    ("autodel_premium_emoji", "AUTODEL_PREMIUM_EMOJI", "删除会员表情(自定义表情)", "bool", 0, 1, "autodel"),
    ("welcome_enabled",         "WELCOME_ENABLED",         "入群欢迎开关",              "bool",  0,   1,       "members/join"),
    ("welcome_tpl",             "WELCOME_TPL",             "入群欢迎消息(支持 {name} {group} {id})", "text", 0, 0, "members/join"),
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
    ("chat_daily_cap",          "CHAT_DAILY_CAP",          "聊天积分每日上限(0=不限)",  "int",   0,   1000000, "points/cap"),
    ("sign_cmd",                "SIGN_CMD",                "签到指令(不带斜杠)",        "cmd",   0,   0,       "points/sign"),
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
    ("level_notify_enabled",    "LEVEL_NOTIFY_ENABLED",    "等级升降群内通知开关",      "bool",  0,   1,       "points/level"),
    ("level_cmd",               "LEVEL_CMD",               "查询等级指令(不带斜杠)",    "cmd",   0,   0,       "points/level"),
    ("level_up_msg_tpl",        "LEVEL_UP_MSG_TPL",        "用户升级通知",              "text",  0,   0,       "points/level"),
    ("level_down_msg_tpl",      "LEVEL_DOWN_MSG_TPL",      "用户降级通知",              "text",  0,   0,       "points/level"),
    ("point_levels",            "POINT_LEVELS",            "积分等级表",               "levels", 0, 0,      "points/level_hidden"),
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
    ("redeem_cmd",              "REDEEM_CMD",              "兑换触发词(不带斜杠)",      "cmd",   0,   0,       "points/redeem"),
    ("redeem_max_per_user",     "REDEEM_MAX_PER_USER",     "每人最大兑换数量(0=不限)",  "int",   0,   9999,    "points/redeem"),
    ("redeem_start",            "REDEEM_START",            "兑换开始时间(YYYY-MM-DD HH:MM,留空不限)", "short", 0, 0, "points/redeem"),
    ("redeem_end",              "REDEEM_END",              "兑换结束时间(同上,留空不限)", "short", 0,  0,       "points/redeem"),
    ("redeem_msg_list",         "REDEEM_MSG_LIST",         "兑换商品行模板",            "text",  0,   0,       "points/redeem"),
    ("redeem_msg_ok_group",     "REDEEM_MSG_OK_GROUP",     "兑换成功群通知",            "text",  0,   0,       "points/redeem"),
    ("redeem_msg_ok_dm",        "REDEEM_MSG_OK_DM",        "兑换成功私聊通知",          "text",  0,   0,       "points/redeem"),
    # ---------- 邀请系统（群组设置 → 邀请系统，子页面制照阿福模板） ----------
    ("invite_enabled",          "INVITE_ENABLED",          "邀请系统开关",              "bool",  0,   1,       "invite/config"),
    ("invite_notify",           "INVITE_NOTIFY",           "邀请人私聊通知开关",        "bool",  0,   1,       "invite/config"),
    ("invite_reward",           "INVITE_REWARD",           "邀请奖励(积分/人)",         "int",   0,   1000000, "invite/config"),
    ("invite_audit_enabled",    "INVITE_AUDIT_ENABLED",    "新邀请需人工审核开关",      "bool",  0,   1,       "invite/config"),
    ("invite_loose_match",      "INVITE_LOOSE_MATCH",      "宽松归因(申请没带链接时唯一链接兜底)", "bool", 0, 1, "invite/config"),
    ("invite_audit_award",      "INVITE_AUDIT_AWARD",      "审核通过后补发奖励开关",    "bool",  0,   1,       "invite/config"),
    ("invite_link_cmd",         "INVITE_LINK_CMD",         "邀请链接指令(不带斜杠)",    "cmd",   0,   0,       "invite/config"),
    ("invite_rank_admin_only",  "INVITE_RANK_ADMIN_ONLY",  "排行仅管理员可查开关",      "bool",  0,   1,       "invite/config"),
    ("invite_rank_today_cmd",   "INVITE_RANK_TODAY_CMD",   "今日邀请排行指令",          "cmd",   0,   0,       "invite/config"),
    ("invite_rank_month_cmd",   "INVITE_RANK_MONTH_CMD",   "本月邀请排行指令",          "cmd",   0,   0,       "invite/config"),
    ("invite_rank_all_cmd",     "INVITE_RANK_ALL_CMD",     "总邀请排行指令",            "cmd",   0,   0,       "invite/config"),
    ("invite_ok_group",         "INVITE_OK_GROUP",         "邀请成功群内通知模板",      "text",  0,   0,       "invite/config"),
    ("invite_link_msg",         "INVITE_LINK_MSG",         "邀请链接消息模板",          "text",  0,   0,       "invite/config"),
    ("invite_rank_today_msg",   "INVITE_RANK_TODAY_MSG",   "今日邀请排行标题模板",      "text",  0,   0,       "invite/config"),
    ("invite_rank_month_msg",   "INVITE_RANK_MONTH_MSG",   "本月邀请排行标题模板",      "text",  0,   0,       "invite/config"),
    ("invite_rank_all_msg",     "INVITE_RANK_ALL_MSG",     "总邀请排行标题模板",        "text",  0,   0,       "invite/config"),
    ("invite_rank_line_fmt",    "INVITE_RANK_LINE_FMT",    "排行行格式模板",            "text",  0,   0,       "invite/config"),
    ("invite_invalid_msg",      "INVITE_INVALID_MSG",      "无效邀请链接消息",          "text",  0,   0,       "invite/config"),
    ("invite_self_msg",         "INVITE_SELF_MSG",         "自己邀请自己消息",          "text",  0,   0,       "invite/config"),
    ("invite_pre_enabled",      "INVITE_PRE_ENABLED",      "进群前置条件开关",          "bool",  0,   1,       "invite/pre"),
    ("invite_pre_points",       "INVITE_PRE_POINTS",       "前置-被邀请人积分≥N(0=不限)", "int", 0,  1000000, "invite/pre"),
    ("invite_pre_msgs",         "INVITE_PRE_MSGS",         "前置-被邀请人发言≥N条(0=不限)", "int", 0, 100000,  "invite/pre"),
    ("invite_pre_avatar",       "INVITE_PRE_AVATAR",       "前置-被邀请人必须有头像",   "bool",  0,   1,       "invite/pre"),
    ("invite_pre_username",     "INVITE_PRE_USERNAME",     "前置-被邀请人必须有用户名", "bool",  0,   1,       "invite/pre"),
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
REPLY_DELETE_SECONDS = 30   # 查询类命令的 bot 回复自动删除（0=不删）
SETTLE_DELETE_SECONDS = 600 # 游戏结算消息自动删除（0=不删）
PANEL_DELETE_SECONDS = 300 # 游戏卡片/下注面板：本局结束后自动删除（0=不删）
RACE_NOTICE_DELETE_SECONDS = 60  # 赛车倒计时提示自动删除（0=不删）
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
# ---------- 邀请系统 ----------
INVITE_ENABLED = 1          # 邀请系统总开关
INVITE_NOTIFY = 1           # 邀请成功私聊通知邀请人开关
INVITE_REWARD = 50          # 每成功邀请 1 人奖励积分
INVITE_AUDIT_ENABLED = 0    # 新邀请需人工审核开关（审核页一键通过/拒绝）
INVITE_LOOSE_MATCH = 1      # 宽松归因：申请/事件都没带链接时，本群唯一专属链接直接兜底（Telegram 偶发漏字段）
INVITE_AUTO_APPROVE = True  # 入群申请自动批准：点专属链接→秒批→进群→归因→发奖全自动，不再要管理员手动批
INVITE_AUDIT_AWARD = 1      # 审核通过后补发奖励开关
INVITE_LINK_CMD = "link"    # 获取专属邀请链接指令
INVITE_RANK_ADMIN_ONLY = 0  # 邀请排行仅管理员可查开关
INVITE_RANK_TODAY_CMD = "今日邀请排行"
INVITE_RANK_MONTH_CMD = "本月邀请排行"
INVITE_RANK_ALL_CMD = "总邀请排行"
INVITE_PRE_ENABLED = 0      # 进群前置条件开关（被邀请人需满足才发奖，否则记 unmet）
INVITE_PRE_POINTS = 0       # 前置：被邀请人积分 ≥ N（0=不限）
INVITE_PRE_MSGS = 0         # 前置：被邀请人累计发言 ≥ N 条（0=不限）
INVITE_PRE_AVATAR = 0       # 前置：被邀请人必须有头像
INVITE_PRE_USERNAME = 0     # 前置：被邀请人必须有用户名
# ===== 定时刷屏识别（TG 定时消息发出后无标记，只能按行为特征抓：复读机 + 定时器节奏） =====
ANTISPAM_ENABLED = 1        # 1=开启
ANTISPAM_REPEAT_N = 3       # 复读命中：窗口内同内容第 N 条
ANTISPAM_WINDOW = 120       # 复读检测窗口（秒）
ANTISPAM_TIMER_N = 4        # 定时器特征：同内容累计至少 N 条才开始判定
ANTISPAM_TIMER_TOL = 30     # 定时器间隔偏差容忍（百分比，间隔需落在均值 ±30% 内）
ANTISPAM_MUTE_SECONDS = 3600  # 命中禁言基础时长（秒，0=只删不禁）
ANTISPAM_MUTE_ESCALATE = 1  # 累犯禁言翻倍（1h→2h→4h…）
ANTISPAM_NOTICE_SECONDS = 60  # 命中通告自动删除（秒，0=不删）
ANTISPAM_MIN_LEN = 5        # 参与统计的最短内容长度（防误伤"哈哈哈"类闲聊）
antispam_hist = {}          # (cid, uid, 内容归一化) -> [ts,...] 最多保留 12 条
antispam_offense = {}       # (cid, uid) -> [命中 ts,...] 用于累犯加重
# ===== 自动删除规则中心默认值（网页「自动删除」页可改，保存立即生效） =====
AUTODEL_LINKS = 1           # 链接消息
AUTODEL_LONG_ENABLED = 1    # 超长消息开关
AUTODEL_LONG_LEN = 200      # 超长阈值
AUTODEL_PHOTO = 0
AUTODEL_VIDEO = 0
AUTODEL_STICKER = 0
AUTODEL_GIF = 0
AUTODEL_VOICE = 0
AUTODEL_DOCUMENT = 0
AUTODEL_ARCHIVE = 0
AUTODEL_EXECUTABLE = 1
AUTODEL_CONTACT = 1
AUTODEL_SERVICE = 1
AUTODEL_PREMIUM_EMOJI = 0
WELCOME_ENABLED = 0         # 入群欢迎开关（1=开启）
WELCOME_TPL = "🎉 欢迎 {name} 加入本群！\n积分游戏请在群内发送 /start 查看玩法。"
REDPACKET_ENABLED = 1
POINT_LEVELS = [
    {"name": "练气期", "value": 0},
    {"name": "筑基期", "value": 2000},
    {"name": "金丹期", "value": 5000},
    {"name": "元婴期", "value": 12000},
    {"name": "化神期", "value": 30000},
    {"name": "炼虚期", "value": 80000},
    {"name": "合体期", "value": 200000},
    {"name": "大乘期", "value": 500000},
    {"name": "渡劫期", "value": 1200000},
    {"name": "真仙", "value": 3000000},
]
MALL_ITEMS = []  # [{"name": 商品名, "value": 价格}]
INHERIT_ENABLED = 1
INHERIT_FEE_PERCENT = 0
GUESS_ENABLED = 1           # 积分竞猜开关
GUESS_MIN_BET = 10          # 竞猜单注下限
GUESS_MAX_BET = 0           # 竞猜单注上限（0=不限）
GUESS_DURATION = 5          # 竞猜下注时长（分钟），到点封盘等管理员结算
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
    "mall_msg_buy": "🛍 购买成功：{item}（-{price} 积分）\n💰 余额 {balance}\n管理员会尽快处理发货。",
    "mall_msg_empty": "🛒 商城暂无商品，管理员可在后台上架。",
    "inherit_msg_ok": "✅ {name} → {target}：{amount} 积分{fee}\n💰 对方到账 {recv}｜你当前 {balance}",
    "redeem_msg_list": "🎁 {goodsName}｜{pointNum} 积分｜剩余 {leftNum}",
    "redeem_msg_ok_group": "🎉 {name} 兑换成功：{goodsName}（-{pointNum} 积分）\n💰 余额 {balance}",
    "redeem_msg_ok_dm": "🎉 你已成功兑换「{goodsName}」（{pointNum} 积分），请联系管理员发货。",
    "invite_ok_group": "🎉 {invitee} 通过 {inviter} 的邀请加入本群！\n💰 {inviter} 获得邀请奖励 {reward} 积分",
    "invite_link_msg": "🎟️ 你的专属邀请链接：\n{link}\n\n每成功邀请 1 位新朋友进群，奖励 {reward} 积分！",
    "invite_rank_today_msg": "📈 <b>今日邀请排行</b>",
    "invite_rank_month_msg": "📅 <b>本月邀请排行</b>",
    "invite_rank_all_msg": "🏆 <b>总邀请排行</b>",
    "invite_rank_line_fmt": "{i}. {name}｜邀请 {count} 人",
    "invite_invalid_msg": "⚠️ {name} 的邀请链接无效，请让邀请人重新生成",
    "invite_self_msg": "😅 不能邀请自己哦",
}
INVITE_OK_GROUP = MSG_TPL_DEFAULTS["invite_ok_group"]
INVITE_LINK_MSG = MSG_TPL_DEFAULTS["invite_link_msg"]
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
MALL_MSG_BUY = MSG_TPL_DEFAULTS["mall_msg_buy"]
MALL_MSG_EMPTY = MSG_TPL_DEFAULTS["mall_msg_empty"]
INHERIT_MSG_OK = MSG_TPL_DEFAULTS["inherit_msg_ok"]
REDEEM_MSG_LIST = MSG_TPL_DEFAULTS["redeem_msg_list"]
REDEEM_MSG_OK_GROUP = MSG_TPL_DEFAULTS["redeem_msg_ok_group"]
REDEEM_MSG_OK_DM = MSG_TPL_DEFAULTS["redeem_msg_ok_dm"]

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
chat_rules = []                                      # 阿福式聊天积分规则 [{"match","points","on"}] 命中即停；空=走每N字符旧规则
buy_packages = []                                    # 购买积分套餐 [{"name","cny","points","sort","on"}]
rp_packets = {}                                      # pid -> {"cid","from","left_amt","left_n","grabbed":{uid:amt},"ts","msg_id"}
guesses = {}                                         # cid -> 竞猜 {"q","a","b","end_ts","locked","bets":{uid:{"A","B"}},"side_pots":{"A","B"},"msg_id","task"}
invite_links = {}                                    # cid -> {uid: {"link","invite_id","ts"}} 每人专属邀请链接
invite_records = {}                                  # "cid:uid" -> {"cid","inviter","invitee","invitee_name","ts","audit","left","award","link"}
invite_pending = {}                                  # "cid:uid" -> 进群申请携带的邀请链接（人审批后 join 事件常不带链接，靠这个兜底归因；内存态）
invite_debug = defaultdict(list)                     # cid -> [最近10条邀请链路调试事件]（每环失败不再静默，/邀请调试 可查）


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
    if sidebar_order is None:
        sidebar_order = list(SETTINGS_SNAPSHOT.get("sidebar_order") or [])
    payload = {"fields": cfg, "web_password": password,
               "cmd_aliases": cmd_aliases or {}, "tg_menu": tg_menu or [],
               "sidebar_order": sidebar_order,
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

def _sync_dyn_aliases():
    """把网页自定义的指令名（查询积分/签到/积分排行）注册进命令分发表；旧名随之失效。"""
    aliases = globals().get("CMD_ALIASES")
    if aliases is None:
        return
    for gname, fn in (("QUERY_CMD", cmd_my_points), ("SIGN_CMD", cmd_sign), ("RANK_CMD", cmd_points_rank), ("LEVEL_CMD", cmd_my_level), ("REDEEM_CMD", cmd_points_redeem),
                      ("INVITE_LINK_CMD", cmd_invite_link), ("INVITE_RANK_TODAY_CMD", cmd_invite_rank_today),
                      ("INVITE_RANK_MONTH_CMD", cmd_invite_rank_month), ("INVITE_RANK_ALL_CMD", cmd_invite_rank_all)):
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
    global _web_password
    payload, origin = _load_settings_payload()
    if not payload:
        logger.info("无可用设置（%s 与数据快照均无），全部使用默认配置", SETTINGS_FILE)
        return
    try:
        if "fields" not in payload and "_settings" in payload:
            payload = payload["_settings"]  # 误指向 bot_data.json 时拆出内嵌设置，表格化数据(chat_rules等)才读得到
        apply_settings(payload.get("fields", {}))
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
                                  point_levels=list(POINT_LEVELS), mall_items=list(MALL_ITEMS),
                                  redeem_goods=list(redeem_goods)),
                # 群组抽奖：每群活动（含已结束的，方便历史展示）
                "_lotteries": {str(cid): {k: v for k, v in lo.items() if k != "msg_id"}
                               for cid, lo in lotteries.items()},
                # 进行中的红包（lock 不序列化）：不持久化的话重启后未领完的积分凭空消失
                "rp_packets": {pid: {k: v for k, v in p.items() if k != "lock"}
                               for pid, p in rp_packets.items()},
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
        invite_debug.clear()
        for cid, lst in data.get("invite_debug", {}).items():
            invite_debug[int(cid)] = list(lst)[-10:]
        invite_links.clear()
        for cid, users in data.get("invite_links", {}).items():
            for uid, v in users.items():
                try: invite_links[int(cid)][int(uid)] = dict(v)
                except (KeyError, ValueError, TypeError): continue
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
    if msg_id:
        try: await bot.delete_message(chat_id=cid, message_id=msg_id)
        except TelegramError: pass


def schedule_delete_ids(app, cid, ids, seconds):
    """延迟删除指定 message_id（用于只有 id、拿不到 Message 对象的场景，如原地编辑的下注面板）。"""
    if seconds <= 0 or not ids: return
    if isinstance(ids, int): ids = [ids]
    ids = [int(i) for i in ids if i]
    if not ids: return
    async def _del_later():
        await asyncio.sleep(seconds)
        for mid in ids: await safe_delete(app.bot, cid, mid)
    try: asyncio.create_task(_del_later())
    except RuntimeError: pass


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
    secs = int(SETTLE_DELETE_SECONDS if delete_after is None else delete_after)
    kwargs = {"parse_mode": parse_mode}
    if kb is not None:
        kwargs["reply_markup"] = kb
    msgs = await safe_send_long(app.bot, cid, text, **kwargs)
    if msgs and secs > 0:
        schedule_delete(app, cid, msgs, secs)
    return msgs


async def send_reply(update, context, text, kb=None, parse_mode=None, delete_after=None):
    """【查询类命令必用】查询回复统一出口：发送 + 自动按 REPLY_DELETE_SECONDS 回收。

    以后写任何查询类命令（积分/战绩/排行/商城等），回复一律走这里——
    回复自动删除是默认行为，不用（也不会忘）另写 schedule_delete。
    时长由网页「积分系统 → 积分设置 → 查询回复自动删除(秒)」控制，0 = 永久保留。
    注意：用户发的命令本身按 POINTS_DELETE_SECONDS 在 _dispatch_alias 全局统一删，无需关心。
    """
    secs = int(REPLY_DELETE_SECONDS if delete_after is None else delete_after)
    kwargs = {}
    if parse_mode is None:
        parse_mode = "HTML"   # 默认 HTML：<b>/<code> 生效；解析失败自动回退纯文本
    if parse_mode:
        kwargs["parse_mode"] = parse_mode
    if kb is not None:
        kwargs["reply_markup"] = kb
    try:
        reply = await update.message.reply_text(text, **kwargs)
    except BadRequest as exc:
        if "parse entities" in str(exc).lower() and kwargs.get("parse_mode"):
            kwargs.pop("parse_mode")  # 昵称含 < 等导致解析炸 → 纯文本重发
            reply = await update.message.reply_text(text, **kwargs)
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
    message = await safe_send(app.bot, cid, f"🎲 {await get_name(app, uid)} {desc}")
    if message:
        async def delete_later():
            await asyncio.sleep(10); await safe_delete(app.bot, cid, message.message_id)
        asyncio.create_task(delete_later())


def ledger_add(cid, frm, to, amt, typ):
    """资金流台账：红包领取/转赠等人对人转移逐笔记账（防小号审查用，留 5000 条）。"""
    ledger.append({"ts": now_bj().strftime("%Y-%m-%d %H:%M"), "cid": cid, "frm": frm, "to": to, "amt": amt, "typ": typ})
    if len(ledger) > 5000: del ledger[:len(ledger) - 5000]


def calc_rake(nets):
    """计算抽水（纯计算不扣款）：对赢家净赢按 RAKE_PERCENT% 抽成。返回 (总抽水, {uid: 金额})。"""
    if not RAKE_ENABLED or RAKE_PERCENT <= 0:
        return 0, {}
    rake_total, rake_per = 0, {}
    for uid, net in (nets or {}).items():
        if not isinstance(uid, int) or uid <= 0 or net <= 0:
            continue
        if net < RAKE_MIN_NET:
            continue
        amt = int(net * RAKE_PERCENT / 100)
        if amt <= 0:
            continue
        rake_per[uid] = amt
        rake_total += amt
    return rake_total, rake_per


async def commit_rake(app, cid, rake_per, label):
    """抽水落账：从钱包扣除 + 写台账。不再单独发群消息——抽水在结算面板里直接体现为「实收」。"""
    if not rake_per:
        return 0
    total = 0
    for uid, amt in rake_per.items():
        async with wallet_locks[uid]:
            game_chips[cid][uid] = max(0, game_chips[cid].get(uid, 0) - amt)
        ledger_add(cid, uid, 0, amt, f"抽水-{label}")
        total += amt
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
        if not BROADCAST_ENABLED or net < max(1, BROADCAST_MIN_AMOUNT): return
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
        f"🃏 公牌：{'  '.join(card_str(card) for card in game.board) or '未发牌'}",
        f"💰 奖池 {game.pot}｜下注 {game.current_bet}",
    ]
    current = game.current()
    if current:
        lines.append(f"⏳ 当前行动：{await get_name(app, current)}｜需跟：{max(0, game.current_bet - game.round_bets[current])}")
    lines.append("━━━━━━━━━━━━━━━━━")
    for index, uid in enumerate(game.players, 1):
        status = "❌ 弃牌" if uid in game.folded else "🔥 全下" if uid in game.all_in else "🟢 在局"
        mark = "👉" if uid == current else ""
        lines.append(f"{mark}{index}. {await get_name(app, uid)} {status} 投{game.total_bet[uid]} 余{game.chips[uid]}")
    return "\n".join(lines)


def poker_buttons(game, uid):
    acting = (uid == game.current() and uid not in game.folded and uid not in game.all_in)
    if not acting:
        return InlineKeyboardMarkup([[InlineKeyboardButton("🃏 查看手牌", callback_data="texas_hand")]])
    to_call = max(0, game.current_bet - game.round_bets[uid])
    # 面板宽度=最宽行：每行最多2个按钮压宽度；跟注+加注同行、半池+全池同行、全下独占
    rows = [[InlineKeyboardButton("🃏 手牌", callback_data="texas_hand"),
             InlineKeyboardButton("❌ 弃牌", callback_data="texas_fold")]]
    act_btn = InlineKeyboardButton("✅ 过牌" if not to_call else f"✅ 跟注 {to_call}",
                                   callback_data="texas_check" if not to_call else "texas_call")
    if uid not in game.raise_locked:
        # 半池/全池快捷加注：加注金额=底池的 1/2 或 1 倍；不足最小加注时按最小加注兜底
        half_amt = max(FIXED_MIN_RAISE, game.pot // 2)
        pot_amt = max(FIXED_MIN_RAISE, game.pot)
        row_act = [act_btn]
        if game.chips[uid] >= to_call + FIXED_MIN_RAISE and half_amt > FIXED_MIN_RAISE:
            row_act.append(InlineKeyboardButton(f"🔼 加注 {FIXED_MIN_RAISE}", callback_data=f"texas_raise_{FIXED_MIN_RAISE}"))
        rows.append(row_act)
        row_p = []
        if half_amt < pot_amt and game.chips[uid] >= to_call + half_amt:
            row_p.append(InlineKeyboardButton(f"💰 半池+{half_amt}", callback_data="texas_raise_half"))
        if game.chips[uid] >= to_call + pot_amt:
            row_p.append(InlineKeyboardButton(f"💰 全池+{pot_amt}", callback_data="texas_raise_pot"))
        if row_p: rows.append(row_p)
    else:
        rows.append([act_btn])
    if game.chips[uid] > 0:
        rows.append([InlineKeyboardButton(f"🔥 全下 {game.chips[uid]}", callback_data="texas_allin")])
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
            lines.extend([f"{names[uid]}：投入 {game.total_bet[uid]}｜盈亏 {net:+d}{r_txt}", ""])

        # 资金流审查：官方模式把本局人对人净转移记账（防"故意输牌送分"）；排位分不记
        if game.mode == "official" and not game.season:
            record_game_flows(game.chat_id, _nets, "德州")
            await commit_rake(app, game.chat_id, rake_per, "德州")

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
        if SETTLE_DELETE_SECONDS > 0:
            schedule_delete(app, game.chat_id, delivered, SETTLE_DELETE_SECONDS)
        # 牌桌卡片此前结算后一直留在群里，结束后延迟清理
        schedule_delete_ids(app, game.chat_id, game.game_msg_id, PANEL_DELETE_SECONDS)
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
        # 赔率上限（经济保护）：默认 10 倍，0=无上限（旧行为）。封顶在单调约束前统一应用
        if RACE_ODDS_CAP > 0:
            raw = [min(value, RACE_ODDS_CAP) for value in raw]
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
                        notice = await safe_send(app.bot, self.chat_id, f"⏰ 赛车还剩 {threshold // 60} 分钟 {threshold % 60} 秒！")
                        # 之前这条提示发出后就一直留在群里，需要自动删除
                        schedule_delete(app, self.chat_id, notice, RACE_NOTICE_DELETE_SECONDS)
                
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
                # 抽水先算（官方模式），结算行直接带「实收」
                rake_per = calc_rake({s[0]: s[5] for s in settlements})[1] if self.mode == "official" else {}
                # 阶段二：统一改写钱包（此处仅 dict 操作，不会抛异常，payouts_applied 必定置位）
                for uid, _, _, _, payout, _, _ in settlements:
                    wallet[self.chat_id][uid] += payout; total_payout += payout
                payouts_applied = True

                # 大奖战报：押中独赢且净赢超阈值 → 广播其他授权群
                best = max(settlements, key=lambda s: s[5]) if settlements else None
                if best and best[5] > 0:
                    detail = f"🐴 押中 {HORSE_EMOJI[winner]}{HORSE_NAMES[winner]}（赔率 {best[6]:.1f}）"
                    await broadcast_big_win(app, self.chat_id, best[0], "🏎️ 赛车大赛", best[5], detail)
                if self.mode == "official":
                    await commit_rake(app, self.chat_id, rake_per, "赛车")

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
                    r_amt = rake_per.get(_, 0)
                    r_txt = f"（实收 {net - r_amt}，含抽水{r_amt}）" if r_amt else ""
                    if bet_on_winner > 0:
                        lines.append(f"{name}：总投注 {stake}｜命中 {bet_on_winner}（{bo:.2f}x）｜派彩 {payout}｜净 {net:+d}{r_txt}")
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
                if SETTLE_DELETE_SECONDS > 0:
                    schedule_delete(app, self.chat_id, delivered, SETTLE_DELETE_SECONDS)

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
                # 下注面板此前全程只做原地编辑、从不删除，会一直堆在群里；结算后延迟清理
                schedule_delete_ids(app, self.chat_id, self.game_msg_id, PANEL_DELETE_SECONDS)
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
            # 取消/退款后的面板同样只留一小会儿，避免残留占位
            schedule_delete_ids(app, self.chat_id, self.game_msg_id, PANEL_DELETE_SECONDS)


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
            if update.effective_message:
                if context is not None and update.message: await send_reply(update, context, "❌ 此群组未授权，请联系管理员。")
                else: await update.effective_message.reply_text("❌ 此群组未授权，请联系管理员。")
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
    if not await need_auth(update, context): return
    text = "🎮 欢迎使用娱乐机器人！\n\n🎲 发起游戏：\n/开始 或 /菜单 - 查看本帮助\n/德州 - 发起德州扑克（统一积分）\n/赛车 - 发起赛车\n/21点 - 发起21点\n/炸金花 - 发起炸金花（闷牌偷鸡）\n\n💰 积分系统：\n/签到 - 每日签到领积分\n/我的积分 - 积分/等级/签到状态\n/积分排行 - 积分排行榜\n/积分商城 - 用积分换好物\n红包 总数 份数 - 发积分红包（如：红包 1000 5）\n转赠 数量 - 把积分转给群里成员（回复消息用）\n充值 数量 - 申请购买积分（管理员确认到账）\n\n🎟️ 邀请有礼：\n/link - 领取本群专属邀请链接\n今日邀请排行 / 本月邀请排行 / 总邀请排行 - 查看邀请榜\n\n📊 数据查询：\n/盈亏 - 当日盈亏榜\n/排行 - 总积分榜\n流水 - 查自己的积分来源明细（红包/抽水/邀请奖励等；回复他人消息查对方仅限管理员）\n/结束 - 终止当前游戏\n\n🏪 称号商店：\n/商店 - 查看可兑换称号\n/兑换 称号名 - 用积分换称号"
    if is_bot_admin(update.effective_user.id):
        text += "\n\n🔧 管理命令（仅管理员）：\n/授权 - 授权当前群使用\n取消授权 - 取消群授权\n/授权列表 - 查看已授权群\n/加管理员 /减管理员 /管理员列表\n/加积分(负数即减) /赛季分\n/拉黑 /解黑 /黑名单 - 封禁违规玩家\n/列表 - 管理总览(管理员/授权群/黑名单三合一)\n/备份 /恢复\n💡 快捷加减分：在群里回复某玩家的消息，然后发「/add 数量」即可给他加/减分（负数即减），不用输ID"
    await send_reply(update, context, text)

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
        dealer_peek = game.get_card_str(game.dealer_hand, True)
        my_hand = game.get_card_str(game.hands[curr_uid])
        my_score = game.get_score(game.hands[curr_uid])
        # 单一权威面板：牌桌+操作按钮同一条消息，原地编辑不闪跳；信息不再写两遍
        lines = ["🃏 <b>21点</b>", f"🏛 庄家：{dealer_peek}", "━━━━━━━━━━━━━━━━━"]
        for i, uid in enumerate(game.players, 1):
            mark = "👉" if uid == curr_uid else ""
            lines.append(f"{mark}{i}. {await get_name(app, uid)} {game.get_card_str(game.hands[uid])} ({game.get_score(game.hands[uid])})")
        lines.append(f"⏳ <b>{await get_name(app, curr_uid)}</b> 行动｜我 {my_hand} ({my_score}点)")
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
            text = f"🃏 <b>21点 结算</b>\n━━━━━━━━━━━━━━━━━\n🏛 <b>庄家</b>：{game.get_card_str(game.dealer_hand)} ({d_score})\n\n"
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
                # 抽水在面板体现：赢家用「实收」显示税后，不再单独发抽水消息
                r_amt = calc_rake({uid: net})[1].get(uid, 0) if game.mode == "official" else 0
                rake_txt = f"（实收 {net - r_amt}，含抽水{r_amt}）" if r_amt else ""
                lines.append(f"👤 <b>玩家</b>：{player_names[uid]} | {hand_text} ({p_score})\n<b>结果</b>：{result_str} | 盈亏 {net:+d}{rake_txt}")
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
            settled_msgs = await safe_send_long(app.bot, game.chat_id, text, parse_mode="HTML")
            if SETTLE_DELETE_SECONDS > 0:
                schedule_delete(app, game.chat_id, settled_msgs, SETTLE_DELETE_SECONDS)
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







async def _game_gate(update, context, game):
    """4 游戏总开关/仅管理员开局（后台各游戏分组设置，保存立即生效）。返回 True=放行。"""
    label, enabled, admin_only = {
        "texas":     ("德州扑克", TEXAS_ENABLED, TEXAS_ADMIN_ONLY),
        "blackjack": ("21点", BJ_ENABLED, BJ_ADMIN_ONLY),
        "jinhua":    ("炸金花", JINHUA_ENABLED, JINHUA_ADMIN_ONLY),
        "race":      ("赛车", RACE_ENABLED, RACE_ADMIN_ONLY),
    }[game]
    if not enabled:
        await send_reply(update, context, f"❌ {label}已关闭（管理员可在后台「{label}」分组重新开启）。")
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

# ==================== 骰子 ====================



















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
RACE_HOURLY_END = 23         # 自动开赛时段-结束点(几点,含)，如 22 = 22点那场仍开；起始>结束=全天不开
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
        """该玩家本轮应投入的实际金额 = 闷牌单位 × (看牌 2 倍 / 闷牌 1 倍)。
        加倍开关关闭时看牌与闷牌同价。"""
        mult = 2 if (uid in self.seen and JINHUA_SEEN_DOUBLE) else 1
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
        if extra < JINHUA_BASE: return False, f"最低加注为 {JINHUA_BASE}"
        if uid in self.raise_locked: return False, "短全下后已行动玩家只能跟注或弃牌"
        # 先按校验后的值计算目标投入，余额不足直接拒绝，绝不先改 current_bet
        mult = 2 if (uid in self.seen and JINHUA_SEEN_DOUBLE) else 1
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
        mult = 2 if (uid in self.seen and JINHUA_SEEN_DOUBLE) else 1
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
    return f"🌸 新一局炸金花\n发起人：{await get_name(app, game.owner_id)}\n\n已加入：\n" + "\n".join(players) + "\n\n点击加入，发起人可立即开始。\n⏰ 满 2 人后 60 秒自动开局，不足 2 人 60 秒后自动解散。"


async def update_jinhua_waiting(game, app):
    rows = [[InlineKeyboardButton("📥 加入游戏", callback_data="jh_join")]]
    if len(game.players) >= 2: rows.append([InlineKeyboardButton("🎮 开始游戏", callback_data="jh_start")])
    rows.append([InlineKeyboardButton("❌ 终止房间", callback_data="jh_end")])
    await safe_edit(app.bot, game.chat_id, game.game_msg_id, await jinhua_waiting_text(game, app), reply_markup=InlineKeyboardMarkup(rows))


async def jinhua_table_text(game, app):
    lines = [
        "🌸 炸金花",
        f"💰 奖池 {game.pot}｜单注 {game.current_bet}" + ("（看牌者×2）" if JINHUA_SEEN_DOUBLE else ""),
    ]
    if game.last_action:
        lines.append(f"🔔 上一手：{game.last_action}")
    current = game.current() if game.phase == "betting" else None
    if current:
        lines.append(f"⏳ 当前行动：{await get_name(app, current)}｜需补：{max(0, game._target(current) - game.round_bets[current])}")
    lines.append("━━━━━━━━━━━━━━━━━")
    # 紧凑排版：每人 1 行；👉 标记当前行动者（与德州/21点一致）
    for index, uid in enumerate(game.players, 1):
        status = "❌弃" if uid in game.folded else "🔥全下" if uid in game.all_in else "🟢"
        seen_mark = "👁" if uid in game.seen else "🎴"
        mark = "👉" if uid == current else ""
        lines.append(f"{mark}{index}. {await get_name(app, uid)} {seen_mark}{status} 投{game.total_bet[uid]} 余{game.chips[uid]}")
    return "\n".join(lines)


def jinhua_buttons(game, uid):
    """紧凑布局：非行动玩家仅「看牌」；行动玩家每行最多2按钮（看牌|弃牌 → 跟注|比牌 → 加注|刷新 → 全下）。"""
    if uid not in game.folded:
        label = "🃏 查看手牌" if uid in game.seen else "👁 看牌"
        if uid != game.current():
            return InlineKeyboardMarkup([[InlineKeyboardButton(label, callback_data="jh_see")]])
    else:
        return InlineKeyboardMarkup([[InlineKeyboardButton("🔄 刷新界面", callback_data="jh_refresh")]])
    to_call = max(0, game._target(uid) - game.round_bets[uid])
    # 每行最多2个按钮压宽度（面板宽度=最宽行）：看牌|弃牌 / 跟注|比牌 / 加注|刷新 / 全下独占
    rows = [[InlineKeyboardButton(label, callback_data="jh_see"),
             InlineKeyboardButton("❌ 弃牌", callback_data="jh_fold")]]
    row_call = [InlineKeyboardButton("✅ 过牌" if not to_call else f"✅ 跟注 {to_call}", callback_data="jh_call")]
    if sum(1 for p in game.players if p not in game.folded) >= 2:
        row_call.append(InlineKeyboardButton("⚔️ 比牌", callback_data="jh_compare_menu"))
    rows.append(row_call)
    row_raise = []
    if uid not in game.raise_locked and game.chips[uid] >= to_call + JINHUA_BASE:
        row_raise.append(InlineKeyboardButton(f"🔼 加注 {JINHUA_BASE}", callback_data=f"jh_raise_{JINHUA_BASE}"))
    row_raise.append(InlineKeyboardButton("🔄 刷新", callback_data="jh_refresh"))
    rows.append(row_raise)
    if game.chips[uid] > 0:
        rows.append([InlineKeyboardButton(f"🔥 全下 {game.chips[uid]}", callback_data="jh_allin")])
    return InlineKeyboardMarkup(rows)


async def _sync_jinhua_msg(game, app, text, kb):
    """渲染唯一权威牌桌消息：删旧发新，让牌桌永远停在群最新位置（不被聊天顶上去），全群始终只有这一条。

    流程：先发新消息（更新 game_msg_id）再删旧消息，避免牌桌短暂消失；发送失败则回退原地编辑兜底。
    加锁避免快速连续操作（连点/超时与点击并发）时出现两条牌桌。
    """
    async with game._render_lock:
        old_id = game.game_msg_id
        # 群反馈：每次删旧发新牌桌乱跳难操作 → 优先原地编辑（按钮位置稳定），失败才重发兜底
        if old_id:
            edited = await safe_edit(app.bot, game.chat_id, old_id, text, reply_markup=kb, parse_mode="HTML")
            if edited is not None:
                return
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
            [InlineKeyboardButton(f"🔼 继续加注 {JINHUA_BASE}", callback_data=f"jh_raise_{JINHUA_BASE}"),
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
        # 抽水先算（官方模式），面板「盈亏」行直接带实收
        _nets = {uid: game.chips[uid] - game.initial_chips[uid] for uid in game.players} \
            if game.mode == "official" else {}
        rake_per = calc_rake(_nets)[1] if _nets else {}
        lines.append("投入 / 盈亏：")
        for uid in game.players:
            net = game.chips[uid] - game.initial_chips[uid]
            if game.mode == "official":
                jinhua_profit_by_date[date][game.chat_id][uid] += net
            r_amt = rake_per.get(uid, 0)
            r_txt = f"（实收 {net - r_amt}，含抽水{r_amt}）" if r_amt else ""
            lines.extend([f"{names[uid]}：投入 {game.total_bet[uid]}｜盈亏 {net:+d}{r_txt}", ""])
        # 资金流审查：官方模式把本局人对人净转移记账（防"故意输牌/比牌倒赔送分"）
        if game.mode == "official":
            record_game_flows(game.chat_id, _nets, "金花")
            await commit_rake(app, game.chat_id, rake_per, "金花")
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
        if game.mode == "official":
            rank = sorted(jinhua_profit_by_date[date][game.chat_id].items(), key=lambda item: item[1], reverse=True)[:50]
            lines.extend(["", "🏆 <b>当日炸金花累计盈利榜</b>", "━━━━━━━━━━━━━━━━━"])
            lines.extend([f"{rank_marker(index)} {names.get(uid) or await get_name(app, uid)}：{amount:+d}" for index, (uid, amount) in enumerate(rank, 1)])
        await safe_delete(app.bot, game.chat_id, game.game_msg_id)
        delivered = await safe_send_long(app.bot, game.chat_id, "\n".join(lines), parse_mode="HTML")
        if SETTLE_DELETE_SECONDS > 0:
            schedule_delete(app, game.chat_id, delivered, SETTLE_DELETE_SECONDS)
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
    if not await need_auth(update, context): return
    if not await _game_gate(update, context, "jinhua"): return
    if not await require_group_chat(update, "炸金花", "jinhua", context): return
    cid, uid = update.effective_chat.id, update.effective_user.id
    game = active_jinhua_games.get(cid)
    room_name, _ = poker_room_of(cid, uid, exclude_game=game)
    if room_name:
        await send_reply(update, context, f"⚠️ 你已在 {room_name} 房间，请先结束再开新的扑克游戏。"); return
    mode = game.mode if game and game.phase == "waiting" else current_game_mode()
    if game_chips[cid][uid] < MIN_ENTRY_CHIPS:
        await send_reply(update, context, f"❌ 进入炸金花至少需要 {MIN_ENTRY_CHIPS} 积分。"); return
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
    if not await need_auth(update, context): return
    if not await _game_gate(update, context, "texas"): return
    if not await require_group_chat(update, "德州扑克", "dz", context): return
    cid, uid = update.effective_chat.id, update.effective_user.id; game = active_poker_games.get(cid)
    room_name, _ = poker_room_of(cid, uid, exclude_game=game)
    if room_name:
        await send_reply(update, context, f"⚠️ 你已在 {room_name} 房间，请先结束再开新的扑克游戏。"); return
    mode = game.mode if game and game.phase == "waiting" else current_game_mode()
    wallet = game_chips
    if wallet[cid][uid] < MIN_ENTRY_CHIPS:
        label = "积分"
        await send_reply(update, context, f"❌ 进入德州至少需要 {MIN_ENTRY_CHIPS} {label}。"); return
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
    if not await need_auth(update, context): return
    if not await require_group_chat(update, "德州排位赛", "排位", context): return
    cid, uid = update.effective_chat.id, update.effective_user.id
    ok, key = await season_signup(context.application, cid, uid)
    await render_season_lobby(context.application, cid)
    if key == "started":
        await send_reply(update, context, f"🏆 报名满 {SEASON_MIN_PLAYERS} 人，第{season_id}赛季「{season_name or '排位赛'}」开始！每人 {SEASON_START_CHIPS} 分，周期 {SEASON_DAYS} 天。用 /排位 开局。")
    elif key == "joined_active":
        await send_reply(update, context, f"✅ 已加入进行中的赛季（需满 {SEASON_MIN_GAMES} 局才上榜）。当前分 {season_points[cid][uid]}。用 /排位 开局。")
    else:
        n = len(season_joined[cid])
        await send_reply(update, context, f"✅ 已报名本赛季排位赛（{n}/{SEASON_MIN_PLAYERS}）。满 {SEASON_MIN_PLAYERS} 人自动开赛；也可点群里的大厅看板报名。")


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
        await send_reply(update, context, f"🏆 第{season_id}赛季「{season_name or '排位赛'}」由管理员强制开启！每人 {SEASON_START_CHIPS} 分，周期 {SEASON_DAYS} 天。用 /排位 开局。")
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
    await safe_send_long(context.bot, cid, "\n".join(lines))


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
        await safe_send_long(context.bot, update.effective_chat.id, text, parse_mode="HTML")
    except Exception:
        # 历史称号含 < & 等特殊字符导致 HTML 渲染失败时，降级为纯文本发送，避免命令“失效无响应”
        await safe_send_long(context.bot, update.effective_chat.id, text)


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
    await safe_send_long(context.bot, update.effective_chat.id, "\n".join(lines), parse_mode="HTML")


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
    await safe_send_long(context.bot, update.effective_chat.id, "\n".join(lines), parse_mode="HTML")


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


async def cmd_season_help(update, context):
    if not await need_auth(update, context): return
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
    if not await need_auth(update, context): return
    if not await require_group_chat(update, "德州排位赛", "排位", context): return
    cid, uid = update.effective_chat.id, update.effective_user.id
    if not season_active:
        ok, key = await season_signup(context.application, cid, uid)
        if key == "started":
            await render_season_lobby(context.application, cid)  # 满 20 自动开赛：翻转看板为进行中，继续往下开房
        else:
            # UX2：/排位 静默报名不弹看板（看板仅在 /排位报名 或按钮点击时出现，减少刷屏）
            n = len(season_joined[cid])
            await send_reply(update, context, f"✅ 已报名本赛季排位赛（{n}/{SEASON_MIN_PLAYERS}）。满 {SEASON_MIN_PLAYERS} 人自动开赛；发 /排位报名 可看报名大厅。")
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
        await send_reply(update, context, "❌ 你的排位分已用完，等待应急补分或下局。"); return
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
    game = PokerGame(cid, uid, current_game_mode(), season=True); game.add(uid); active_poker_games[cid] = game
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
        # 已有赛车：直接把当前带按钮的看板重发出来，让后发的人也能立刻看到/参与，而不是只回一句文字
        if getattr(race, "phase", "") == "betting":
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
    schedule_delete_ids(app, game.chat_id, game.game_msg_id, PANEL_DELETE_SECONDS)
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


async def cmd_my_invite(update, context):
    """我的邀请进度（对标竞品）：已计入/合格人数/累计奖励/专属链接，一眼看清到哪一步。"""
    if not await need_auth(update, context): return
    if not INVITE_ENABLED:
        await send_reply(update, context, "❌ 邀请系统未开启。"); return
    if is_group_chat(update):
        cid, cname = update.effective_chat.id, (getattr(update.effective_chat, "title", "") or "本群")
    else:
        cid, cname = None, "全部群"
    uid = update.effective_user.id
    total = ok_n = left_n = pending_n = award_sum = 0
    for rec in invite_records.values():
        if rec.get("inviter") != uid: continue
        if cid is not None and rec.get("cid") != cid: continue
        if rec.get("audit") == "ok":
            total += 1
            if rec.get("left"): left_n += 1
            else: ok_n += 1
            award_sum += int(rec.get("award", 0) or 0)
        elif rec.get("audit") in ("pending", "unmet"):
            pending_n += 1
    mine = invite_links.get(cid, {}).get(uid) if cid is not None else None
    cname = "全部群" if cid is None else (chat_name_cache.get(cid) or str(cid))
    my_name = await get_name(context.application, uid)
    lines = [
        f"<b>🌸 我的邀请进度</b>｜{html.escape(cname)}",
        f"<b>邀请人</b>　{html.escape(my_name)} <code>{uid}</code>",
        f"<b>已计入</b>　{ok_n} 人",
    ]
    if left_n: lines.append(f"<b>已退群</b>　{left_n} 人（不计排行）")
    if pending_n: lines.append(f"<b>待审核</b>　{pending_n} 人")
    lines.append(f"<b>累计奖励</b>　{award_sum} 分（每成功 1 位 +{INVITE_REWARD} 分）")
    if mine:
        lines.append("")
        lines.append("<b>我的专属链接</b>")
        lines.append(f"<code>{mine.get('link', '')}</code>")
    else:
        lines.append("")
        lines.append("📌 本群还没有你的专属链接，发「邀请」即可领取。")
    await send_reply(update, context, "\n".join(lines))


async def cmd_invite_debug(update, context):
    """邀请系统体检（管理员）：bot 自查权限/事件源/数据，一条命令定位「为什么进人不加分」。"""
    if not await need_auth(update, context): return
    if not is_bot_admin(update.effective_user.id):
        await send_reply(update, context, "❌ 邀请调试仅管理员可用。"); return
    cid = update.effective_chat.id
    L = ["🔧 邀请系统体检（本群）", "━━━━━━━━━━━━━━━━━"]
    L.append(f"开关：{'开' if INVITE_ENABLED else '关'}｜自动批准：{'开' if INVITE_AUTO_APPROVE else '关'}")
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
        L.append("发「邀请」→ 复制链接 → 换一个号点链接 → 应自动批准并入群加分。")
        L.append("若仍无事件，说明群里进的人不是通过 bot 专属链接（普通拉人/群链接不算邀请）。")
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

    if not any([poker, race, bj, jinhua]):
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
        await send_reply(update, context, "❌ 仅 Bot 管理员可操作"); return
    if not ADMIN_ADJUST_ENABLED:
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
        old_bal = game_chips[cid][uid]
        game_chips[cid][uid] += amount; save_data()
    verb = "添加" if amount > 0 else "扣除"
    msg = _fmt_tpl("add_msg_tpl", target=await get_name(context.application, uid),
                   verb=verb, amount=abs(amount), balance=game_chips[cid][uid])
    await send_reply(update, context, msg)
    await _check_level_change(context.application, cid, uid, old_bal, game_chips[cid][uid])



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
        if REPLY_DELETE_SECONDS > 0 and is_group_chat(update):
            schedule_delete(context.application, cid, reply, REPLY_DELETE_SECONDS)
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
    if REPLY_DELETE_SECONDS > 0 and is_group_chat(update):
        schedule_delete(context.application, cid, msgs, REPLY_DELETE_SECONDS)

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
    if REPLY_DELETE_SECONDS > 0 and is_group_chat(update):
        schedule_delete(context.application, cid, msgs, REPLY_DELETE_SECONDS)

async def cmd_sq(update, context):
    if not is_bot_admin(update.effective_user.id):
        await send_reply(update, context, "❌ 仅 Bot 管理员可操作"); return
    if not is_group_chat(update):
        await send_reply(update, context, "⚠️ 授权需在群聊中进行：请在目标群里发送 /授权，机器人会把该群加入授权名单。私聊里授权无意义，且会导致游戏开在私聊、别人看不到。")
        return
    cid = update.effective_chat.id
    AUTHORIZED_GROUPS.add(cid); save_data()
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
    await safe_send_long(context.bot, update.effective_chat.id, "\n".join(lines))

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
    await safe_send_long(context.bot, update.effective_chat.id, "\n".join(lines), parse_mode="HTML")

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

    await safe_send_long(context.bot, update.effective_chat.id, "\n".join(lines), parse_mode="HTML")

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
    await safe_send_long(context.bot, update.effective_chat.id, "\n".join(lines), parse_mode="HTML")

async def cmd_autosm(update, context):
    if not await need_auth(update, context): return
    if not is_bot_admin(update.effective_user.id): await send_reply(update, context, "❌ 仅 Bot 管理员可操作"); return
    cid = update.effective_chat.id
    cur = hourly_race_enabled.get(cid, True)   # 授权群默认开启，此处按群覆盖
    hourly_race_enabled[cid] = not cur; save_data()
    await send_reply(update, context, f"本群整点自动赛车：{'✅ 已开启' if not cur else '❌ 已关闭（总开关和时段仍需在后台配置）'}")

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
        if data == "noop": await q.answer(); return  # 占位按钮（售罄/页码），点了不报错
        
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
            # 下注阶段：当前玩家操作；跟平阶段（open_pending）允许任意存活玩家弃牌止损
            if data == "jh_fold" and game.phase == "open_pending":
                if uid in game.folded:
                    await q.answer("你已弃牌", show_alert=True); return
                ok, desc = game.action(uid, "fold")
                if not ok: await q.answer(desc, show_alert=True); return
                await q.answer(desc)
                game.last_action = f"{await get_name(context.application, uid)} 弃牌"
                if game.phase == "showdown": await settle_jinhua(game, context.application)
                else: await show_jinhua_action(game, context.application)
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
            elif game.phase == "open_pending": await show_jinhua_action(game, context.application)
            else: await start_jinhua_turn_timer(game, context.application)
            return
        # --- 积分商城：点蓝色按钮直接兑换 / 翻页 / 商品详情 ---
        if data.startswith("mall_buy_") or data.startswith("mall_show_") or data.startswith("mall_page_"):
            cid, uid = q.message.chat.id, q.from_user.id
            if data.startswith("mall_show_"):
                # 商品详情：弹出商品信息，1 秒后回到原列表
                try: idx = int(data[len("mall_show_"):])
                except ValueError: await q.answer(); return
                items = [x for x in MALL_ITEMS if x.get("on", True)]
                if not (1 <= idx <= len(items)): await q.answer("商品已下架", show_alert=True); return
                it = items[idx - 1]
                stk = it.get("stock")
                stk_txt = "不限量" if not isinstance(stk, int) else (f"剩 {stk}" if stk > 0 else "已售罄")
                await q.answer(f"#{idx} {it['name']}\n价格 {_mall_price(it)} 分｜{stk_txt}\n点 ✅ 立即兑换 直接购买", show_alert=True)
                return
            if data.startswith("mall_buy_"):
                try: idx = int(data[len("mall_buy_"):])
                except ValueError: await q.answer(); return
                if not MALL_ENABLED: await q.answer("商城未开启", show_alert=True); return
                items = [x for x in MALL_ITEMS if x.get("on", True)]
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
                # 在原按钮消息就地刷新为新页（编辑消息按钮）
                items = [x for x in MALL_ITEMS if x.get("on", True)]
                if not items: await q.answer("商城已空"); return
                pages = max(1, (len(items) + MALL_PAGE_SIZE - 1) // MALL_PAGE_SIZE)
                page = max(1, min(page, pages))
                chunk = items[(page - 1) * MALL_PAGE_SIZE: page * MALL_PAGE_SIZE]
                new_rows = []
                for i, item in enumerate(chunk, (page - 1) * MALL_PAGE_SIZE + 1):
                    sb = item.get("stock")
                    if isinstance(sb, int) and sb <= 0:
                        new_rows.append([InlineKeyboardButton(f"{i}. {item['name']}（已售罄）", callback_data="noop")])
                    else:
                        new_rows.append([InlineKeyboardButton(f"{i}. {item['name']} — {_mall_price(item)} 积分 ✅ 立即兑换", callback_data=f"mall_buy_{i}")])
                nav = []
                if page > 1: nav.append(InlineKeyboardButton("⬅ 上一页", callback_data=f"mall_page_{page-1}"))
                if pages > 1: nav.append(InlineKeyboardButton(f"📄 {page}/{pages}", callback_data="noop"))
                if page < pages: nav.append(InlineKeyboardButton("➡ 下一页", callback_data=f"mall_page_{page+1}"))
                if nav: new_rows.append(nav)
                try:
                    await q.message.edit_reply_markup(reply_markup=InlineKeyboardMarkup(new_rows))
                except Exception: pass
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
            race.name_cache[uid] = await get_name(context.application, uid); await q.answer(desc); await action_notice(cid, context.application, uid, f"下注 {amount} 于 {HORSE_EMOJI[horse]}")
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
    recent = [t for t in hist if now - t <= ANTISPAM_WINDOW]
    if len(recent) >= ANTISPAM_REPEAT_N:
        return "repeat"
    if len(hist) >= ANTISPAM_TIMER_N:
        ivs = [b - a for a, b in zip(hist, hist[1:])][-(ANTISPAM_TIMER_N - 1):]
        mean = sum(ivs) / len(ivs)
        if mean >= 30 and all(abs(iv - mean) <= mean * ANTISPAM_TIMER_TOL / 100 for iv in ivs):
            return "timer"
    return None

async def _antispam_hit(update, context, cid, uid, reason):
    """命中处理：撤删本条 → 清该用户统计防连环触发 → 禁言（累犯翻倍）→ 群内通告。"""
    message = update.effective_message
    try: await message.delete()
    except TelegramError: pass
    for k in [k for k in antispam_hist if k[0] == cid and k[1] == uid]:
        antispam_hist.pop(k, None)
    offs = antispam_offense.setdefault((cid, uid), [])
    offs.append(time.time())
    n = len(offs)
    mute = ANTISPAM_MUTE_SECONDS * (2 ** (n - 1)) if ANTISPAM_MUTE_ESCALATE else ANTISPAM_MUTE_SECONDS
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
        tip += f"，禁言 {mins} 分钟" + ("（累犯加倍）" if n > 1 and ANTISPAM_MUTE_ESCALATE else "")
    elif ANTISPAM_MUTE_SECONDS > 0:
        tip += "（我需要管理员禁言权限才能禁言）"
    try:
        m = await context.bot.send_message(cid, tip)
        if ANTISPAM_NOTICE_SECONDS > 0:
            schedule_delete(context.application, cid, m, ANTISPAM_NOTICE_SECONDS)
    except TelegramError: pass

def _autodel_text_hit(message, text):
    """自动删除规则（文本类）：返回规则名或 None。开关即法律，网页「自动删除」页可改。"""
    if AUTODEL_LINKS and text and ("http://" in text or "https://" in text or "t.me/" in text
            or any(getattr(e, "type", None) in ("url", "text_link") for e in (message.entities or []))):
        return "links"
    if AUTODEL_LONG_ENABLED and text and len(text) > max(50, int(AUTODEL_LONG_LEN)):
        return "long"
    if AUTODEL_PREMIUM_EMOJI and any(getattr(e, "type", None) == "custom_emoji" for e in (message.entities or [])):
        return "premium_emoji"
    return None

def _autodel_media_hit(message):
    """自动删除规则（媒体类）：返回规则名或 None。"""
    if message is None:
        return None
    if (message.new_chat_members or message.left_chat_member or message.new_chat_title
            or message.new_chat_photo or message.pinned_message or message.group_chat_created
            or message.supergroup_chat_created or message.migrate_to_chat_id):
        return "service" if AUTODEL_SERVICE else None
    if message.sticker is not None:
        return "sticker" if AUTODEL_STICKER else None
    if message.animation is not None:
        return "gif" if AUTODEL_GIF else None
    if message.voice is not None or message.video_note is not None:
        return "voice" if AUTODEL_VOICE else None
    if message.contact is not None:
        return "contact" if AUTODEL_CONTACT else None
    if message.document is not None:
        name = (message.document.file_name or "").lower()
        mt = message.document.mime_type or ""
        if AUTODEL_ARCHIVE and (mt in ("application/zip", "application/x-rar-compressed",
                                       "application/x-7z-compressed", "application/gzip", "application/x-tar")
                or name.endswith((".zip", ".rar", ".7z", ".tar", ".gz"))):
            return "archive"
        if AUTODEL_EXECUTABLE and (mt in ("application/x-msdownload", "application/vnd.android.package-archive",
                                          "application/x-dosexec")
                or name.endswith((".exe", ".msi", ".bat", ".cmd", ".scr", ".apk", ".com"))):
            return "executable"
        return "document" if AUTODEL_DOCUMENT else None
    if message.photo:
        return "photo" if AUTODEL_PHOTO else None
    if message.video is not None:
        return "video" if AUTODEL_VIDEO else None
    return None

async def _autodel_enforce(update, context):
    """自动删除规则执行：命中即静默撤删。返回 True 表示已删（调用方应停止后续处理）。管理员豁免。"""
    user, message = update.effective_user, update.effective_message
    if not user or user.is_bot or not message or not is_group_chat(update):
        return False
    if is_bot_admin(user.id):
        return False
    if _autodel_text_hit(message, message.text or message.caption or "") or _autodel_media_hit(message):
        try:
            await message.delete()
        except TelegramError:
            pass
        return True
    return False

async def on_media(update, context):
    """自动删除规则中心：非文本消息（图/视频/贴纸/文件/联系人/系统消息等）按开关静默撤删。"""
    try:
        if await _autodel_enforce(update, context):
            return
    except Exception:
        logger.exception("自动删除(媒体)异常（已吞并）")

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
            await send_reply(update, context, "🚫 你已被禁止使用本机器人，如有疑问请联系管理员。"); return

        # 新成员观察期：入群未满观察时长的成员发言即删，并禁言至观察期结束（管理员豁免）
        if OBSERVE_ENABLED and OBSERVE_SECONDS > 0 and is_group_chat(update) and not is_bot_admin(user.id):
            _jt = member_joined_at.get(cid, {}).get(user.id, 0)
            _elapsed = time.time() - _jt if _jt else 1e9
            if _elapsed < OBSERVE_SECONDS:
                try:
                    await context.bot.delete_message(chat_id=cid, message_id=message.message_id)
                    await context.bot.restrict_chat_member(
                        cid, user.id, permissions=ChatPermissions(can_send_messages=False),
                        until_date=datetime.now(timezone.utc) + timedelta(seconds=OBSERVE_SECONDS - _elapsed + 1))
                except TelegramError: pass
                return

        # 自动删除规则中心：链接/超长/会员表情（媒体消息走 on_media；管理员豁免）
        if await _autodel_enforce(update, context):
            return

        # 定时刷屏识别：复读机 + 定时器特征（管理员豁免；内容太短不参与统计防误伤闲聊）
        if (ANTISPAM_ENABLED and is_group_chat(update) and not is_bot_admin(user.id)
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
            if _alo and text.strip() in {LOTTERY_KEYWORD, (_alo.get("keyword") or "").strip()}:
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
            if not found: await send_reply(update, context, "💡 当前没有任何正在进行的游戏。")
            return

        # 21点文字加入
        blackjack = active_blackjack_games.get(cid)
        bj_match = re.fullmatch(r"(?:下注|下|押|买)?(?:21点|21)\s*(\d+)", text)
        if bj_match and blackjack:
            if blackjack.phase != "waiting":
                await send_reply(update, context, "❌ 21点已经开始，请等待下一局。"); return
            amount = int(bj_match.group(1))
            if amount < BJ_MIN_BET:
                await send_reply(update, context, f"❌ 21点最低下注 {BJ_MIN_BET} 积分。"); return
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
    except Exception:
        logger.exception("文本指令处理异常")
        # 命令分发异常不再静默：给用户明确反馈，便于排查而非毫无反应
        try:
            await send_reply(update, context, "⚠️ 指令处理出错，请联系管理员。")
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

def _level_rank(lv_name):
    """等级名 -> 在等级表中的序号（升序），未找到返回 -1。"""
    for i, item in enumerate(POINT_LEVELS):
        if item["name"] == lv_name:
            return i
    return -1

async def _check_level_change(app, cid, uid, old_bal, new_bal):
    """余额变动后检查积分等级升降并发群内通知（LEVEL_NOTIFY_ENABLED 控制）。

    接入点：签到 / 管理员加减分 / 转赠双方 / 商城兑换 / 红包领取。
    聊天积分小额高频，刻意不接（避免刷屏）。
    """
    try:
        if not LEVEL_NOTIFY_ENABLED or new_bal == old_bal or not POINT_LEVELS:
            return
        old_lv, new_lv = _get_level(old_bal), _get_level(new_bal)
        if old_lv == new_lv:
            return
        name = await get_name(app, uid, cid=cid)
        if _level_rank(new_lv) > _level_rank(old_lv):
            await send_settle(app, cid, _fmt_tpl("level_up_msg_tpl", name=name, level=new_lv, balance=new_bal))
        elif old_lv:
            await send_settle(app, cid, _fmt_tpl("level_down_msg_tpl", name=name, level=new_lv or "无等级", balance=new_bal))
    except Exception:
        logger.exception("等级变动通知失败（已忽略）")

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
    if not POINT_LEVELS:
        await send_reply(update, context, "ℹ️ 积分等级未配置（后台「积分系统 → 积分等级」添加）。"); return
    bal = game_chips[cid][uid]
    lv = _get_level(bal)
    next_lv, next_val = "", None
    for item in POINT_LEVELS:
        if item["value"] > bal and (next_val is None or item["value"] < next_val):
            next_lv, next_val = item["name"], item["value"]
    nxt = f"\n⬆️ 下一等级：{next_lv}（还差 {next_val - bal} 积分）" if next_lv else "\n🏆 你已是最高等级！"
    await send_reply(update, context,
                     f"🎖 {await get_name(context.application, uid)} 的等级：{lv or '无'}\n💰 积分：{bal}{nxt}")

def _award_chat_points(cid, uid, text):
    """聊天积分：优先走网页配置的规则表（阿福式：文字/长度条件 → 分值，命中即停）；
    规则表为空或全停时回退旧逻辑（每 N 字符记 X 分）。均受每日上限约束。"""
    if not CHAT_ENABLED:
        return
    t = text.strip()
    enabled = [r for r in chat_rules if r.get("on")]
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
        if CHAT_REWARD <= 0 or CHAT_CHARS_PER <= 0:
            return
        n = len(t)
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
    if not await need_auth(update, context): return
    if not SIGN_ENABLED:
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
    reward = SIGN_BASE_REWARD + (SIGN_STREAK_BONUS if streak % 7 == 0 else 0)
    async with wallet_locks[uid]:
        old_bal = game_chips[cid][uid]
        game_chips[cid][uid] += reward
        sign_data[cid][uid] = {"last": today, "streak": streak}
        save_data()
    bonus = "（含连续7天额外奖励）" if streak % 7 == 0 else ""
    msg = _fmt_tpl("sign_msg_tpl", name=await get_name(context.application, uid),
                   streak=streak, reward=reward, bonus=bonus, balance=game_chips[cid][uid])
    await send_reply(update, context, msg)
    await _check_level_change(context.application, cid, uid, old_bal, game_chips[cid][uid])

async def cmd_sign_rank(update, context):
    if not await need_auth(update, context): return
    cid = update.effective_chat.id
    users = [(uid, v.get("streak", 0)) for uid, v in sign_data.get(cid, {}).items() if v.get("streak", 0) > 0]
    if not users:
        await send_reply(update, context, "本群还没有签到记录，发「签到」抢头名！"); return
    lines = ["📅 连续签到排行", "━" * 14]
    for i, (uid, s) in enumerate(sorted(users, key=lambda x: (-x[1], x[0]))[:20], 1):
        lines.append(f"{rank_marker(i)} {await get_name(context.application, uid, cid=cid)}：连续 {s} 天")
    await safe_send_long(context.bot, cid, "\n".join(lines))

async def cmd_my_points(update, context):
    if not await need_auth(update, context): return
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
    reply = await send_reply(update, context, msg)
    if POINTS_DELETE_SECONDS > 0 and is_group_chat(update):
        async def _del():
            await asyncio.sleep(POINTS_DELETE_SECONDS)
            await safe_delete(context.bot, cid, update.message.message_id)
        asyncio.create_task(_del())
    if REPLY_DELETE_SECONDS > 0 and is_group_chat(update):
        schedule_delete(context.application, cid, reply, REPLY_DELETE_SECONDS)

async def cmd_points_rank(update, context):
    if not await need_auth(update, context): return
    cid = update.effective_chat.id
    lines = ["💰 积分排行榜", "━" * 14]
    for i, (uid, value) in enumerate(sorted(game_chips[cid].items(), key=lambda x: x[1], reverse=True)[:20], 1):
        lv = _get_level(value)
        tag = f"｜{lv}" if lv else ""
        lines.append(f"{rank_marker(i)} {await get_name(context.application, uid, cid=cid)}：{value}{tag}")
    msgs = await safe_send_long(context.bot, cid, "\n".join(lines))
    if REPLY_DELETE_SECONDS > 0 and is_group_chat(update):
        schedule_delete(context.application, cid, msgs, REPLY_DELETE_SECONDS)

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
    start, end = _parse_dt_bj(REDEEM_START), _parse_dt_bj(REDEEM_END)
    if start and now < start:
        return f"⏳ 兑换活动尚未开始（{REDEEM_START} 起）。"
    if end and now > end:
        return "🔚 兑换活动已结束。"
    return None

async def _redeem_execute(context, cid, uid, item):
    """执行兑换（命令与按钮回调共用）：限购→扣费→自动下架→台账→群通知+私聊通知。
    返回 None=成功；字符串=拒绝原因。"""
    if REDEEM_MAX_PER_USER > 0 and redeem_counts.get(uid, 0) >= REDEEM_MAX_PER_USER:
        return f"❌ 每人限兑 {REDEEM_MAX_PER_USER} 次，你已用完额度。"
    price = int(item.get("price", 0) or 0)
    left = int(item.get("left", 0) or 0)
    old_bal = game_chips[cid][uid]
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
    await _check_level_change(context.application, cid, uid, old_bal, game_chips[cid][uid])
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
    if gate:
        await q.answer(gate, show_alert=True); return
    items = [x for x in redeem_goods if x.get("on", True)
             and (not x.get("target_groups") or cid in x["target_groups"])]
    if not (1 <= idx <= len(items)):
        await q.answer("❌ 商品不存在或已下架，重新发「%s」看最新列表" % REDEEM_CMD, show_alert=True); return
    err = await _redeem_execute(context, cid, uid, items[idx - 1])
    if err:
        await q.answer(err, show_alert=True)
    else:
        await q.answer("🎉 兑换成功！")

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
    if not args:  # 商品按钮列表：点蓝色按钮直接兑换
        _cn = chat_name_cache.get(cid) or ""
        lines = [f"🎁 积分兑换｜{_cn}" if _cn else "🎁 积分兑换", "━" * 14]
        for i, x in enumerate(items, 1):
            left = int(x.get("left", 0) or 0)
            left_txt = "不限" if left <= 0 else str(left)
            lines.append(f"{i}. {x['name']}　—　{int(x.get('price', 0) or 0)} 积分　剩余 {left_txt}")
        lines.append("")
        mins = max(1, MALL_LIST_DELETE_SECONDS // 60)
        lines.append(f"💡 点下方蓝色按钮兑换（{mins} 分钟后消息自动删除）；也可发「{REDEEM_CMD} 编号/名称」")
        rows = []
        for i, x in enumerate(items, 1):
            price = int(x.get("price", 0) or 0)
            left = int(x.get("left", 0) or 0)
            left_txt = "不限" if left <= 0 else str(left)
            # 整行一个 button：与竞品一致——点商品行任何位置都直接兑换
            rows.append([InlineKeyboardButton(f"{i}. {x['name']} — {price} 积分 剩余 {left_txt}  ✅ 立即兑换", callback_data=f"redeem_buy_{i}")])
        msg = await safe_send(context.bot, cid, "\n".join(lines),
                              reply_markup=InlineKeyboardMarkup(rows))
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

async def cmd_mall(update, context):
    if not await need_auth(update, context): return
    if not MALL_ENABLED:
        await send_reply(update, context, "ℹ️ 积分商城未开启。"); return
    items = [x for x in MALL_ITEMS if x.get("on", True)]
    if not items:
        await send_reply(update, context, _fmt_tpl("mall_msg_empty")); return
    page = 1
    if context.args and context.args[0].isdigit():
        page = max(1, int(context.args[0]))
    pages = max(1, (len(items) + MALL_PAGE_SIZE - 1) // MALL_PAGE_SIZE)
    page = min(page, pages)
    chunk = items[(page - 1) * MALL_PAGE_SIZE: page * MALL_PAGE_SIZE]
    lines = [f"🛒 积分商城（{page}/{pages} 页）", "━" * 14]
    for i, item in enumerate(chunk, (page - 1) * MALL_PAGE_SIZE + 1):
        desc = str(item.get("desc", "") or "").strip()
        stk_txt = ""
        if isinstance(item.get("stock"), int):
            stk_txt = f"  剩余 {item['stock']}" if item['stock'] else "  已售罄"
        lines.append(f"{i}. {item['name']}　—　{_mall_price(item)} 积分{stk_txt}"
                     + (f"\n  　{desc}" if desc else ""))
    lines.append("")
    lines.append("💡 点击下方【立即兑换】按钮即可购买；翻页用【上一页/下一页】。")
    # 内联按钮：每商品一行（商品名 / 立即兑换），底部翻页
    rows = []
    for i, item in enumerate(chunk, (page - 1) * MALL_PAGE_SIZE + 1):
        stock_btn = item.get("stock")
        if isinstance(stock_btn, int) and stock_btn <= 0:
            rows.append([InlineKeyboardButton(f"{i}. {item['name']}（已售罄）", callback_data="noop")])
        else:
            # 整行一个 button：与竞品一致——点商品行任何位置都直接兑换
            rows.append([InlineKeyboardButton(f"{i}. {item['name']} — {_mall_price(item)} 积分 ✅ 立即兑换", callback_data=f"mall_buy_{i}")])
    nav = []
    if page > 1:
        nav.append(InlineKeyboardButton("⬅ 上一页", callback_data=f"mall_page_{page-1}"))
    if pages > 1:
        nav.append(InlineKeyboardButton(f"📄 {page}/{pages}", callback_data="noop"))
    if page < pages:
        nav.append(InlineKeyboardButton("➡ 下一页", callback_data=f"mall_page_{page+1}"))
    if nav: rows.append(nav)
    kb = InlineKeyboardMarkup(rows) if rows else None
    # 列表+按钮同条消息；delete_after=MALL_LIST_DELETE_SECONDS 让按钮活到用完再清群
    await send_reply(update, context, "\n".join(lines), kb=kb, delete_after=MALL_LIST_DELETE_SECONDS)

async def cmd_mall_buy(update, context):
    if not await need_auth(update, context): return
    if not is_group_chat(update):
        await send_reply(update, context, "⚠️ 购买请在群聊中进行。"); return
    if not MALL_ENABLED:
        await send_reply(update, context, "ℹ️ 积分商城未开启。"); return
    items = [x for x in MALL_ITEMS if x.get("on", True)]
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
    if MALL_MIN_AGE_DAYS > 0:  # 兑换门槛1：与 bot 首次互动满 N 天（小号没有历史）
        seen = user_first_seen.get(uid)
        days = (now_bj().timestamp() - seen) / 86400 if seen else 0.0
        if days < MALL_MIN_AGE_DAYS:
            await send_reply(update, context, f"❌ 兑换门槛：使用满 {MALL_MIN_AGE_DAYS} 天才能兑换（当前 {days:.0f} 天）。"); return
    if MALL_MIN_ACTIVE_DAYS > 0:  # 兑换门槛2：有游戏盈亏记录的天数 ≥N
        active_days = set()
        for prof in (poker_profit_by_date, race_profit_by_date, blackjack_profit_by_date, jinhua_profit_by_date):
            for d, chats in prof.items():
                if uid in (chats.get(cid) or {}): active_days.add(d)
        if len(active_days) < MALL_MIN_ACTIVE_DAYS:
            await send_reply(update, context, f"❌ 兑换门槛：累计 {MALL_MIN_ACTIVE_DAYS} 天参与游戏才能兑换（当前 {len(active_days)} 天）。"); return
    old_bal = game_chips[cid][uid]
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
    await _check_level_change(context.application, cid, uid, old_bal, game_chips[cid][uid])
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
    schedule_delete(context.application, cid, reply_msg, REPLY_DELETE_SECONDS)


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
    keyword = (form.get("keyword", [""])[0] or "").strip() or LOTTERY_KEYWORD
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
    if not LOTTERY_ENABLED: return
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
    return LOTTERY_MSG_START.format(
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
    """开奖：从参与者中按奖品库存随机抽；写回 lo['winners']/prizes 剩余库存；发群通知 + 私聊中奖者。"""
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
        text = LOTTERY_MSG_RESULT.format(
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

async def cmd_lottery(update, context):
    """群组抽奖：管理员用 /开奖 <标题> | <奖品> | <秒数> 开局；玩家用 /开奖 或 关键词 参与。

    用法：
      /开奖                              → 若活动进行中视为参与；否则帮助
      /开奖 <标题> | <奖品> | <秒数>      → 管理员开新活动
      /开奖开奖                           → 管理员手动立即开奖
      /开奖结束                           → 管理员强制结束并退款（按需）
    """
    if not await need_auth(update, context): return
    if not LOTTERY_ENABLED:
        await send_reply(update, context, "❌ 群组抽奖已关闭（后台「积分系统→群组抽奖」可开启）"); return
    cid = update.effective_chat.id
    uid = update.effective_user.id
    text = (update.message.text or "").strip()
    # 参与形态：/开奖、/抽奖、全局触发词、或本活动自定义关键词；其余原样交给开局参数
    _alo = _lottery_active(cid)
    _join_words = {LOTTERY_KEYWORD, "抽奖", (_alo.get("keyword") or "").strip() if _alo else ""}
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
            await _lottery_draw(context.application, cid, lo)
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
                LOTTERY_MSG_JOINED.format(nick=html.escape(name), n=info, balance=bal),
                parse_mode="HTML")
            # 公告上的已参与人数实时刷新
            await _lottery_refresh_announce(context.application, cid, lo)
        elif info == "dup":
            name = await get_name(context.application, uid)
            await send_reply(update, context, LOTTERY_MSG_DUP.format(nick=html.escape(name)))
        else:
            name = await get_name(context.application, uid)
            await send_reply(update, context, LOTTERY_MSG_FAIL.format(nick=html.escape(name), reason=info))
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
    duration = max(10, int(end_ts - time.time())) if end_ts else LOTTERY_DEFAULT_DURATION
    lotteries[cid] = {
        "title": title, "prizes": prizes, "fee": int(LOTTERY_FEE),
        "keyword": LOTTERY_KEYWORD, "start_ts": time.time(),
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
    base = (WEB_BASE_URL or "").strip().rstrip("/")
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
    if not REDPACKET_ENABLED:
        await send_reply(update, context, "ℹ️ 红包功能未开启。"); return
    if not is_group_chat(update):
        await send_reply(update, context, "⚠️ 红包请在群聊中发。"); return
    cid = update.effective_chat.id

    async def _reply(text):  # 机器人提示语也按后台设置自动删除
        reply = await send_reply(update, context, text)
        schedule_delete(context.application, cid, reply, REPLY_DELETE_SECONDS)

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
    if target and not RP_EXCLUSIVE_ENABLED:
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
        old_bal = game_chips[cid][uid]
        if p["left_n"] == 1:
            amt = p["left_amt"]
        elif RP_LUCK_ENABLED:  # 拼手气：随机拆分；关闭则平均分
            amt = random.randint(1, max(1, p["left_amt"] - p["left_n"] + 1))
        else:
            amt = max(1, p["left_amt"] // p["left_n"])
        async with wallet_locks[uid]:
            p["grabbed"][uid] = amt
            p["left_amt"] -= amt; p["left_n"] -= 1
            game_chips[cid][uid] += amt
            ledger_add(cid, p["from"], uid, amt, "红包")  # 资金流台账：发包人→领取人
            save_data()
    await q.answer(_fmt_tpl("rp_msg_grab", amount=amt, balance=game_chips[cid][uid]))
    await _check_level_change(context.application, cid, uid, old_bal, game_chips[cid][uid])
    total, count = sum(p["grabbed"].values()), len(p["grabbed"])
    if p["left_n"] <= 0:
        if RP_LOG_ENABLED:  # 手气排行：按金额降序，前三名带奖牌表情
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
    if not INHERIT_ENABLED:
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
    fee = amount * INHERIT_FEE_PERCENT // 100
    recv = amount - fee
    if INHERIT_DAILY_LIMIT > 0:  # 每日转赠总额上限（防小号互刷）
        today = now_bj().strftime("%Y-%m-%d")
        used = inherit_daily[today][cid].get(uid, 0)
        if used + amount > INHERIT_DAILY_LIMIT:
            await send_reply(update, context, f"❌ 超出每日转赠上限：今日已转出 {used}，上限 {INHERIT_DAILY_LIMIT}（网页「积分继承」可调）。"); return
    old_self, old_tgt = game_chips[cid][uid], game_chips[cid][target]
    async with wallet_locks[uid]:
        if game_chips[cid][uid] < amount:
            await send_reply(update, context, f"❌ 你的积分不足：需要 {amount}，当前 {game_chips[cid][uid]}。"); return
        game_chips[cid][uid] -= amount
        game_chips[cid][target] += recv
        if INHERIT_DAILY_LIMIT > 0:
            inherit_daily[now_bj().strftime("%Y-%m-%d")][cid][uid] += amount
        ledger_add(cid, uid, target, amount, "转赠")  # 资金流台账
        save_data()
    fee_txt = f"（手续费 {fee}）" if fee else ""
    await send_reply(update, context, _fmt_tpl("inherit_msg_ok",
        name=await get_name(context.application, uid), target=await get_name(context.application, target, cid=cid),
        amount=amount, fee=fee_txt, recv=recv, balance=game_chips[cid][uid]))
    await _check_level_change(context.application, cid, uid, old_self, game_chips[cid][uid])
    await _check_level_change(context.application, cid, target, old_tgt, game_chips[cid][target])


# ---------- 积分竞猜：管理开局面两方下注，封盘后按比例瓜分奖池 ----------
def _guess_buttons(cid):
    g = guesses[cid]
    return InlineKeyboardMarkup([[InlineKeyboardButton(f"🔵 {g['a']} {amt}", callback_data=f"guessbet_A_{amt}"),
                                  InlineKeyboardButton(f"🔴 {g['b']} {amt}", callback_data=f"guessbet_B_{amt}")]
                                 for amt in FIXED_BET_AMOUNTS])


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
    if amount < GUESS_MIN_BET:
        await q.answer(f"单注至少 {GUESS_MIN_BET} 积分", show_alert=True); return
    if GUESS_MAX_BET and amount > GUESS_MAX_BET:
        await q.answer(f"单注最多 {GUESS_MAX_BET} 积分", show_alert=True); return
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


async def _guess_do_settle(app, cid, winner):
    """结算：猜中方按注额比例瓜分全部奖池；无人猜中则奖池沉没。返回错误文案或 None。"""
    g = guesses.get(cid)
    if not g: return "本群没有进行中的竞猜"
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
        for uid, _s, _amt, old in paid:  # 等级联动（按派付后余额）
            await _check_level_change(app, cid, uid, old, game_chips[cid].get(uid, 0))
    else:
        lines = "\n（无人猜中，奖池沉没）"
    try:
        await send_settle(app, cid, f"🎯 竞猜结算｜{g['q']}\n✅ 答案：{ans_txt}｜奖池 {total} 分（{len(paid)} 人瓜分）" + lines)
    except Exception:
        logger.exception("竞猜结算播报异常（已吞并）")
    return None


async def _guess_do_cancel(app, cid):
    """撤销竞猜：全额退还托管注金。返回错误文案或 None。"""
    g = guesses.get(cid)
    if not g: return "本群没有进行中的竞猜"
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
        await send_settle(app, cid, f"🎯 竞猜「{g['q']}」已撤销，{n} 人的托管注金已全额退回。")
    except Exception:
        logger.exception("竞猜撤销播报异常（已吞并）")
    return None


async def _guess_do_create(app, cid, q, a, b, duration):
    """创建竞猜并发布到群（命令与网页共用）。返回错误文案或 None。"""
    if not GUESS_ENABLED:
        return "竞猜功能未开启（网页「积分系统 → 积分竞猜」可开启）"
    if cid in guesses:
        return "本群已有竞猜进行中，结算或撤销后再开"
    q, a, b = (q or "").strip()[:50], (a or "").strip()[:20], (b or "").strip()[:20]
    if not q or not a or not b:
        return "题目与选项 A/B 不能为空"
    try:
        duration = max(1, min(1440, int(duration)))
    except (TypeError, ValueError):
        duration = GUESS_DURATION
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
                                 parts[3] if len(parts) == 4 else GUESS_DURATION)
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
    if not BUY_ENABLED:
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
            await safe_send_long(context.bot, update.effective_chat.id, "\n".join(lines)); return
        await send_reply(update, context, f"用法：充值 数量（{BUY_MIN} ~ {BUY_MAX}）\n提交申请后联系管理员转账，管理员确认后积分自动到账。"); return
    pkg_arg = args[0].strip()
    amount = int(pkg_arg) if pkg_arg.isdigit() else None
    if amount is None:
        p = next((x for x in buy_packages if x.get("on") and x.get("name") == pkg_arg), None)
        if p:
            amount = int(p.get("points", 0) or 0)
    if not amount:
        await send_reply(update, context, "❌ 没有这个套餐；按数量充值用法：充值 数量。"); return
    from_pkg = amount is not None and not pkg_arg.isdigit()
    if not from_pkg and not (BUY_MIN <= amount <= BUY_MAX):
        await send_reply(update, context, f"❌ 单次购买需在 {BUY_MIN} ~ {BUY_MAX} 之间。"); return
    cid, uid = update.effective_chat.id, update.effective_user.id
    oid = secrets.token_hex(4)
    buy_orders[oid] = {"cid": cid, "uid": uid, "amount": amount, "ts": now_bj().strftime("%Y-%m-%d %H:%M")}
    save_data()
    await send_reply(update, context, f"📝 购买申请已提交：{amount} 积分（单号 {oid}）\n请联系管理员完成转账，确认后积分自动到账。")
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
    await safe_send_long(context.bot, cid, "\n".join(lines))

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
    await safe_send_long(context.bot, cid, "\n".join(lines))

# ---------- 邀请系统：专属链接追踪进群、奖励、审核、排行 ----------

def _invite_count(inviter, cid=None):
    """邀请人有效邀请数（audit=ok 且未退群）；cid 限定群，None=全部群。"""
    n = 0
    for rec in invite_records.values():
        if rec.get("inviter") != inviter or rec.get("audit") != "ok" or rec.get("left"):
            continue
        if cid is not None and rec.get("cid") != cid:
            continue
        n += 1
    return n


async def _invite_pre_reasons(cid, uid, cmu):
    """进群前置条件检查：返回未满足项名称列表（空=全部满足）。"""
    if not INVITE_PRE_ENABLED:
        return []
    reasons = []
    if INVITE_PRE_POINTS > 0 and game_chips.get(cid, {}).get(uid, 0) < INVITE_PRE_POINTS:
        reasons.append(f"积分≥{INVITE_PRE_POINTS}")
    if INVITE_PRE_MSGS > 0:
        msgs = int((member_profiles.get(cid, {}).get(uid, {}) or {}).get("msgs", 0) or 0)
        if msgs < INVITE_PRE_MSGS:
            reasons.append(f"发言≥{INVITE_PRE_MSGS}条")
    user = getattr(getattr(cmu, "new_chat_member", None), "user", None)
    if INVITE_PRE_AVATAR:
        try:
            photos = await _bot_app.bot.get_user_profile_photos(uid, limit=1)
            if not getattr(photos, "total_count", 0):
                reasons.append("有头像")
        except Exception:
            reasons.append("有头像")
    if INVITE_PRE_USERNAME and not getattr(user, "username", None):
        reasons.append("有用户名")
    return reasons


async def _invite_award(app, rec):
    """给邀请人发奖并通知（群内 + 私聊）。rec 需含 cid/inviter/invitee_name/audit。"""
    inviter, cid = rec["inviter"], rec["cid"]
    reward = max(0, int(INVITE_REWARD))
    if reward:
        old = game_chips[cid].get(inviter, 0)
        game_chips[cid][inviter] = old + reward
        rec["award"] = reward
        ledger_add(cid, 0, inviter, reward, "邀请奖励")
    inviter_name = await get_name(app, inviter, cid=cid)
    if INVITE_NOTIFY:
        try:
            await app.bot.send_message(chat_id=inviter,
                text=f"🎟️ 邀请成功！{rec.get('invitee_name', '')} 通过你的邀请进群，奖励 {reward} 积分已到账。")
        except Exception:
            pass
    if str(INVITE_OK_GROUP).strip():
        try:
            await app.bot.send_message(chat_id=cid, text=_fmt_tpl(
                "invite_ok_group", inviter=inviter_name, inviter_id=inviter,
                invitee=rec.get("invitee_name", ""), invitee_id=rec.get("invitee", ""), reward=reward))
        except Exception:
            pass
    save_data()


async def _invite_track_join(cmu, cid, uid, name, context):
    """邀请追踪：进群事件携带 invite_link 时匹配邀请人，记记录/发奖励/通知（所有异常吞并）。"""
    try:
        if not INVITE_ENABLED or uid <= 0 or cid not in AUTHORIZED_GROUPS:
            _inv_dbg(cid, f"进群 uid={uid} 跳过：开关{INVITE_ENABLED}/授权{cid in AUTHORIZED_GROUPS}")
            return
        key = f"{cid}:{uid}"
        if key in invite_records:   # 重复进群不重复计，仅视为回归
            invite_records[key]["left"] = False
            _inv_dbg(cid, f"进群 uid={uid} 重复（已有记录，视为回归）")
            return
        link = (getattr(getattr(cmu, "invite_link", None), "link", "")
                or invite_pending.pop(f"{cid}:{uid}", ""))   # 入群申请兜底：审批后的 join 事件常不带链接
        _inv_dbg(cid, f"进群 uid={uid} 事件链接：{link or '（无）'}")
        inviter = 0
        for i_uid, info in invite_links.get(cid, {}).items():
            if info.get("link") == link and i_uid != uid:
                inviter = i_uid
                break
        if not inviter and not link and INVITE_LOOSE_MATCH:
            # 宽松归因：Telegram 实测会漏掉 chat_join_request 的 invite_link 字段（申请明明点了专属链接）。
            # 申请/事件都没带链接时，若本群只有一条机器人专属链接，直接归因给它；多条则无法判定。
            cands = [i_uid for i_uid, info in invite_links.get(cid, {}).items()
                     if str(info.get("link", "")).startswith("http") and i_uid != uid]
            if len(cands) == 1:
                inviter = cands[0]
                link = f"宽松归因(唯一链接…{str(invite_links[cid][inviter].get('link',''))[-8:]})"
                _inv_dbg(cid, f"宽松归因命中：申请未带链接，本群唯一专属链接 → 邀请人 {inviter}")
            elif len(cands) > 1:
                _inv_dbg(cid, f"⚠️ 申请未带链接且本群有 {len(cands)} 条专属链接，宽松归因无法判定")
        if not inviter:
            if link:
                _inv_dbg(cid, f"⚠️ 归因失败：链接不在已存表（已存：{[i.get('link','')[-12:] for i in invite_links.get(cid, {}).values()]}）")
                if str(INVITE_INVALID_MSG).strip():
                    try:
                        await context.bot.send_message(chat_id=cid, text=_fmt_tpl("invite_invalid_msg", name=name))
                    except Exception:
                        pass
            else:
                _inv_dbg(cid, "⚠️ 归因失败：事件和申请都没带链接（普通群无法归因，需超级群）")
            return
        if inviter == uid:
            _inv_dbg(cid, f"uid={uid} 自己邀自己，跳过")
            if str(INVITE_SELF_MSG).strip():
                try:
                    await context.bot.send_message(chat_id=cid, text=_fmt_tpl("invite_self_msg", name=name))
                except Exception:
                    pass
            return
        _inv_dbg(cid, f"✅ 归因成功 uid={uid} → 邀请人 {inviter}")
        rec = {"cid": cid, "inviter": inviter, "invitee": uid, "invitee_name": name,
               "ts": now_bj().strftime("%Y-%m-%d %H:%M"), "audit": "ok", "left": False,
               "award": 0, "link": link}
        unmet = await _invite_pre_reasons(cid, uid, cmu)
        if unmet:
            rec["audit"], rec["note"] = "unmet", "、".join(unmet)
        elif INVITE_AUDIT_ENABLED:
            rec["audit"] = "pending"
        invite_records[key] = rec
        if rec["audit"] == "ok":
            await _invite_award(context.application, rec)
        save_data()
    except Exception:
        logger.exception("邀请追踪异常（已吞并）")


def _invite_rank_rows(scope):
    """按 scope（today/month/all）算邀请排行，返回 [(rank, uid, count)]（前 10）。"""
    today = now_bj().strftime("%Y-%m-%d")
    month = today[:7]
    counts = defaultdict(int)
    for rec in invite_records.values():
        if rec.get("audit") != "ok" or rec.get("left"):
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
    if not INVITE_ENABLED:
        await send_reply(update, context, "❌ 邀请系统未开启（网页「群组设置 → 邀请系统」可开启）。"); return
    if INVITE_RANK_ADMIN_ONLY and not is_bot_admin(update.effective_user.id):
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
    """获取本群专属邀请链接：/link，新朋友通过链接进群即计邀请。"""
    if not await need_auth(update, context): return
    if not is_group_chat(update):
        await send_reply(update, context, "⚠️ 请在群聊中使用。"); return
    if not INVITE_ENABLED:
        await send_reply(update, context, "❌ 邀请系统未开启（网页「群组设置 → 邀请系统」可开启）。"); return
    cid = update.effective_chat.id
    uid = update.effective_user.id
    mine = invite_links.get(cid, {}).get(uid)
    if not mine:
        link_obj, last_err = None, None
        for kw in ({"name": f"inv{uid}", "creates_join_request": True},
                   {"creates_join_request": True},
                   {}):   # 逐级回退：带名字+入群审核 → 仅入群审核 → 普通链接
            try:
                link_obj = await context.bot.create_chat_invite_link(chat_id=cid, **kw)
                break
            except Exception as e:
                last_err = e
        if not link_obj:
            await send_reply(update, context,
                             f"❌ 创建邀请链接失败：{last_err!r}\n请确认机器人是本群管理员，且管理员权限里勾选了「邀请用户（通过链接）」")
            return
        invite_links.setdefault(cid, {})[uid] = {"link": link_obj.invite_link,
                                                 "invite_id": link_obj.invite_link.rsplit("/", 1)[-1],
                                                 "ts": now_bj().strftime("%Y-%m-%d %H:%M")}
        _inv_dbg(cid, f"创建专属链接 inviter={uid}：…{link_obj.invite_link[-12:]}")
        save_data()
        mine = invite_links[cid][uid]
    total = _invite_count(uid, cid)
    my_name = await get_name(context.application, uid, cid=cid)
    cname = getattr(update.effective_chat, "title", "") or "本群"
    link = mine.get("link", "")
    text = (
        f"<b>🎟️ 我的专属邀请链接</b>\n"
        f"<b>邀请人</b>　{html.escape(my_name)} <code>{uid}</code>\n"
        f"<b>群组</b>　　{html.escape(cname)}\n"
        f"<b>已邀请</b>　{total} 人（每成功 +{INVITE_REWARD} 分）\n\n"
        f"<b>你的专属链接</b>\n"
        f"<code>{link}</code>\n\n"
        f"📋 <b>使用说明</b>\n"
        f"1. 把链接发给好友\n"
        f"2. 好友点链接 → 申请加入\n"
        f"3. 管理员批准 → 自动到账 +{INVITE_REWARD} 积分\n"
        f"4. 退群自动失效，奖励已发不追回"
    )
    await send_reply(update, context, text)


async def cmd_invite_test(update, context):
    """邀请归因预演（管理员）：只读模拟，不改任何数据、不发奖励。
    演示两种真实场景会归因给谁：①事件带链接 ②事件漏链接(Telegram 常见)→宽松归因。
    用于定位「进人不加分」到底是事件源断了，还是归因判定断了。"""
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
        cands = [i_uid for i_uid, info in invite_links.get(cid, {}).items()
                 if str(info.get("link", "")).startswith("http") and i_uid != fake_uid]
        if len(cands) == 1:
            return cands[0], "宽松归因命中：事件漏链接，本群恰只有一条专属链接"
        if len(cands) > 1:
            return 0, f"⚠️ 宽松归因失效：本群有 {len(cands)} 条专属链接，事件漏链接时无法判定"
        return 0, "⚠️ 事件漏链接且本群没有专属链接，无从归因"

    L = ["🧪 邀请归因预演（只读，不改数据）", "━━━━━━━━━━━━━━━━━"]
    L.append(f"你的专属链接：…{link[-12:]}")
    L.append(f"本群专属链接数（含你的）：{n_links + 1} 条")
    L.append("")
    L.append("<b>场景① 事件带链接</b>（Telegram 正常提供时）")
    a, b = _judge(link)
    L.append(f"　→ 归因：{'✅ ' + str(a) if a else '❌ 失败'}")
    L.append(f"　　{b}")
    L.append("")
    L.append("<b>场景② 事件漏链接</b>（Telegram 对部分 bot 不提供 invite_link）")
    c_, d = _judge("")
    L.append(f"　→ 归因：{'✅ ' + str(c_) if c_ else '❌ 失败'}")
    L.append(f"　　{d}")
    L.append("")
    L.append("判定失败 ≠ 系统坏了：先发 /邀请调试 看 bot 是不是管理员、有没有真进群事件。")
    await send_reply(update, context, "\n".join(L))


async def on_new_members_msg(update, context):
    """message 版入群事件（普通群收不到 chat_member 更新，只能靠服务消息兜底）。
    普通群的服务消息不带邀请链接，能归因到就走 pending 映射，归因不到就静默跳过。"""
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
    except Exception:
        logger.exception("message 入群事件处理异常（已吞并）")


async def on_member_event(update, context):
    """成员进出事件：退群/入群记录（bot 需为群管理员才能收到）。"""
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
        elif new.status in ("member", "administrator") and old.status in ("left", "kicked"):
            leave_records[cid].append({"ts": ts, "uid": uid, "name": name, "join": True})
            leave_records[cid] = leave_records[cid][-100:]
            member_joined_at[cid][uid] = time.time()  # 观察期起点
            _inv_dbg(cid, f"chat_member 进群事件 uid={uid}，事件链接：{(getattr(getattr(cmu, 'invite_link', None), 'link', '') or '（无）')}")
            await _invite_track_join(cmu, cid, uid, name, context)  # 邀请系统追踪（内部自吞异常）
            if WELCOME_ENABLED:
                try:
                    text = WELCOME_TPL.replace("{name}", name).replace("{group}", getattr(cmu.chat, "title", "") or "").replace("{id}", str(uid))
                    await context.bot.send_message(chat_id=cid, text=text)
                except TelegramError: pass
        _remember_name(update)
        save_data()
    except Exception:
        logger.exception("成员事件处理异常（已吞并）")

async def on_join_request(update, context):
    """入群申请：记录 + 存归因链接 + **自动批准**（bot 为管理员时秒批，人进群→service 事件→归因→发奖全自动）。"""
    try:
        req = update.chat_join_request
        if not req:
            return
        cid = req.chat.id
        _inv_dbg(cid, f"[req] on_join_request 触发 cid={cid}")
        uid, name = req.from_user.id, req.from_user.first_name or f"用户{req.from_user.id}"
        join_requests[cid].append({"ts": now_bj().strftime("%Y-%m-%d %H:%M"), "uid": uid, "name": name})
        join_requests[cid] = join_requests[cid][-100:]
        if getattr(req, "invite_link", None) and getattr(req.invite_link, "link", ""):
            invite_pending[f"{cid}:{uid}"] = req.invite_link.link   # 邀请归因兜底：批准后的 join 事件可能不带链接
            _inv_dbg(cid, f"入群申请 uid={uid}，已存待归因链接 …{req.invite_link.link[-12:]}")
        else:
            _inv_dbg(cid, f"入群申请 uid={uid}，⚠️ 申请未携带链接")
        save_data()
        # 自动批准：不批准人永远进不了群，归因/发奖链路就断在这（此前靠管理员去 Telegram 手动点，没人点=数据一直空）
        if INVITE_AUTO_APPROVE and is_auth(cid) and uid not in BLACKLISTED_USERS:
            try:
                await context.bot.approve_chat_join_request(cid, uid)
                _inv_dbg(cid, f"✅ 已自动批准 uid={uid}（{name}），等进群事件触发归因发奖")
            except TelegramError as exc:
                _inv_dbg(cid, f"⚠️ 自动批准 uid={uid} 失败：{exc}（bot 需为群管理员且有人审批权限；可去 Telegram 手动批准）")
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
        rh, rm = parse_hm(DAILY_RESET_TIME, 0, 0)  # 每轮重读，网页改时间即时生效
        target = now.replace(hour=rh, minute=rm, second=1, microsecond=0)
        if target <= now: target += timedelta(days=1)
        await asyncio.sleep((target-now).total_seconds())
        if not DAILY_RESET_ENABLED:  # 后台「定时任务」开关：关闭期间到点不执行
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
                for cid in target_groups:  # 只重置作用群
                    users = season_points.get(cid)
                    if not users: continue
                    for uid in list(users.keys()):
                        if (cid, uid) in season_protected:
                            continue  # 进行中排位局跳过，等结算补重置
                        day_profit = users[uid] - SEASON_START_CHIPS
                        if day_profit:
                            season_profit_by_date[day_key][cid][uid] += day_profit
                        users[uid] = SEASON_START_CHIPS
                save_data()
            for cid in target_groups:
                if cid in race_daily_stats: race_daily_stats[cid] = [0] * HORSE_COUNT
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
        now = now_bj()
        lh, lm = parse_hm(LEADERBOARD_TIME, 23, 50)  # 每轮重读，网页改时间即时生效
        target = now.replace(hour=lh, minute=lm, second=0, microsecond=0)
        if target <= now: target += timedelta(days=1)
        await asyncio.sleep((target-now).total_seconds())
        if not LEADERBOARD_ENABLED:  # 后台「定时任务」开关：关闭期间到点不推送
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
                lines = [f"🏆 德州当日排行榜（{date}）", "━"*14]
                for i, (uid, amount) in enumerate(sorted(data.items(), key=lambda x:x[1], reverse=True)[:50], 1): lines.append(f"{rank_marker(i)} {await get_name(app, uid)}：{amount:+d}")
                await safe_send_long(app.bot, cid, "\n".join(lines))
            # 排位赛每日 23:50 推送「当日分数」（每人每天从 2W 起始，当日分即当前分）
            if season_active:
                for cid in list(season_points.keys()):
                    if cid not in target_groups: continue  # 只推目标群
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
        rh, rm = parse_hm(ADMIN_REPORT_TIME, 9, 0)
        target = now.replace(hour=rh, minute=rm, second=0, microsecond=0)
        if target <= now: target += timedelta(days=1)
        await asyncio.sleep(max(1, (target - now).total_seconds()))
        if not ADMIN_REPORT_ENABLED:  # 后台「定时任务」开关：关闭期间到点不推送
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
    if not (RACE_AUTO_ENABLED and RACE_ENABLED
            and now.minute == max(0, min(59, RACE_HOURLY_MINUTE))
            and max(0, min(23, RACE_HOURLY_START)) <= now.hour <= max(0, min(23, RACE_HOURLY_END))):
        return
    for cid in list(AUTHORIZED_GROUPS):
        if not hourly_race_enabled.get(cid, True):
            race_skip_stats[cid]["群开关关闭"] += 1; continue
        if cid in active_horse_races:
            race_skip_stats[cid]["已有进行中赛车"] += 1; continue
        try:
            mode = current_game_mode()
            jackpot = race_jackpot.get(cid, 0) if mode == "official" else 0
            race = HorseRace(cid, ADMIN_USER_ID, jackpot, mode); active_horse_races[cid] = race
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
                if RACE_AUTO_ENABLED and now.minute == max(0, min(59, RACE_HOURLY_MINUTE)):
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
    lines.append(f"<b>1️⃣ 整点自动赛车</b>　总开关：{'✅ 开' if RACE_AUTO_ENABLED and RACE_ENABLED else '❌ 关'}　时段：{RACE_HOURLY_START:02d}:00–{RACE_HOURLY_END:02d}:59　开赛分钟：{RACE_HOURLY_MINUTE:02d} 分")
    if AUTHORIZED_GROUPS:
        for cid in sorted(AUTHORIZED_GROUPS):
            on = "✅" if hourly_race_enabled.get(cid, True) else "⏸"
            last = race_last_sent.get(cid) or "（暂无记录）"
            skips = race_skip_stats.get(cid, {})
            skip_txt = ""
            if skips:
                items = ", ".join(f"{k}×{v}" for k, v in skips.items())
                skip_txt = f"　跳过：{items}"
            lines.append(f"　{on} <code>{cid}</code> {html.escape(chat_name_cache.get(cid, '?'))}　最近推送：{last}{skip_txt}")
    else:
        lines.append("　（无授权群）")
    lines.append("")

    # 2) 每日重置
    lines.append(f"<b>2️⃣ 每日重置</b>　时刻：{DAILY_RESET_TIME}　上次业务日：{last_business_date or '（未记录）'}")
    lines.append("")

    # 3) 自动备份
    jq = getattr(context.application, "job_queue", None)
    if jq is not None:
        lines.append(f"<b>3️⃣ 自动备份</b>　间隔：{BACKUP_INTERVAL_HOURS} 小时　job_queue：✅ 运行中")
    else:
        lines.append(f"<b>3️⃣ 自动备份</b>　间隔：{BACKUP_INTERVAL_HOURS} 小时　job_queue：❌ 未启用（需 python-telegram-bot[job-queue]）")
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
                                     data.get("web_password") or globals().get("_web_password", ""),
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
                                     embedded.get("web_password") or globals().get("_web_password", ""),
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
    ("start", "开始 / 菜单 / 帮助"), ("dz", "德州扑克"), ("sc", "赛车"), ("21", "21点"), ("mylv", "我的等级"), ("jifen", "积分兑换"),
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
    global _bot_app, _bot_loop
    _bot_app, _bot_loop = app, asyncio.get_running_loop()  # 供网页后台跨线程调用 bot API（入群批准/拒绝等）
    background_tasks.update({
        asyncio.create_task(daily_reset_scheduler(app)),
        asyncio.create_task(leaderboard_scheduler(app)),
        asyncio.create_task(season_settle_scheduler(app)),
        asyncio.create_task(hourly_race_scheduler(app)),
        asyncio.create_task(admin_report_scheduler(app)),
        asyncio.create_task(lottery_scheduler(app)),
        asyncio.create_task(data_save_worker())
    })
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
    "adminlist": cmd_admin_list,
    "备份": cmd_backup,
    "恢复": cmd_restore,
    "炸金花": cmd_jinhua, "jinhua": cmd_jinhua, "zjh": cmd_jinhua, "金花": cmd_jinhua,
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
    if POINTS_DELETE_SECONDS > 0 and handler is not cmd_lottery and is_group_chat(update):
        schedule_delete(context.application, update.effective_chat.id, update.message, POINTS_DELETE_SECONDS)
    await handler(update, context)


async def route_command(update, context):
    """把 /中文 或 /英文 命令路由到对应处理函数。"""
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
                        subs.append(f"<a class='{pcls}' href='/page/{gkey}'>⚙️ {name}设置</a>")
                    for skey, sname in subpage_subs:
                        cls = "active" if sidebar_active == f"{gkey}/{skey}" else ""
                        subs.append(f"<a class='{cls}' href='/page/{gkey}/{skey}'>{sname}</a>")
                    for ck, (cname, cicon) in child_groups:
                        ccls = "active" if sidebar_active == ck or sidebar_active.startswith(ck + "/") else ""
                        subs.append(f"<a class='{ccls}' href='/page/{ck}'>{cname}</a>")
                    items.append(
                        f"<details{' open' if active_now else ''}>"
                        f"<summary class='{'active' if active_now else ''}'>{icon}<span>{name}</span></summary>"
                        f"<div class='sub'>{''.join(subs)}</div></details>")
                else:
                    cls = "item active" if active_now else "item"
                    items.append(f"<a class='{cls}' href='/page/{gkey}'>{icon}<span>{name}</span></a>")

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
                    "*{box-sizing:border-box}"
                    "html,body{height:100%}"
                    "body{background:#1c1d2e;color:#e6e5f0;font-family:system-ui,'PingFang SC','Microsoft YaHei',sans-serif;"
                    "margin:0;font-size:14px;-webkit-font-smoothing:antialiased}"
                    "a{color:inherit;text-decoration:none}"
                    "code{font-family:ui-monospace,Consolas,monospace;font-size:13px;color:#d6d2f5;"
                    "background:#151621;padding:1px 6px;border-radius:6px}"
                    # 顶部 header
                    ".hd{position:sticky;top:0;z-index:50;height:52px;background:#151621;"
                    "border-bottom:1px solid #26273a;display:flex;align-items:center;padding:0 18px;gap:14px}"
                    ".hd .logo{font-size:15px;font-weight:500;color:#fff;display:flex;align-items:center;gap:8px}"
                    ".hd .crumb{color:#8a89a0;font-size:13px}"
                    ".hd .right{margin-left:auto;display:flex;align-items:center;gap:14px;color:#8a89a0;font-size:12px}"
                    ".hd .burger{display:none;background:transparent;border:1px solid #2b2c40;color:#e6e5f0;"
                    "border-radius:8px;padding:6px 10px;cursor:pointer}"
                    # 整体布局
                    ".wrap{display:flex;min-height:calc(100vh - 52px)}"
                    # 侧栏
                    ".side{width:224px;background:#151621;border-right:1px solid #26273a;padding:14px 10px;"
                    "flex-shrink:0;overflow-y:auto;transition:transform .2s ease}"
                    ".side .grp-title{padding:14px 12px 6px;font-size:11px;color:#6a6982;letter-spacing:1px;"
                    "text-transform:uppercase;font-weight:500}"
                    ".side .grp-title:first-child{padding-top:4px}"
                    ".side a{display:flex;align-items:center;gap:10px;color:#a9a8bd;font-size:14px;"
                    "padding:9px 12px;border-radius:8px;margin-bottom:1px;transition:background .12s,color .12s}"
                    ".side a:hover{background:#1d1e2e;color:#fff}"
                    ".side a.active{background:linear-gradient(135deg,#7c6cf0 0%,#5d4dd6 100%);color:#fff;"
                    "box-shadow:0 4px 12px rgba(124,108,240,.25)}"
                    ".side a.active .badge{background:rgba(255,255,255,.18);color:#fff}"
                    ".side details{margin-bottom:1px}"
                    ".side summary{list-style:none;cursor:pointer;display:flex;align-items:center;gap:10px;"
                    "font-size:14px;color:#a9a8bd;padding:9px 12px;border-radius:8px;user-select:none;"
                    "transition:background .12s,color .12s}"
                    ".side summary::-webkit-details-marker{display:none}"
                    ".side summary:hover{background:#1d1e2e;color:#fff}"
                    ".side summary.active{background:#2b2854;color:#fff}"
                    ".side summary::after{content:'⌄';margin-left:auto;color:#6a6982;font-size:11px;transition:transform .15s}"
                    ".side details[open] summary::after{transform:rotate(180deg)}"
                    ".side .sub a{padding:7px 12px 7px 36px;font-size:13px;position:relative}"
                    ".side .sub a::before{content:'○';position:absolute;left:18px;font-size:8px;color:#6a6982}"
                    ".side .sub a.active::before{content:'●';color:#fff}"
                    ".badge{margin-left:auto;font-size:10px;background:#2b2c40;color:#a9a8bd;"
                    "border-radius:6px;padding:1px 6px;font-weight:500}"
                    # 主区
                    ".main{flex:1;padding:24px 28px;max-width:920px;min-width:0}"
                    ".main h1{font-size:20px;font-weight:500;margin:0 0 4px;color:#fff}"
                    ".main h1 .ico{margin-right:6px}"
                    ".main .sub{font-size:13px;color:#8a89a0;margin-bottom:18px}"
                    # 卡片
                    ".card{background:#1d1e2e;border:1px solid #2b2c40;border-radius:12px;padding:20px 22px;margin-bottom:16px}"
                    ".card h3{font-size:14px;font-weight:500;margin:0 0 12px;color:#c9c8da}"
                    # 表单
                    "label{display:block;font-size:13px;color:#a9a8bd;margin:14px 0 5px}"
                    "input,select,textarea{width:100%;background:#151621;border:1px solid #2b2c40;color:#e6e5f0;"
                    "border-radius:8px;padding:9px 12px;font-size:14px;font-family:inherit;transition:border-color .12s}"
                    "input:focus,select:focus,textarea:focus{outline:none;border-color:#7c6cf0;"
                    "box-shadow:0 0 0 3px rgba(124,108,240,.12)}"
                    "textarea{font-family:ui-monospace,Consolas,monospace;line-height:1.5}"
                    "button{background:linear-gradient(135deg,#7c6cf0 0%,#5d4dd6 100%);color:#fff;border:none;"
                    "border-radius:8px;padding:9px 22px;font-size:14px;cursor:pointer;font-weight:500;"
                    "transition:transform .1s,box-shadow .12s;box-shadow:0 2px 8px rgba(124,108,240,.2)}"
                    "button:hover{transform:translateY(-1px);box-shadow:0 4px 14px rgba(124,108,240,.35)}"
                    "button:active{transform:translateY(0)}"
                    "button.danger{background:linear-gradient(135deg,#e06666 0%,#b94545 100%);"
                    "box-shadow:0 2px 8px rgba(224,102,102,.2)}"
                    # 提示
                    ".ok{color:#6fd08c;font-size:13px;padding:10px 14px;background:rgba(111,208,140,.08);"
                    "border:1px solid rgba(111,208,140,.2);border-radius:8px;margin-bottom:14px}"
                    ".err{color:#f09595;font-size:13px;padding:10px 14px;background:rgba(240,149,149,.08);"
                    "border:1px solid rgba(240,149,149,.2);border-radius:8px;margin-bottom:14px}"
                    # 统计卡片
                    ".cards{display:grid;grid-template-columns:repeat(auto-fill,minmax(170px,1fr));gap:14px}"
                    ".stat{background:linear-gradient(135deg,#1d1e2e 0%,#232438 100%);border:1px solid #2b2c40;"
                    "border-radius:12px;padding:16px 18px;transition:transform .15s,border-color .15s}"
                    ".stat:hover{transform:translateY(-2px);border-color:#3a3b5a}"
                    ".stat .v{font-size:24px;font-weight:500;margin-top:6px;color:#fff}"
                    ".stat .t{font-size:12px;color:#8a89a0;display:flex;align-items:center;gap:6px}"
                    # 快捷入口
                    ".q{display:inline-flex;align-items:center;gap:5px;margin:5px 5px 0 0;background:#2b2854;color:#d6d2f5;"
                    "font-size:13px;padding:8px 13px;border-radius:8px;transition:background .12s,color .12s}"
                    ".q:hover{background:#7c6cf0;color:#fff}"
                    # 行
                    ".row{display:flex;align-items:center;justify-content:space-between;gap:16px;"
                    "padding:12px 0;border-bottom:1px solid #26273a}"
                    ".row:last-child{border-bottom:none}"
                    ".row .lbl{font-size:14px;color:#d6d2f5;flex:1;min-width:0}"
                    ".row .lbl small{display:block;color:#8a89a0;font-size:12px;margin-top:2px;font-weight:400}"
                    ".row input[type=number],.row input[type=text],.row select{width:240px;flex-shrink:0}"
                    ".row textarea{width:100%;margin-top:8px}"
                    # 开关
                    ".tg{position:relative;width:44px;height:24px;flex-shrink:0}"
                    ".tg input{opacity:0;width:0;height:0;position:absolute}"
                    ".tg .sl{position:absolute;inset:0;background:#34354a;border-radius:24px;transition:.2s;cursor:pointer}"
                    ".tg .sl:before{content:'';position:absolute;width:18px;height:18px;left:3px;top:3px;"
                    "background:#fff;border-radius:50%;transition:.2s}"
                    ".tg input:checked+.sl{background:#7c6cf0}"
                    ".tg input:checked+.sl:before{transform:translateX(20px)}"
                    # 表格
                    ".tbl{width:100%;border-collapse:collapse;font-size:13px;margin-top:6px}"
                    ".tbl td,.tbl th{padding:9px 8px;border-bottom:1px solid #26273a;text-align:left}"
                    ".tbl th{color:#8a89a0;font-weight:500;font-size:12px}"
                    ".tbl tr:last-child td{border-bottom:none}"
                    ".tbl tr:hover td{background:rgba(124,108,240,.04)}"
                    # 内部表单行（季节/授权等用 div 套 input 而不是 .row）
                    "[style*='padding:13px 2px']{padding:12px 0 !important;border-bottom:1px solid #26273a !important}"
                    # footer
                    ".ft{padding:16px 28px;text-align:center;color:#6a6982;font-size:12px;border-top:1px solid #26273a}"
                    ".ft a{color:#7c6cf0}"
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
                    "::-webkit-scrollbar-thumb{background:#2b2c40;border-radius:4px}"
                    "::-webkit-scrollbar-thumb:hover{background:#3a3b5a}"
                    "</style></head><body>"
                    # 顶部 header
                    "<header class='hd'>"
                    "<button class='burger' onclick=\"document.querySelector('.side').classList.toggle('open');"
                    "document.querySelector('.backdrop').classList.toggle('show')\" aria-label='菜单'>☰</button>"
                    f"<div class='logo'>🤖 机器人后台</div>"
                    f"<div class='crumb'>· {html.escape(title)}</div>"
                    "<div class='right'>机器人后台</div>"
                    "</header>"
                    "<div class='backdrop' onclick=\"document.querySelector('.side').classList.remove('open');"
                    "this.classList.remove('show')\"></div>"
                    "<div class='wrap'>"
                    f"<nav class='side'>{''.join(items)}</nav>"
                    f"<main class='main'>{body}</main>{_id_picker_js()}</div>"
                    "<footer class='ft'>© 机器人后台</footer>"
                    "</body></html>").encode("utf-8")

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
            return ("<script>var GUSERS=" + json.dumps(gusers, ensure_ascii=False) + ";"
                    "document.addEventListener('DOMContentLoaded',function(){"
                    "function fill(){document.querySelectorAll('select[data-users-for]').forEach(function(sel){"
                    "var dl=document.getElementById(sel.getAttribute('data-users-for'));if(!dl)return;"
                    "var us=GUSERS[sel.value]||{};"
                    "dl.innerHTML=Object.keys(us).map(function(u){return '<option value=\"'+u+'\">'+us[u]+'</option>';}).join('');});}"
                    "document.querySelectorAll('select[data-users-for]').forEach(function(sel){sel.addEventListener('change',fill);});fill();});</script>")

        def _otp_page(otp_token, err="", notice=""):
            """二次验证页：密码已通过，等 Telegram 私聊发来的 6 位验证码。"""
            msg = f"<div class='err'>{html.escape(err)}</div>" if err else ""
            msg += f"<div class='ok'>{html.escape(notice)}</div>" if notice else ""
            return ("<!DOCTYPE html><html lang='zh'><head><meta charset='utf-8'>"
                    "<meta name='viewport' content='width=device-width, initial-scale=1'>"
                    "<title>二次验证 - 机器人后台</title><style>"
                    "*{box-sizing:border-box}html,body{height:100%}"
                    "body{background:linear-gradient(135deg,#1c1d2e 0%,#151621 100%);color:#e6e5f0;"
                    "font-family:system-ui,'PingFang SC','Microsoft YaHei',sans-serif;margin:0;display:flex;"
                    "align-items:center;justify-content:center;padding:20px;min-height:100vh}"
                    ".login{background:#1d1e2e;border:1px solid #2b2c40;border-radius:14px;padding:32px;"
                    "width:min(380px,100%);box-shadow:0 20px 60px rgba(0,0,0,.4)}"
                    ".login h1{font-size:20px;font-weight:500;margin:0 0 4px;text-align:center;color:#fff}"
                    ".login .desc{font-size:12px;color:#8a89a0;text-align:center;margin-bottom:24px;line-height:1.6}"
                    ".login label{display:block;font-size:13px;color:#a9a8bd;margin:14px 0 6px}"
                    ".login input{width:100%;background:#151621;border:1px solid #2b2c40;color:#e6e5f0;"
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
                    ".login .resend button{background:transparent;border:1px solid #2b2c40;color:#a9a8bd;"
                    "box-shadow:none;font-size:13px;padding:8px 16px;margin-top:0}"
                    ".login .ft{padding:14px 0 0;margin-top:20px;border-top:1px solid #26273a;font-size:11px;"
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
            return ("<!DOCTYPE html><html lang='zh'><head><meta charset='utf-8'>"
                    "<meta name='viewport' content='width=device-width, initial-scale=1'>"
                    "<title>登录 - 机器人后台</title><style>"
                    "*{box-sizing:border-box}"
                    "html,body{height:100%}"
                    "body{background:linear-gradient(135deg,#1c1d2e 0%,#151621 100%);color:#e6e5f0;"
                    "font-family:system-ui,'PingFang SC','Microsoft YaHei',sans-serif;margin:0;display:flex;"
                    "align-items:center;justify-content:center;padding:20px;min-height:100vh}"
                    ".login{background:#1d1e2e;border:1px solid #2b2c40;border-radius:14px;padding:32px;"
                    "width:min(380px,100%);box-shadow:0 20px 60px rgba(0,0,0,.4)}"
                    ".login h1{font-size:20px;font-weight:500;margin:0 0 4px;text-align:center;color:#fff}"
                    ".login .desc{font-size:12px;color:#8a89a0;text-align:center;margin-bottom:24px}"
                    ".login label{display:block;font-size:13px;color:#a9a8bd;margin:14px 0 6px}"
                    ".login input{width:100%;background:#151621;border:1px solid #2b2c40;color:#e6e5f0;"
                    "border-radius:8px;padding:11px 14px;font-size:14px;transition:border-color .12s}"
                    ".login input:focus{outline:none;border-color:#7c6cf0;box-shadow:0 0 0 3px rgba(124,108,240,.12)}"
                    ".login button{width:100%;background:linear-gradient(135deg,#7c6cf0 0%,#5d4dd6 100%);"
                    "color:#fff;border:none;border-radius:8px;padding:12px;font-size:15px;cursor:pointer;"
                    "font-weight:500;margin-top:22px;transition:transform .1s,box-shadow .12s;"
                    "box-shadow:0 4px 14px rgba(124,108,240,.3)}"
                    ".login button:hover{transform:translateY(-1px);box-shadow:0 6px 20px rgba(124,108,240,.45)}"
                    ".login .err{color:#f09595;font-size:13px;padding:10px 14px;background:rgba(240,149,149,.08);"
                    "border:1px solid rgba(240,149,149,.2);border-radius:8px;margin-bottom:14px;text-align:center}"
                    ".login .ft{padding:14px 0 0;margin-top:20px;border-top:1px solid #26273a;font-size:11px;"
                    "color:#6a6982;text-align:center}"
                    "</style></head><body><div class='login'>"
                    "<h1>🤖 机器人后台</h1>"
                    "<div class='desc'>管理员登录</div>" + msg +
                    "<form method='post' action='/login'>"
                    "<label>管理密码</label><input type='password' name='password' autofocus required>"
                    "<button type='submit'>登 录</button></form>"
                    "<div class='ft'>💡 推荐：Telegram 发 <b>/后台</b>，点链接免密登录（密码为备用通道）<br>© 机器人后台</div>"
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
                stat("🏆 赛季", season_txt, f"ID {season_id}" if season_id else "")
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
                                if r.get("cid") == cid and r.get("audit") == "ok"
                                and not r.get("left") and str(r.get("ts", "")).startswith(today))
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
                              "border-bottom:1px solid #26273a'>"
                              f"<span style='flex:1'>{i} {n}</span>"
                              f"<a href='/menu_move/{k}/-1' style='padding:2px 10px;background:#26273a;"
                              "border-radius:6px;font-size:12px'>▲ 上移</a>"
                              f"<a href='/menu_move/{k}/1' style='padding:2px 10px;background:#26273a;"
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
                            f"<button type='submit' style='padding:2px 10px;cursor:pointer;background:{color};color:#fff;border:none;border-radius:6px'>{label}</button></form>")
                rows_html = ""
                for x in members[(page - 1) * per: page * per]:
                    in_wl = x["uid"] in whitelist.get(sel_cid, set())
                    rows_html += ("<tr><td>" + html.escape(x["name"]) + "</td>"
                                  f"<td><code>{x['uid']}</code></td>"
                                  f"<td>{x['joined_txt']}</td>"
                                  f"<td>{x['last']}</td>"
                                  f"<td>{x['chips']}</td>"
                                  f"<td>{x['warn']}</td>"
                                  "<td>" + _mb("warn_add", x["uid"], "＋", "#3d6b4f") + " " + _mb("warn_sub", x["uid"], "－") + "</td>"
                                  "<td>" + (_mb("wl_del", x["uid"], "删白", "#8a6d3b") if in_wl else _mb("wl_add", x["uid"], "✅ 加白", "#3d6b4f")) + " "
                                  + _mb("ban", x["uid"], "⛔ 封禁", "#8a3b3b") + " "
                                  + _mb("kick", x["uid"], "👋 踢出", "#8a3b3b") + "</td></tr>")
                if not rows_html:
                    rows_html = f"<tr><td colspan='8' style='text-align:center;color:#6a6982'>{'左侧选一个群后展示成员' if not sel_cid else '该群暂无成员档案（发过言/进过群才会建档）'}</td></tr>"
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
                        f"<div class='card' style='margin-top:18px'><div class='sub'>共 {total} 条记录 · 第 {page}/{pages} 页</div>"
                        "<table class='tbl'><tr><th>昵称</th><th>用户ID</th><th>进群时间</th><th>最近发言</th><th>积分</th><th>警告</th><th>警告操作</th><th>操作</th></tr>"
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
                            "<button type='submit'>💾 保 存</button></form></div>")
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
                            "<div class='sub'>授权群里的玩家才能使用游戏；也可在群里发 /授权</div>{msg}"
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
                            "<div class='sub'>被拉黑的玩家无法使用机器人任何功能；也可群里 /拉黑 /解黑</div>{msg}"
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
                            "<div class='sub'>给玩家加/减排位分（正加负减）；赛季未开始时需玩家已在赛季名单</div>{msg}"
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
                              "<button type='submit' style='margin-top:10px'>💾 保存阈值</button></form></div>")
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
                body = (f"<h1>{gicon} 命令管理</h1>"
                        "<div class='sub'>每个命令的触发词随意改（逗号分隔，可中文可英文）；保存后<b>立即生效</b>并持久化。"
                        "Telegram / 菜单每行一条「命令 描述」，命令仅限英文小写/数字/下划线</div>{msg}{err}"
                        "<div class='card'><form method='post' action='/cmdaliases'>"
                        "<h3>⌨️ 命令触发词</h3>"
                        "<table class='tbl'><tr><th style='width:150px'>命令</th><th>触发词（逗号分隔）</th></tr>"
                        + "".join(rows) + "</table>"
                        "<h3 style='margin-top:20px'>📱 Telegram / 菜单</h3>"
                        "<textarea name='tg_menu' rows='14' style='width:100%;font-family:inherit'>" + html.escape(menu_txt) + "</textarea>"
                        "<button type='submit' style='margin-top:12px'>💾 保存全部命令设置</button></form></div>")
            elif gkey == "security":
                is_default = _web_password == WEB_DEFAULT_PASSWORD
                warn = "<div class='err'>⚠️ 当前还在用初始密码，建议立即修改（至少4位）</div>" if is_default else ""
                body = (f"<h1>{gicon} {gname}</h1><div class='sub'>修改后台登录密码</div>{msg}{warn}"
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
                               if not LOTTERY_ENABLED else "")
                body = (f"<h1>{gicon} {sname}</h1>"
                        f"<div class='sub'>在这里创建抽奖 → 机器人自动发到群里 → 群成员发「{html.escape(LOTTERY_KEYWORD)}」参与 → 到点自动开奖</div>"
                        f"{msg}{err}{status_html}" +
                        # 新增抽奖表单（照阿福格式：描述/关键词/开奖方式下拉/结构化奖品行）
                        "<div class='card'><h3>➕ 新增抽奖</h3>"
                        "<form method='post' action='/lottery_create' id='lottery_form'>"
                        "<div class='row'><div class='lbl'>发到哪个群 *</div>"
                        f"<select name='cid' required>{_group_options()}</select></div>"
                        "<div class='row'><div class='lbl'>抽奖标题 *</div>"
                        "<input type='text' name='title' maxlength='50' required placeholder='例：群友福利'></div>"
                        "<div style='padding:12px 0;border-bottom:1px solid #26273a'>"
                        "<div class='lbl'>抽奖描述<small>（可选）显示在公告标题下方</small></div>"
                        "<textarea name='desc' rows='2' placeholder='活动说明、注意事项等（可留空）'></textarea></div>"
                        "<div class='row'><div class='lbl'>参与关键词 *</div>"
                        f"<input type='text' name='keyword' maxlength='20' value='{html.escape(LOTTERY_KEYWORD)}' placeholder='群友发这个词参与抽奖'></div>"
                        "<div class='row'><div class='lbl'>开奖方式 *</div>"
                        "<select name='mode' id='mode_sel'>"
                        "<option value='time'>定时开奖</option>"
                        "<option value='duration'>倒计时开奖</option></select></div>"
                        "<div class='row' id='row_time'><div class='lbl'>开奖时间 *<small>输入的时间将按北京时间解析执行：20:00 / 09-08 20:00 / 2026-09-08 20:00</small></div>"
                        "<input type='text' name='endtime' id='endtime' placeholder='例：21:30 或 09-08 20:00'></div>"
                        "<div class='row' id='row_duration' style='display:none'><div class='lbl'>持续秒数 *<small>到点自动开奖（10 ~ 604800）</small></div>"
                        f"<input type='number' name='duration' id='duration' value='{max(10, int(LOTTERY_DEFAULT_DURATION))}' min='10'></div>"
                        "<div style='padding:12px 0;border-bottom:1px solid #26273a'>"
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
                        f"<input type='hidden' name='group' value='points/lottery'>"
                        + _field_rows("lottery")
                        + "<div class='sub' style='margin-top:16px'>消息模板支持占位符："
                          f"<code>{'{title}'}</code> <code>{'{nick}'}</code> <code>{'{n}'}</code> <code>{'{balance}'}</code> "
                          f"<code>{'{prize_list}'}</code> <code>{'{keyword}'}</code> <code>{'{duration}'}</code> "
                          f"<code>{'{winners}'}</code> <code>{'{reason}'}</code></div>"
                        "<button type='submit' style='margin-top:8px'>💾 保存全部抽奖设置</button></form></div>")
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
                    warn_html = ("<div class='err'>⚠️ 邀请系统当前已关闭</div>" if not INVITE_ENABLED else "")
                    body = (f"<h1>{gicon} {gname}</h1>"
                            f"<div class='sub'>群里发「<code>{html.escape(str(INVITE_LINK_CMD))}</code>」领专属邀请链接 → 新朋友经链接进群 → 邀请人得奖励"
                            f"（群内发「{html.escape(str(INVITE_RANK_ALL_CMD))}」看排行）</div>{msg}{warn_html}"
                            "<div class='card'><h3>🎟️ 使用说明</h3>"
                            "<div class='sub'>链接经 Telegram 官方 invite_link 事件追踪，进群即记账；被邀请人退群自动失效不计排行；"
                            "开启人工审核后进群只入册不发奖，到「审核」子页一键通过/拒绝</div></div>"
                            "<div class='card' style='margin-top:18px'><form method='post' action='/save'>"
                            "<input type='hidden' name='group' value='invite/config'>"
                            + _field_rows("invite/config") +
                            "<div class='sub' style='margin-top:16px'>模板占位符：邀请成功通知 <code>{inviter}</code> <code>{invitee}</code> <code>{reward}</code>；"
                            "链接消息 <code>{link}</code> <code>{reward}</code>；排行行 <code>{i}</code> <code>{name}</code> <code>{count}</code></div>"
                            "<button type='submit' style='margin-top:8px'>💾 保存邀请设置</button></form></div>")
                elif sub == "records":
                    _recs = [(k, r) for k, r in invite_records.items()
                             if not sel_icid or _inv_icid(r.get("cid")) == sel_icid]
                    rows_html = ""
                    for k, r in sorted(_recs, key=lambda kv: kv[1].get("ts", ""), reverse=True)[:100]:
                        audit_badge = {"ok": "<span style='color:#6fd08c'>有效</span>",
                                       "pending": "<span style='color:#f0c060'>待审核</span>",
                                       "unmet": "<span style='color:#f09595'>未满足</span>",
                                       "rejected": "<span style='color:#8a89a0'>已拒绝</span>"}.get(r.get("audit", ""), r.get("audit", ""))
                        if r.get("left"):
                            audit_badge += " <span style='color:#8a89a0'>(已退群)</span>"
                        rows_html += (f"<tr><td><code>{k}</code></td>"
                                      f"<td><code>{r.get('inviter', '')}</code></td>"
                                      f"<td><code>{r.get('invitee', '')}</code> {html.escape(str(r.get('invitee_name', '')))}</td>"
                                      f"<td>{r.get('ts', '')}</td><td>{audit_badge}</td>"
                                      f"<td>{r.get('award', 0)}</td>"
                                      f"<td><a class='q' href='/invite_del/{k}' onclick=\"return confirm('删除该邀请记录？')\">🗑 删除</a></td></tr>")
                    if not rows_html:
                        rows_html = "<tr><td colspan='7' style='text-align:center;color:#6a6982'>暂无邀请记录</td></tr>"
                    body = (f"<h1>{gicon} 邀请记录</h1><div class='sub'>最近 100 条邀请记录；退群自动标失效（不计排行）</div>{msg}"
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
                        if r.get("audit") == "ok" and (not sel_icid or _inv_icid(r.get("cid")) == sel_icid):
                            daily_counts[str(r.get("ts", ""))[:10]] += 1
                    rows_html = "".join(f"<tr><td>{d}</td><td>{n}</td></tr>"
                                        for d, n in sorted(daily_counts.items(), reverse=True)[:60])
                    if not rows_html:
                        rows_html = "<tr><td colspan='2' style='text-align:center;color:#6a6982'>暂无数据</td></tr>"
                    body = (f"<h1>{gicon} 统计</h1><div class='sub'>每日有效邀请数（最近 60 天）</div>{msg}"
                            "<div class='card'>" + _inv_bar("/page/invite/daily") +
                            "<table class='tbl'><tr><th>日期</th><th>有效邀请</th></tr>"
                            + rows_html + "</table></div>")
                elif sub == "summary":
                    sums = defaultdict(lambda: {"ok": 0, "award": 0})
                    for r in invite_records.values():
                        if r.get("audit") == "ok" and not r.get("left") and (not sel_icid or _inv_icid(r.get("cid")) == sel_icid):
                            sums[r.get("inviter")]["ok"] += 1
                            sums[r.get("inviter")]["award"] += int(r.get("award", 0) or 0)
                    rows_html = ""
                    for uid, s in sorted(sums.items(), key=lambda kv: -kv[1]["ok"])[:50]:
                        rows_html += (f"<tr><td><code>{uid}</code> {html.escape(user_names.get(uid, ''))}</td>"
                                      f"<td>{s['ok']}</td><td>{s['award']}</td></tr>")
                    if not rows_html:
                        rows_html = "<tr><td colspan='3' style='text-align:center;color:#6a6982'>暂无数据</td></tr>"
                    body = (f"<h1>{gicon} 汇总</h1><div class='sub'>按邀请人汇总（有效且未退群，前 50）</div>{msg}"
                            "<div class='card'>" + _inv_bar("/page/invite/summary") +
                            "<table class='tbl'><tr><th>邀请人</th><th>有效邀请</th><th>累计奖励</th></tr>"
                            + rows_html + "</table></div>")
                elif sub == "pre":
                    body = (f"<h1>{gicon} 前置条件</h1>"
                            f"<div class='sub'>被邀请人进群时需满足的条件；不满足记「未满足」且不发奖（防小号白嫖邀请奖励）</div>{msg}"
                            "<div class='card'><form method='post' action='/save'>"
                            "<input type='hidden' name='group' value='invite/pre'>"
                            + _field_rows("invite/pre") +
                            "<button type='submit' style='margin-top:8px'>💾 保存前置条件</button></form></div>")
                elif sub == "audit":
                    pend = {k: r for k, r in invite_records.items()
                            if r.get("audit") in ("pending", "unmet") and (not sel_icid or _inv_icid(r.get("cid")) == sel_icid)}
                    rows_html = ""
                    for k, r in sorted(pend.items(), key=lambda kv: kv[1].get("ts", ""), reverse=True):
                        tag = "待审核" if r.get("audit") == "pending" else f"未满足（{html.escape(str(r.get('note', '')))}）"
                        rows_html += (f"<tr><td><code>{k}</code></td>"
                                      f"<td><code>{r.get('inviter', '')}</code></td>"
                                      f"<td><code>{r.get('invitee', '')}</code> {html.escape(str(r.get('invitee_name', '')))}</td>"
                                      f"<td>{r.get('ts', '')}</td><td>{tag}</td>"
                                      f"<td><form style='display:inline;margin:0' method='post' action='/invite_audit'>"
                                      f"<input type='hidden' name='op' value='approve'><input type='hidden' name='sel' value='{k}'>"
                                      f"<button style='padding:2px 10px;cursor:pointer;background:#3d6b4f;color:#fff;border:none;border-radius:6px'>✅ 通过</button></form> "
                                      f"<form style='display:inline;margin:0' method='post' action='/invite_audit'>"
                                      f"<input type='hidden' name='op' value='reject'><input type='hidden' name='sel' value='{k}'>"
                                      f"<button style='padding:2px 10px;cursor:pointer;background:#8a3b3b;color:#fff;border:none;border-radius:6px'>❌ 拒绝</button></form></td></tr>")
                    if not rows_html:
                        rows_html = "<tr><td colspan='6' style='text-align:center;color:#6a6982'>暂无待审核记录</td></tr>"
                    body = (f"<h1>{gicon} 审核</h1><div class='sub'>开启「新邀请需人工审核」后，进群邀请在此通过/拒绝；"
                            f"「审核通过后补发奖励」开关决定通过时是否补发 {INVITE_REWARD} 积分</div>{msg}"
                            "<div class='card'>" + _inv_bar("/page/invite/audit") +
                            "<table class='tbl'><tr><th>记录ID</th><th>邀请人</th><th>被邀请人</th><th>时间</th><th>状态</th><th>操作</th></tr>"
                            + rows_html + "</table></div>")
                else:
                    body = f"<h1>{gicon} {gname}</h1><div class='sub'>该子页暂未开通</div>{msg}"
            elif sub:
                # 子页面制（照阿福模板：积分相关 → 积分设置/每日签到/…）
                subs = {k: n for k, n in SUBPAGES.get(gkey, [])}
                sname = subs.get(sub, sub)
                if gkey == "points" and sub == "adjust":
                    body = (f"<h1>{gicon} {sname}</h1>"
                            "<div class='sub'>直接给玩家加/减统一积分（正数加、负数减），立即生效并落盘；等效群里的 /add 命令</div>{msg}"
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
                            "<div class='sub'>按群导出/导入积分。导入会<b>覆盖</b>该群已有积分，务必先用模板核对格式</div>{msg}{err}"
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
                            "<button type='submit'>✅ 确认导入</button></form></div>")
                elif gkey == "points" and sub == "level":
                    lv_rows = "".join(
                        f"<tr><td>{html.escape(str(x.get('name', '?')))}</td><td>{int(x.get('value', 0) or 0)}</td>"
                        f"<td><a href='/level_del/{i}' style='color:#f09595'>删除</a></td></tr>"
                        for i, x in enumerate(POINT_LEVELS))
                    if not lv_rows:
                        lv_rows = ("<tr><td colspan='3' style='text-align:center;color:#6a6982'>"
                                   "暂无等级数据，先新增等级</td></tr>")
                    body = (f"<h1>{gicon} {sname}</h1><div class='sub'>积分达到最低积分即获得该等级；升降级自动群内通知（下方可开关）。保存立即生效</div>{msg}"
                            "<div class='card'><h3>🎖 等级列表（按最低积分升序）</h3>"
                            "<table class='tbl'><tr><th>等级名称</th><th>最低积分</th><th>操作</th></tr>"
                            + lv_rows + "</table>"
                            "<form method='post' action='/level_add' style='display:flex;gap:10px;margin-top:12px'>"
                            "<input type='text' name='name' placeholder='等级名称(≤12字)' required maxlength='12' style='flex:2'>"
                            "<input type='number' name='value' placeholder='最低积分' required min='0' style='flex:1'>"
                            "<button style='margin:0'>➕ 新增等级</button></form></div>"
                            "<div class='card' style='margin-top:18px'><form method='post' action='/save'>"
                            "<input type='hidden' name='group' value='points/level'>"
                            + _field_rows("points/level")
                            + "<div class='sub' style='margin-top:16px'>占位符：<code>{name}</code> <code>{level}</code> <code>{balance}</code>；群内发「"
                              + html.escape(str(LEVEL_CMD)) + "」查询自己的等级</div>"
                            "<button type='submit' style='margin-top:8px'>💾 保存通知设置</button></form></div>")
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
                            + _field_rows("points/mall") + "<button type='submit'>💾 保存商城设置</button></form></div>")
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
                            + "）</td></tr>"
                            f"<tr><th>转赠</th><td>{'开启' if INHERIT_ENABLED else '关闭'}，把积分转给群内成员{fee}</td></tr>"
                            "<tr><th>等级</th><td>"
                            + " ≥ ".join(f"{x['name']} {x['value']}分" for x in POINT_LEVELS) + "</td></tr>"
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
                              "防伪单号由系统自动生成，只发用户私聊和管理员对账（群里不显示，防群友看到别人单号冒领），无需模板配置</div>"
                            "<button type='submit' style='margin-top:8px'>💾 保存兑换设置</button></form></div>")
                elif gkey == "points" and sub == "guess":
                    gs_rows = ""
                    for gc, g in sorted(guesses.items()):
                        locked = bool(g.get("locked"))
                        st = "<span style='color:#e0b040'>已封盘</span>" if locked else "<span style='color:#6fd08c'>下注中</span>"
                        gs_rows += (f"<tr><td>{gc} {html.escape(chat_name_cache.get(gc, ''))}</td>"
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
                            "到点自动封盘，「竞猜结算 A/B」开出答案后猜中方按注额比例瓜分全部奖池，「竞猜撤销」全额退款</div>{msg}"
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
                            "<input type='number' name='duration' placeholder='时长(分钟,默认" + str(GUESS_DURATION) + ")' min='1' max='1440' style='flex:1;min-width:120px'>"
                            "<button style='margin:0'>🎯 发起竞猜</button></form></div>"
                            "<div class='card' style='margin-top:18px'><form method='post' action='/save'>"
                            "<input type='hidden' name='group' value='points/guess'>"
                            + _field_rows("points/guess")
                            + "<button type='submit' style='margin-top:8px'>💾 保存竞猜设置</button></form></div>")
                elif gkey == "points" and sub == "mallord":
                    _ord_src = [o for o in reversed(mall_orders[-200:]) if not sel_flt_cid or int(o.get("cid", 0) or 0) == sel_flt_cid]
                    ord_rows = "".join(
                        f"<tr><td>{html.escape(str(o.get('ts', '')))}</td><td>{o.get('cid')} {html.escape(chat_name_cache.get(int(o.get('cid', 0) or 0), ''))}</td>"
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
                        f"<tr><td><code>{oid}</code></td><td>{o.get('cid')} {html.escape(chat_name_cache.get(int(o.get('cid', 0) or 0), ''))}</td>"
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
                            + _field_rows("points/buy") + "<button type='submit'>💾 保存</button></form></div>")
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
                form_open = "<div class='card'>"
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
                                       ("经营日报推送", ADMIN_REPORT_ENABLED)):
                        _rows += ("<div style='display:flex;justify-content:space-between;padding:7px 2px;"
                                  "border-bottom:1px solid #26273a'><span>" + _name + "</span>" + _badge(_on) + "</div>")
                    # 整点赛车每群推送明细：一眼看出哪个群没收到 + 网页直接开关每群
                    _race_rows = ""
                    for _cid in sorted(AUTHORIZED_GROUPS):
                        _on = bool(hourly_race_enabled.get(_cid, True))
                        _badge = "<span style='color:#6fd08c'>✅ 开</span>" if _on else "<span style='color:#8a89a0'>⏸ 关</span>"
                        _last = race_last_sent.get(_cid) or "（暂无）"
                        _tg = "<a href='/racegrp/" + str(_cid) + "/toggle' style='margin-left:8px'>" + ("关闭" if _on else "开启") + "</a>"
                        _race_rows += ("<tr><td>" + _badge + " <code>" + str(_cid) + "</code> " + html.escape(chat_name_cache.get(_cid, '?')) + _tg + "</td>"
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
                            _tg_txt = "<br>".join(f"<code>{c}</code> {html.escape(chat_name_cache.get(c, '?'))}" for c in _tg)
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
                body = (f"<h1>{gicon} {gname}</h1><div class='sub'>保存立即生效，无需重启</div>{msg}"
                        + form_open +
                        "<form method='post' action='/save'>"
                        f"<input type='hidden' name='group' value='{gkey}'>"
                        + _field_rows(gkey) +
                        "<button type='submit'>💾 保 存</button></form></div>")
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
                        ip = self.client_address[0]
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
                        if act == "del" or kind == "level":  # 等级无启停，level 路径一律视为删除（防呆）
                            lst.pop(idx)
                        else:
                            lst[idx]["on"] = not lst[idx].get("on", True)
                        save_settings({})
                    self._redirect(back); return
                mm = re.fullmatch(r"/racegrp/(-?\d+)/toggle", path)
                if mm:  # 网页直接开/关某群整点自动赛车
                    rcid = int(mm.group(1))
                    if rcid in AUTHORIZED_GROUPS:
                        hourly_race_enabled[rcid] = not hourly_race_enabled.get(rcid, True)
                        save_data()
                    self._redirect("/page/schedule"); return
                # 4 个调度任务的作用对象切换：/sch_<task>_toggle/<id>
                mm = re.fullmatch(r"/sch_(dailyreset|leaderboard)_toggle/(-?\d+)", path)
                if mm:
                    task, rid = mm.group(1), int(mm.group(2))
                    target = daily_reset_groups if task == "dailyreset" else leaderboard_groups
                    if rid in AUTHORIZED_GROUPS:
                        if rid in target: target.discard(rid)
                        else: target.add(rid)
                        save_settings({})
                    self._redirect("/page/schedule"); return
                mm = re.fullmatch(r"/sch_(backup|report)_admins_toggle/(-?\d+)", path)
                if mm:
                    task, rid = mm.group(1), int(mm.group(2))
                    target = backup_admins if task == "backup" else admin_report_admins
                    if rid in target: target.discard(rid)
                    else: target.add(rid)
                    save_settings({})
                    self._redirect("/page/schedule"); return
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
                if path == "/login":
                    ip = self.client_address[0]
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
                    if secrets.compare_digest(pwd, _web_password):
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
                    ip = self.client_address[0]
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
                        AUTHORIZED_GROUPS.add(cid_); save_data(); _back(note=f"✅ 已授权群 {cid_}")
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
                    dur_ = form.get("duration", [""])[0] or GUESS_DURATION
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
                if path == "/invite_audit":
                    # 邀请审核：approve（可补发奖励）/ reject
                    op = form.get("op", [""])[0]
                    sel = form.get("sel", [""])[0]
                    rec = invite_records.get(sel)
                    if rec and op in ("approve", "reject"):
                        if op == "approve" and rec.get("audit") in ("pending", "unmet"):
                            rec["audit"] = "ok"
                            if INVITE_AUDIT_AWARD and not rec.get("award") and _bot_app and _bot_loop:
                                async def _ia(app=_bot_app, r=rec):
                                    await _invite_award(app, r)
                                try:
                                    asyncio.run_coroutine_threadsafe(_ia(), _bot_loop).result(20)
                                except Exception:
                                    logger.exception("邀请审核补发奖励失败")
                        elif op == "reject":
                            rec["audit"] = "rejected"
                        save_data()
                    self._redirect("/page/invite/audit"); return
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
                if path == "/level_add":
                    def _ilv(k, dflt=0):
                        try: return int(form.get(k, [str(dflt)])[0] or dflt)
                        except ValueError: return dflt
                    name = (form.get("name", [""])[0] or "").strip()[:12]
                    if name and not any(ch in name for ch in "<>&"):
                        POINT_LEVELS.append({"name": name, "value": max(0, _ilv("value"))})
                        POINT_LEVELS.sort(key=lambda x: x["value"])
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
                        "fee": int(LOTTERY_FEE), "keyword": fields["keyword"],
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
    """定时把数据文件发给配置的目标管理员私聊，当作云端持久化备份。

    无持久磁盘的平台容器重启会清空磁盘，有这份备份就能用 /restore 恢复，
    最坏只丢一个备份周期（30 分钟）的积分变动。
    """
    if not BACKUP_ENABLED:  # 后台「定时任务」开关：关了就不备份，保存即时生效
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
        app.job_queue.run_repeating(auto_backup, interval=max(1, int(BACKUP_INTERVAL_HOURS)) * 3600, first=60)
        logger.info("自动备份任务已注册：每 %s 小时一次", BACKUP_INTERVAL_HOURS)
    else:
        logger.warning("JobQueue 不可用，自动备份未启用（需安装 python-telegram-bot[job-queue]）")

    app.add_handler(MessageHandler(filters.TEXT & filters.Regex(r'^/'), route_command))
    app.add_handler(CallbackQueryHandler(on_button)); app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND & ~filters.Regex(r'^/'), on_text))
    app.add_handler(MessageHandler(~filters.TEXT & ~filters.COMMAND, on_media))  # 自动删除规则中心：媒体类
    # 关键：chat_member_types 必须显式传 ANY_CHAT_MEMBER（默认 -1=MY_CHAT_MEMBER 只听 bot 自身状态变化，
    # 普通新成员入群/退群触发的 chat_member 更新会被静默丢弃，调试里"最近事件"无埋点）
    app.add_handler(ChatMemberHandler(on_member_event, chat_member_types=ChatMemberHandler.ANY_CHAT_MEMBER))
    app.add_handler(MessageHandler(filters.StatusUpdate.NEW_CHAT_MEMBERS, on_new_members_msg))  # 普通群入群兜底
    app.add_handler(ChatJoinRequestHandler(on_join_request))  # 入群申请事件（群需开「申请加入」）
    app.run_polling(allowed_updates=Update.ALL_TYPES, drop_pending_updates=True)

if __name__ == "__main__": main()
