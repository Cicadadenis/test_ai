import os
import io
from io import BytesIO
import json
import time
import re
import hashlib
import sqlite3
import base64
import getpass
import httpx
import sys
import asyncio
import logging
import tempfile
import zipfile
import atexit
from cryptography.fernet import Fernet
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC
from groq import Groq
from gtts import gTTS
from datetime import datetime, timedelta
from dotenv import load_dotenv
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.constants import ParseMode
from telegram.ext import (
    Application, CommandHandler, MessageHandler,
    CallbackQueryHandler, filters, ContextTypes
)

TAVILY_API = "https://api.tavily.com/search"

# ════════════════════════════════════════════════════
#  ЛОГИРОВАНИЕ
# ════════════════════════════════════════════════════
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('cicada.log', encoding='utf-8'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)
logging.getLogger("httpx").setLevel(logging.WARNING)

# ════════════════════════════════════════════════════
#  ЗАШИФРОВАННАЯ БД — движок (оптимальная схема)
#  Шифрование: AES-GCM через Fernet (cryptography)
#  БД в RAM (':memory:') + автосохранение каждые 60 сек
#  Debounce: 10 сек минимум между флагами сохранения
#  Кнопки: 💾 Скачать БД | 💾 Сохранить БД (форс)
# ════════════════════════════════════════════════════
DB_ENC_FILE = "cicada.db.enc"   # зашифрованный контейнер
_db_connection: sqlite3.Connection = None
_fernet: Fernet = None
_last_save_time: float = 0
_SAVE_INTERVAL: int = 60   # 60 сек между автосохранениями
_PENDING_SAVE: bool = False  # флаг: нужно ли сохранение
_DEBOUNCE_INTERVAL: int = 10  # минимум 10 сек между флагами сохранения
_SESSION_PASSWORD: str = ""   # пароль текущей сессии


def _derive_key(password: str, salt: bytes = None) -> tuple:
    """PBKDF2 ключ из пароля. Возвращает (ключ, соль)."""
    if salt is None:
        salt = os.urandom(16)
    kdf = PBKDF2HMAC(
        algorithm=hashes.SHA256(),
        length=32,
        salt=salt,
        iterations=100000,
    )
    key = base64.urlsafe_b64encode(kdf.derive(password.encode()))
    return key, salt


def _get_fernet(password: str, salt: bytes = None) -> tuple:
    """Создаёт Fernet из пароля."""
    key, salt = _derive_key(password, salt)
    return Fernet(key), salt


def _encrypt_data(data: bytes, password: str) -> bytes:
    """AES-GCM шифрование через Fernet + соль."""
    fernet, salt = _get_fernet(password)
    encrypted = fernet.encrypt(data)
    # salt (16 bytes) + encrypted
    return salt + encrypted


def _decrypt_data(data: bytes, password: str) -> bytes | None:
    """Расшифровка. Возвращает None если пароль неверный."""
    if len(data) < 16:
        return None
    salt = data[:16]
    encrypted = data[16:]
    try:
        fernet, _ = _get_fernet(password, salt)
        return fernet.decrypt(encrypted)
    except Exception:
        return None


def encrypt_db_to_disk(password: str) -> bool:
    """Сохраняем RAM-БД на диск в зашифрованном виде."""
    global _db_connection, _last_save_time
    if _db_connection is None:
        return False
    
    try:
        # Получаем дамп через iterdump
        dump = '\n'.join(_db_connection.iterdump())
        data = dump.encode('utf-8')
        
        # Шифруем и сохраняем
        encrypted = _encrypt_data(data, password)
        with open(DB_ENC_FILE, "wb") as f:
            f.write(encrypted)
        
        _last_save_time = time.time()
        logger.info(f"БД сохранена на диск, размер: {len(encrypted)} bytes")
        return True
    except Exception as e:
        logger.error(f"Ошибка сохранения БД: {e}")
        return False


def decrypt_db_to_ram(password: str) -> bool:
    """Загружаем БД из файла в RAM."""
    global _db_connection, _fernet
    
    # Создаём Fernet для сессии
    try:
        _fernet, _ = _get_fernet(password)
    except Exception as e:
        logger.error(f"Ошибка создания ключа: {e}")
        return False
    
    # Подключение к RAM
    _db_connection = sqlite3.connect(':memory:', check_same_thread=False)
    _db_connection.row_factory = sqlite3.Row
    
    if not os.path.exists(DB_ENC_FILE):
        logger.info("Первый запуск — создаём пустую БД в RAM")
        return True
    
    try:
        with open(DB_ENC_FILE, "rb") as f:
            encrypted = f.read()
        
        data = _decrypt_data(encrypted, password)
        if data is None:
            logger.error("Неверный пароль или поврежденные данные")
            return False
        
        # Восстанавливаем дамп
        dump = data.decode('utf-8')
        _db_connection.executescript(dump)
        logger.info(f"БД загружена из файла, размер дампа: {len(data)} bytes")
        return True
    except Exception as e:
        logger.error(f"Ошибка загрузки БД: {e}")
        return False


def get_db() -> sqlite3.Connection:
    """Получаем соединение с RAM-БД."""
    global _db_connection
    if _db_connection is None:
        raise RuntimeError("БД не инициализирована")
    return _db_connection


def save_if_needed(password: str):
    """Сохраняем на диск только если прошло время ИЛИ есть pending сохранение."""
    global _last_save_time, _PENDING_SAVE
    current_time = time.time()
    
    # Сохраняем если прошло время ИЛИ есть флаг форс-сохранения
    if (current_time - _last_save_time >= _SAVE_INTERVAL) or _PENDING_SAVE:
        if encrypt_db_to_disk(password):
            _PENDING_SAVE = False
            logger.info(f"💾 БД сохранена (размер: {os.path.getsize(DB_ENC_FILE) if os.path.exists(DB_ENC_FILE) else 0} bytes)")


def force_save(password: str) -> bool:
    """Принудительное сохранение прямо сейчас. Возвращает True при успехе."""
    result = encrypt_db_to_disk(password)
    if result:
        global _PENDING_SAVE
        _PENDING_SAVE = False
    return result


def request_save():
    """Пометить что нужно сохранить при следующей возможности (с debounce)."""
    global _PENDING_SAVE, _last_save_time
    current_time = time.time()
    
    # Debounce: не чаще чем раз в _DEBOUNCE_INTERVAL секунд
    time_since_last = current_time - _last_save_time
    
    if time_since_last < _DEBOUNCE_INTERVAL:
        # Минимум 10 секунд с последнего сохранения
        logger.debug(f"Debounce: пропуск, прошло только {time_since_last:.1f}с")
        return
    
    _PENDING_SAVE = True
    logger.debug(f"Запланировано сохранение (debounce: {time_since_last:.1f}с)")


def get_encrypted_db_bytes(password: str) -> bytes | None:
    """Возвращает зашифрованные данные БД для скачивания."""
    global _db_connection
    if _db_connection is None:
        return None
    
    try:
        # Дамп БД через iterdump
        dump = '\n'.join(_db_connection.iterdump())
        data = dump.encode('utf-8')
        
        # Шифруем
        encrypted = _encrypt_data(data, password)
        return encrypted
    except Exception as e:
        logger.error(f"Ошибка создания дампа: {e}")
        return None


def get_time_until_next_save() -> str:
    """Возвращает время до следующего автосохранения."""
    global _last_save_time
    current_time = time.time()
    elapsed = current_time - _last_save_time
    remaining = _SAVE_INTERVAL - elapsed
    
    if remaining <= 0:
        return "скоро..."
    
    hours = int(remaining // 3600)
    minutes = int((remaining % 3600) // 60)
    
    if hours > 0:
        return f"{hours}ч {minutes}м"
    else:
        return f"{minutes}м"


def _cleanup_on_exit():
    """Очистка при выходе — сохраняем БД."""
    global _db_connection
    if _db_connection is not None and _SESSION_PASSWORD:
        logger.info("Сохранение БД перед выходом...")
        encrypt_db_to_disk(_SESSION_PASSWORD)
        _db_connection.close()
        logger.info("БД закрыта")


atexit.register(_cleanup_on_exit)


# ════════════════════════════════════════════════════
#  ИНИЦИАЛИЗАЦИЯ СХЕМЫ БД
# ════════════════════════════════════════════════════
def init_db():
    conn = get_db()
    c = conn.cursor()

    c.executescript("""
    CREATE TABLE IF NOT EXISTS users (
        id              INTEGER PRIMARY KEY,
        username        TEXT    DEFAULT '',
        first_name      TEXT    DEFAULT '',
        user_limit      INTEGER DEFAULT 50000,
        used            INTEGER DEFAULT 0,
        banned          INTEGER DEFAULT 0,
        joined          TEXT    DEFAULT '',
        premium         INTEGER DEFAULT 0,
        premium_until   TEXT    DEFAULT NULL,
        is_trial        INTEGER DEFAULT 1,
        search_used     INTEGER DEFAULT 0,
        total_messages  INTEGER DEFAULT 0,      -- всего сообщений отправлено
        total_tokens    INTEGER DEFAULT 0,      -- всего токенов потрачено
        longest_chat    INTEGER DEFAULT 0,      -- самый длинный чат
        current_chat_id INTEGER DEFAULT 0       -- ID активного чата
    );

    CREATE TABLE IF NOT EXISTS histories (
        user_id     INTEGER NOT NULL,
        position    INTEGER NOT NULL,
        role        TEXT    NOT NULL,
        content     TEXT    NOT NULL,
        PRIMARY KEY (user_id, position)
    );

    CREATE TABLE IF NOT EXISTS invoices (
        invoice_id  INTEGER PRIMARY KEY,
        user_id     INTEGER NOT NULL,
        plan        TEXT    NOT NULL,
        chat_id     INTEGER NOT NULL,
        message_id  INTEGER NOT NULL,
        status      TEXT    DEFAULT 'pending'
    );

    CREATE TABLE IF NOT EXISTS config (
        key     TEXT PRIMARY KEY,
        value   TEXT NOT NULL
    );

    -- 🧠 МУЛЬТИ-ЧАТЫ: таблица чатов пользователя
    CREATE TABLE IF NOT EXISTS chats (
        chat_id         INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id         INTEGER NOT NULL,
        name            TEXT    DEFAULT 'Новый чат',
        created_at      TEXT    DEFAULT '',
        updated_at      TEXT    DEFAULT '',
        message_count   INTEGER DEFAULT 0,
        is_active       INTEGER DEFAULT 1,
        FOREIGN KEY (user_id) REFERENCES users(id)
    );

    -- ⚙️ НАСТРОЙКИ ПОЛЬЗОВАТЕЛЯ
    CREATE TABLE IF NOT EXISTS user_settings (
        user_id             INTEGER PRIMARY KEY,
        response_style      TEXT    DEFAULT 'detailed',  -- brief, detailed, expert
        bot_personality     TEXT    DEFAULT 'friendly',  -- strict, friendly, sarcastic
        auto_compress       INTEGER DEFAULT 1,           -- авто-сжатие истории
        notifications       INTEGER DEFAULT 1            -- уведомления вкл/выкл
    );

    -- 💳 ИСТОРИЯ ПЛАТЕЖЕЙ (завершённые)
    CREATE TABLE IF NOT EXISTS payments (
        payment_id      INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id         INTEGER NOT NULL,
        plan            TEXT    NOT NULL,
        amount          REAL    DEFAULT 0,
        currency        TEXT    DEFAULT 'USD',
        paid_at         TEXT    DEFAULT '',
        invoice_id      INTEGER DEFAULT 0,
        status          TEXT    DEFAULT 'completed',
        FOREIGN KEY (user_id) REFERENCES users(id)
    );

    -- 💬 СООБЩЕНИЯ ПО ЧАТАМ (для мульти-чатов)
    CREATE TABLE IF NOT EXISTS chat_messages (
        msg_id          INTEGER PRIMARY KEY AUTOINCREMENT,
        chat_id         INTEGER NOT NULL,
        user_id         INTEGER NOT NULL,
        role            TEXT    NOT NULL,  -- user, assistant, system
        content         TEXT    NOT NULL,
        created_at      TEXT    DEFAULT '',
        tokens_used     INTEGER DEFAULT 0,
        FOREIGN KEY (chat_id) REFERENCES chats(chat_id),
        FOREIGN KEY (user_id) REFERENCES users(id)
    );
    """)

    conn.commit()
    # conn is _db_connection (RAM), do not close


# ════════════════════════════════════════════════════
#  SETUP WIZARD — первый запуск
# ════════════════════════════════════════════════════
def run_setup():
    print("\n" + "═"*50)
    print("  🤖 Cicada-AI — Первый запуск. Настройка.")
    print("═"*50 + "\n")
    bot_token       = input("Введи Telegram Bot Token: ").strip()
    admin_id        = input("Введи Telegram ID администратора: ").strip()
    groq_token      = input("Введи Groq API Token: ").strip()
    cryptobot_token = input("Введи CryptoBot API Token (или Enter чтобы пропустить): ").strip()
    tavily_token    = input("Введи Tavily API Token для поиска (tavily.com, или Enter пропустить): ").strip()

    with open(".env", "w", encoding="utf-8") as f:
        f.write(f"BOT_TOKEN={bot_token}\n")
        f.write(f"ADMIN_ID={admin_id}\n")
        f.write(f"GROQ_TOKEN={groq_token}\n")
        f.write(f"CRYPTOBOT_TOKEN={cryptobot_token}\n")
        f.write(f"TAVILY_TOKEN={tavily_token}\n")

    print("\n✅ Токены сохранены в .env\n")


ENV_FILE = ".env"
if not os.path.exists(ENV_FILE):
    run_setup()

load_dotenv(ENV_FILE)

BOT_TOKEN        = os.getenv("BOT_TOKEN", "")
ADMIN_ID         = int(os.getenv("ADMIN_ID", "0"))

# ════════════════════════════════════════════════════
#  РЕЖИМ ТЕХНИЧЕСКИХ РАБОТ
# ════════════════════════════════════════════════════
MAINTENANCE_MODE: bool = False  # включается командой /maintenance on
GROQ_TOKEN       = os.getenv("GROQ_TOKEN", "")
GROQ_TOKEN_2     = os.getenv("GROQ_TOKEN_2", "")
GROQ_TOKEN_3     = os.getenv("GROQ_TOKEN_3", "")
CRYPTOBOT_TOKEN  = os.getenv("CRYPTOBOT_TOKEN", "")
TAVILY_TOKEN     = os.getenv("TAVILY_TOKEN", "")

if not BOT_TOKEN or not GROQ_TOKEN or not ADMIN_ID:
    print("❌ .env повреждён. Удали файл .env и перезапусти.")
    sys.exit(1)

CRYPTOBOT_API = "https://pay.crypt.bot/api"


# ════════════════════════════════════════════════════
#  ПАРОЛЬ ДЛЯ БД — запрашивается при каждом запуске
# ════════════════════════════════════════════════════
print("\n" + "═"*50)
print("  🔐 Cicada AI — Защита базы данных")
print("═"*50)

if not os.path.exists(DB_ENC_FILE):
    print("\n⚠️  Первый запуск — придумай пароль для базы данных.")
    print("    ЗАПОМНИ его — без него данные не восстановить!\n")
    while True:
        pwd1 = getpass.getpass("Новый пароль БД: ")
        pwd2 = getpass.getpass("Повтори пароль: ")
        if not pwd1:
            print("❌ Пароль не может быть пустым.")
        elif pwd1 != pwd2:
            print("❌ Пароли не совпадают.")
        else:
            _SESSION_PASSWORD = pwd1
            print("✅ Пароль установлен.\n")
            # Создаём новую БД в памяти
            _db_connection = sqlite3.connect(":memory:", check_same_thread=False)
            _db_connection.row_factory = sqlite3.Row
            break
else:
    print("\nВведи пароль для расшифровки базы данных.\n")
    attempts = 3
    _SESSION_PASSWORD = ""
    for attempt in range(attempts):
        pwd = getpass.getpass("Пароль БД: ")
        if decrypt_db_to_ram(pwd):
            _SESSION_PASSWORD = pwd
            print("✅ База данных загружена в память.\n")
            break
        else:
            left = attempts - attempt - 1
            if left > 0:
                print(f"❌ Неверный пароль. Осталось попыток: {left}")
            else:
                print("❌ Превышено число попыток. Завершение.")
                sys.exit(1)

# Инициализируем схему (если новая БД)
init_db()
# Сразу сохраняем на диск
force_save(_SESSION_PASSWORD)
logger.info("БД инициализирована и сохранена")


# ════════════════════════════════════════════════════
#  CONFIG — хранится в таблице config
# ════════════════════════════════════════════════════
DEFAULT_CONFIG = {
    "max_history_messages": "10",
    "max_file_chars": "4000",
    "cache_max_size": "200",
    "default_user_limit": "50000",  # лимит в символах
    "rate_limit_per_minute": "10",
    "summary_threshold": "16",
    "summary_keep_last": "4",
    "groq_model": "llama-3.1-8b-instant",
    "summary_model": "llama-3.1-8b-instant",
    "tts_lang": "ru",
    "tts_max_chars": "500",
    # Цены Premium (1/3/5/7 месяцев)
    "price_1month": "1.0",
    "price_3month": "3.0",
    "price_5month": "5.0",
    "price_7month": "7.0",
    # Legacy prices (для совместимости)
    "price_day":   "3.0",
    "price_week":  "5.0",
    "price_month": "10.0",
    "default_search_limit": "25",
    # Счётчики API запросов
    "groq_requests_total": "0",
    "tavily_requests_total": "0",
    "groq_requests_today": "0",
    "tavily_requests_today": "0",
    "counter_date": "",
    # Лимиты для уведомлений
    "groq_alert_threshold": "800",
    "tavily_alert_threshold": "800",
    "groq_alert_sent": "0",
    "tavily_alert_sent": "0",
}


def load_config() -> dict:
    conn = get_db()
    c = conn.cursor()
    c.execute("SELECT key, value FROM config")
    rows = {r["key"]: r["value"] for r in c.fetchall()}
    # conn is _db_connection (RAM), do not close
    # Заполняем отсутствующие ключи
    for k, v in DEFAULT_CONFIG.items():
        if k not in rows:
            rows[k] = v
            _config_set(k, v)
    return rows


def _config_set(key: str, value: str):
    conn = get_db()
    conn.execute(
        "INSERT INTO config (key, value) VALUES (?, ?) "
        "ON CONFLICT(key) DO UPDATE SET value=excluded.value",
        (key, str(value))
    )
    conn.commit()
    # conn is _db_connection (RAM), do not close
    request_save()


def save_config():
    for k, v in CFG.items():
        _config_set(k, str(v))


CFG = load_config()

# Приводим нужные поля к нужным типам
def cfg_int(key): return int(CFG[key])
def cfg_float(key): return float(CFG[key])


AVAILABLE_MODELS = [
    "llama-3.1-8b-instant",       # быстрый, 14.4К req/day
    "llama-3.3-70b-versatile",    # умный, 1К req/day
    "qwen/qwen3-32b",             # 60 req/min, хорош для кода
    "meta-llama/llama-4-scout-17b-16e-instruct",  # свежий, 1К req/day
]


# ════════════════════════════════════════════════════
#  СЧЁТЧИКИ API ЗАПРОСОВ
# ════════════════════════════════════════════════════
def _reset_daily_counters_if_needed():
    """Сбрасываем дневные счётчики если новый день."""
    today = datetime.now().strftime("%Y-%m-%d")
    if CFG.get("counter_date") != today:
        CFG["counter_date"] = today
        CFG["groq_requests_today"] = "0"
        CFG["tavily_requests_today"] = "0"
        CFG["groq_alert_sent"] = "0"
        CFG["tavily_alert_sent"] = "0"
        _config_set("counter_date", today)
        _config_set("groq_requests_today", "0")
        _config_set("tavily_requests_today", "0")
        _config_set("groq_alert_sent", "0")
        _config_set("tavily_alert_sent", "0")


def increment_groq_counter():
    """Увеличиваем счётчик запросов к Groq."""
    _reset_daily_counters_if_needed()
    total = int(CFG.get("groq_requests_total", "0")) + 1
    today = int(CFG.get("groq_requests_today", "0")) + 1
    CFG["groq_requests_total"] = str(total)
    CFG["groq_requests_today"] = str(today)
    _config_set("groq_requests_total", str(total))
    _config_set("groq_requests_today", str(today))
    return today, total


def increment_tavily_counter():
    """Увеличиваем счётчик запросов к Tavily."""
    _reset_daily_counters_if_needed()
    total = int(CFG.get("tavily_requests_total", "0")) + 1
    today = int(CFG.get("tavily_requests_today", "0")) + 1
    CFG["tavily_requests_total"] = str(total)
    CFG["tavily_requests_today"] = str(today)
    _config_set("tavily_requests_total", str(total))
    _config_set("tavily_requests_today", str(today))
    return today, total


# Глобальная переменная для отправки уведомлений
_bot_app = None


async def check_and_notify_limits(api_name: str, today_count: int, bot=None):
    """Проверяем лимит и отправляем уведомление если приближаемся."""
    if not bot:
        return
    threshold_key = f"{api_name}_alert_threshold"
    alert_sent_key = f"{api_name}_alert_sent"
    threshold = int(CFG.get(threshold_key, "800"))
    alert_sent = CFG.get(alert_sent_key, "0") == "1"

    if today_count >= threshold and not alert_sent:
        CFG[alert_sent_key] = "1"
        _config_set(alert_sent_key, "1")
        api_label = "Groq" if api_name == "groq" else "Tavily"
        try:
            await bot.send_message(
                chat_id=ADMIN_ID,
                text=(
                    f"⚠️ <b>ВНИМАНИЕ! Лимит {api_label} API</b>\n\n"
                    f"📊 Сегодня отправлено: <b>{today_count}</b> запросов\n"
                    f"🚨 Порог уведомления: <b>{threshold}</b>\n\n"
                    f"Рекомендую проверить лимиты на сайте {api_label}!\n"
                    f"Сменить токен можно в 🛡 Админ-панели → 🔑 Токены API"
                ),
                parse_mode=ParseMode.HTML,
            )
        except Exception as e:
            logger.error(f"Не удалось отправить уведомление: {e}")


# ════════════════════════════════════════════════════
#  GROQ CLIENT — ротация 3 ключей
# ════════════════════════════════════════════════════
_GROQ_KEYS = [k for k in [GROQ_TOKEN, GROQ_TOKEN_2, GROQ_TOKEN_3] if k]
_groq_key_index = 0
logger.info(f"🔑 Groq ключей загружено: {len(_GROQ_KEYS)} (GROQ_TOKEN={'✅' if GROQ_TOKEN else '❌'}, GROQ_TOKEN_2={'✅' if GROQ_TOKEN_2 else '❌'}, GROQ_TOKEN_3={'✅' if GROQ_TOKEN_3 else '❌'})")

def _get_groq_client() -> Groq:
    """Возвращает Groq клиент со следующим ключом по кругу."""
    global _groq_key_index
    key = _GROQ_KEYS[_groq_key_index % len(_GROQ_KEYS)]
    _groq_key_index += 1
    return Groq(api_key=key)

# Совместимость: client для мест где используется напрямую
client = Groq(api_key=GROQ_TOKEN)


# ════════════════════════════════════════════════════
#  ДИРЕКТОРИИ (только для временных файлов)
# ════════════════════════════════════════════════════
FILES_DIR = "user_files"
os.makedirs(FILES_DIR, exist_ok=True)


# ════════════════════════════════════════════════════
#  ВЕБ-ПОИСК — Tavily API
# ════════════════════════════════════════════════════
SEARCH_TRIGGERS = [
    "найди", "найти", "поищи", "поиск", "погода", "weather",
    "github", "гитхаб", "npm", "pypi", "курс", "цена", "price",
    "новости", "news", "что такое", "кто такой", "когда",
    "сколько стоит", "где скачать", "последняя версия",
    "актуальн", "сейчас", "сегодня", "текущ",
]

def needs_web_search(text: str) -> bool:
    """Эвристика: нужен ли веб-поиск для этого запроса."""
    if not TAVILY_TOKEN:
        return False
    t = text.lower()
    return any(trigger in t for trigger in SEARCH_TRIGGERS)


# ════════════════════════════════════════════════════
#  ЛОКАЛЬНАЯ МОДЕЛЬ — Qwen Coder через Ollama
# ════════════════════════════════════════════════════
OLLAMA_URL = "http://127.0.0.1:11434/api/chat"
OLLAMA_MODEL = "qwen2.5-coder:1.5b"

CODE_TRIGGERS = [
    # русские
    "код", "кода", "функци", "класс", "метод", "скрипт", "алгоритм",
    "программ", "отладь", "исправь", "рефактор", "напиши функцию",
    "напиши класс", "напиши скрипт", "напиши код", "отрефактор",
    "баг", "ошибк", "дебаг", "регулярн", "список", "массив",
    "словарь", "цикл", "рекурси", "сортировк", "парс", "запрос",
    "декоратор", "генератор", "асинхрон",
    # языки
    "python", "javascript", "typescript", "java", "golang", "rust",
    "c++", "c#", "php", "sql", "bash", "shell", "html", "css",
    "async", "await", "api", "regex",
    # английские
    "function", "class", "method", "script", "algorithm", "debug",
    "refactor", "fix the", "fix this", "write a", "implement",
    "optimize", "snippet", "loop", "array", "dict",
    "variable", "module", "import", "library", "package",
]


def needs_local_model(text: str) -> bool:
    """Нужна ли локальная coder-модель (только если не веб-поиск)."""
    if needs_web_search(text):
        return False  # веб-поиск приоритетнее
    t = text.lower()
    return any(trigger in t for trigger in CODE_TRIGGERS)


async def call_ollama(api_messages: list) -> str | None:
    """Вызов Ollama (qwen2.5-coder:3b). Возвращает None если недоступен."""
    try:
        async with httpx.AsyncClient(timeout=120) as http:
            resp = await http.post(
                OLLAMA_URL,
                json={
                    "model": OLLAMA_MODEL,
                    "messages": api_messages,
                    "stream": False,
                    "options": {"temperature": 0.2, "num_predict": 4096},
                },
            )
            data = resp.json()
            return data["message"]["content"].strip()
    except Exception as e:
        logger.warning(f"Ollama недоступна, fallback на Groq: {e}")
        return None

async def web_search(query: str, max_results: int = 5, bot=None) -> str:
    """Поиск через Tavily. Возвращает форматированный текст с результатами."""
    if not TAVILY_TOKEN:
        return ""
    try:
        async with httpx.AsyncClient(timeout=10) as http:
            resp = await http.post(
                TAVILY_API,
                json={
                    "api_key":      TAVILY_TOKEN,
                    "query":        query,
                    "max_results":  max_results,
                    "include_answer": True,
                    "search_depth": "basic",
                },
            )
        data = resp.json()
    except Exception as e:
        return f"[Поиск недоступен: {e}]"

    # Увеличиваем счётчик Tavily
    today_count, _ = increment_tavily_counter()
    if bot:
        asyncio.create_task(check_and_notify_limits("tavily", today_count, bot))

    parts = []
    # Краткий ответ от Tavily (если есть)
    if data.get("answer"):
        parts.append(f"📌 Краткий ответ: {data['answer']}")

    # Результаты
    results = data.get("results", [])
    for i, r in enumerate(results[:max_results], 1):
        title   = r.get("title", "")
        url     = r.get("url", "")
        snippet = r.get("content", "")[:300].replace("\n", " ")
        parts.append(f"{i}. **{title}**\n   {snippet}\n   🔗 {url}")

    return "\n\n".join(parts) if parts else "[Поиск не дал результатов]"



# ════════════════════════════════════════════════════
#  БАЗА ПОЛЬЗОВАТЕЛЕЙ — SQLite
# ════════════════════════════════════════════════════
def get_user(user_id: int) -> dict:
    conn = get_db()
    c = conn.cursor()
    c.execute("SELECT * FROM users WHERE id=?", (user_id,))
    row = c.fetchone()
    if row is None:
        now = datetime.now().strftime("%Y-%m-%d %H:%M")
        conn.execute(
            "INSERT INTO users (id, joined, user_limit) VALUES (?, ?, ?)",
            (user_id, now, cfg_int("default_user_limit"))
        )
        conn.commit()
        c.execute("SELECT * FROM users WHERE id=?", (user_id,))
        row = c.fetchone()
        # conn is _db_connection (RAM), do not close
        request_save()  # отметить для сохранения
    else:
        pass  # conn is _db_connection (RAM), do not close
    return dict(row)


def update_user(user_id: int, **kwargs):
    if not kwargs:
        return
    get_user(user_id)  # создаём если нет
    # Маппинг: "limit" → "user_limit" (SQLite)
    col_map = {"limit": "user_limit"}
    sets = []
    vals = []
    for k, v in kwargs.items():
        col = col_map.get(k, k)
        sets.append(f"{col}=?")
        # bool → int
        vals.append(int(v) if isinstance(v, bool) else v)
    vals.append(user_id)
    conn = get_db()
    conn.execute(f"UPDATE users SET {', '.join(sets)} WHERE id=?", vals)
    conn.commit()
    # conn is _db_connection (RAM), do not close
    request_save()  # отметить для сохранения


def load_users() -> dict:
    """Возвращает словарь всех пользователей {str(id): dict}."""
    conn = get_db()
    c = conn.cursor()
    c.execute("SELECT * FROM users")
    rows = c.fetchall()
    # conn is _db_connection (RAM), do not close
    result = {}
    for r in rows:
        d = dict(r)
        # Нормализуем поле limit
        d["limit"] = d.pop("user_limit", 50)
        result[str(d["id"])] = d
    return result


def is_banned(user_id: int) -> bool:
    return bool(get_user(user_id).get("banned", 0))


def is_premium(user_id: int) -> bool:
    if user_id == ADMIN_ID:
        return True
    u = get_user(user_id)
    if not u.get("premium"):
        return False
    until = u.get("premium_until")
    if not until:
        return False
    try:
        exp = datetime.fromisoformat(until)
        if datetime.now() > exp:
            update_user(user_id, premium=False, premium_until=None)
            return False
        return True
    except Exception:
        return False


def has_limit(user_id: int) -> bool:
    if user_id == ADMIN_ID:
        return True
    if is_premium(user_id):
        return True
    u = get_user(user_id)
    lim = u.get("user_limit", u.get("limit", 50000))
    return u["used"] < lim


def consume_limit(user_id: int, chars: int = 0):
    """Списываем символы (вопрос + ответ) с лимита пользователя."""
    if user_id == ADMIN_ID:
        return
    if is_premium(user_id):
        return
    u = get_user(user_id)
    update_user(user_id, used=u["used"] + max(chars, 1))


def remaining_limit(user_id: int) -> int:
    if user_id == ADMIN_ID:
        return 9_999_999
    if is_premium(user_id):
        return 9_999_999
    u = get_user(user_id)
    lim = u.get("user_limit", u.get("limit", 50000))
    return max(0, lim - u["used"])


def has_search_limit(user_id: int) -> bool:
    """Есть ли ещё поисковые запросы (для триала)."""
    if user_id == ADMIN_ID or is_premium(user_id):
        return True
    u = get_user(user_id)
    lim = cfg_int("default_search_limit")
    return u.get("search_used", 0) < lim


def consume_search_limit(user_id: int):
    if user_id == ADMIN_ID or is_premium(user_id):
        return
    u = get_user(user_id)
    update_user(user_id, search_used=u.get("search_used", 0) + 1)


def remaining_search_limit(user_id: int) -> int:
    if user_id == ADMIN_ID or is_premium(user_id):
        return 9999
    u = get_user(user_id)
    lim = cfg_int("default_search_limit")
    return max(0, lim - u.get("search_used", 0))


# ════════════════════════════════════════════════════
#  RATE LIMITER
# ════════════════════════════════════════════════════
_rate_timestamps: dict = {}


def check_rate_limit(user_id: int) -> bool:
    if user_id == ADMIN_ID:
        return True
    now = time.time()
    window = 60.0
    max_req = cfg_int("rate_limit_per_minute")
    stamps = _rate_timestamps.get(user_id, [])
    stamps = [t for t in stamps if now - t < window]
    if len(stamps) >= max_req:
        _rate_timestamps[user_id] = stamps
        return False
    stamps.append(now)
    _rate_timestamps[user_id] = stamps
    return True


def rate_limit_wait(user_id: int) -> int:
    stamps = _rate_timestamps.get(user_id, [])
    if not stamps:
        return 0
    oldest = min(stamps)
    wait = int(60 - (time.time() - oldest)) + 1
    return max(0, wait)


# ════════════════════════════════════════════════════
#  ИСТОРИЯ — SQLite
# ════════════════════════════════════════════════════
user_histories: dict = {}
user_files:     dict = {}
last_ai_reply:  dict = {}


def load_history(user_id: int) -> list:
    conn = get_db()
    c = conn.cursor()
    c.execute(
        "SELECT role, content FROM histories WHERE user_id=? ORDER BY position",
        (user_id,)
    )
    rows = c.fetchall()
    # conn is _db_connection (RAM), do not close
    return [{"role": r["role"], "content": r["content"]} for r in rows]


def save_history(user_id: int, history: list):
    conn = get_db()
    conn.execute("DELETE FROM histories WHERE user_id=?", (user_id,))
    for i, msg in enumerate(history):
        conn.execute(
            "INSERT INTO histories (user_id, position, role, content) VALUES (?, ?, ?, ?)",
            (user_id, i, msg["role"], msg["content"])
        )
    conn.commit()
    # conn is _db_connection (RAM), do not close
    request_save()  # отметить для сохранения


def get_user_history(user_id: int) -> list:
    if user_id not in user_histories:
        user_histories[user_id] = load_history(user_id)
    return user_histories[user_id]


async def compress_history(user_id: int):
    history   = get_user_history(user_id)
    threshold = cfg_int("summary_threshold")
    keep_last = cfg_int("summary_keep_last")
    if len(history) < threshold:
        return
    old_msgs  = history[:-keep_last]
    keep_msgs = history[-keep_last:]
    dialog = ""
    for m in old_msgs:
        role = "Пользователь" if m["role"] == "user" else "AI"
        dialog += f"{role}: {m['content']}\n\n"
    try:
        chat = client.chat.completions.create(
            model=CFG["summary_model"],
            messages=[
                {
                    "role": "system",
                    "content": (
                        "Ты — ассистент. Кратко резюмируй следующий диалог "
                        "в 3-5 предложениях на русском. "
                        "Сохрани ключевые факты, решения и контекст."
                    )
                },
                {"role": "user", "content": dialog}
            ],
            max_tokens=400,
        )
        summary = chat.choices[0].message.content.strip()
    except Exception as e:
        logger.warning(f"Ошибка сжатия истории для {user_id}: {e}")
        return
    compressed = [
        {"role": "system", "content": f"[Сжатая история диалога]: {summary}"}
    ] + keep_msgs
    user_histories[user_id] = compressed
    save_history(user_id, compressed)


# ════════════════════════════════════════════════════
#  ФАЙЛЫ ПОЛЬЗОВАТЕЛЯ (в памяти — не в БД)
# ════════════════════════════════════════════════════
def get_user_file(user_id): return user_files.get(user_id)
def set_user_file(user_id, filename, content): user_files[user_id] = {"filename": filename, "content": content}
def clear_user_file(user_id): user_files.pop(user_id, None)


# ════════════════════════════════════════════════════
#  КЭШ ОТВЕТОВ с TTL
# ════════════════════════════════════════════════════
_response_cache: dict = {}  # key -> (reply, timestamp)
_CACHE_TTL = 3600  # 1 час

def cache_key(api_messages):
    raw = json.dumps(api_messages, ensure_ascii=False, sort_keys=True)
    return hashlib.md5(raw.encode()).hexdigest()


def get_cached(api_messages):
    key = cache_key(api_messages)
    cached = _response_cache.get(key)
    if cached is None:
        return None
    reply, timestamp = cached
    # Проверяем TTL
    if time.time() - timestamp > _CACHE_TTL:
        _response_cache.pop(key, None)
        return None
    return reply


def set_cached(api_messages, reply):
    key = cache_key(api_messages)
    # Очистка старых записей если кэш переполнен
    if len(_response_cache) >= cfg_int("cache_max_size"):
        now = time.time()
        # Удаляем просроченные
        expired = [k for k, (r, t) in _response_cache.items() if now - t > _CACHE_TTL]
        for k in expired:
            _response_cache.pop(k, None)
        # Если всё ещё переполнен — удаляем самый старый
        if len(_response_cache) >= cfg_int("cache_max_size"):
            oldest = min(_response_cache.keys(), key=lambda k: _response_cache[k][1])
            _response_cache.pop(oldest)
    _response_cache[key] = (reply, time.time())


# ════════════════════════════════════════════════════
#  ИНВОЙСЫ — SQLite
# ════════════════════════════════════════════════════
def save_invoice(invoice_id: int, user_id: int, plan: str, chat_id: int, message_id: int):
    conn = get_db()
    conn.execute(
        "INSERT OR REPLACE INTO invoices (invoice_id, user_id, plan, chat_id, message_id) VALUES (?, ?, ?, ?, ?)",
        (invoice_id, user_id, plan, chat_id, message_id)
    )
    conn.commit()
    # conn is _db_connection (RAM), do not close
    request_save()  # 💰 запланировать сохранение (инвойс)


def get_invoice(invoice_id: int) -> dict | None:
    conn = get_db()
    c = conn.cursor()
    c.execute("SELECT * FROM invoices WHERE invoice_id=?", (invoice_id,))
    row = c.fetchone()
    # conn is _db_connection (RAM), do not close
    return dict(row) if row else None


def delete_invoice(invoice_id: int):
    conn = get_db()
    conn.execute("DELETE FROM invoices WHERE invoice_id=?", (invoice_id,))
    conn.commit()
    # conn is _db_connection (RAM), do not close
    request_save()  # отметить для сохранения


# ════════════════════════════════════════════════════
#  🧠 МУЛЬТИ-ЧАТЫ — управление чатами
# ════════════════════════════════════════════════════
def create_chat(user_id: int, name: str = "Новый чат") -> int:
    """Создаёт новый чат для пользователя. Возвращает chat_id."""
    conn = get_db()
    now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    c = conn.cursor()
    c.execute(
        "INSERT INTO chats (user_id, name, created_at, updated_at) VALUES (?, ?, ?, ?)",
        (user_id, name, now, now)
    )
    chat_id = c.lastrowid
    conn.commit()
    # conn is _db_connection (RAM), do not close
    # Устанавливаем как текущий
    update_user(user_id, current_chat_id=chat_id)
    request_save()
    return chat_id


def get_user_chats(user_id: int) -> list:
    """Возвращает список чатов пользователя."""
    conn = get_db()
    c = conn.cursor()
    c.execute(
        "SELECT * FROM chats WHERE user_id=? AND is_active=1 ORDER BY updated_at DESC",
        (user_id,)
    )
    rows = c.fetchall()
    # conn is _db_connection (RAM), do not close
    return [dict(row) for row in rows]


def get_chat(chat_id: int) -> dict | None:
    """Получает информацию о чате."""
    conn = get_db()
    c = conn.cursor()
    c.execute("SELECT * FROM chats WHERE chat_id=?", (chat_id,))
    row = c.fetchone()
    # conn is _db_connection (RAM), do not close
    return dict(row) if row else None


def switch_chat(user_id: int, chat_id: int) -> bool:
    """Переключается на указанный чат."""
    chat = get_chat(chat_id)
    if not chat or chat["user_id"] != user_id:
        return False
    update_user(user_id, current_chat_id=chat_id)
    return True


def rename_chat(chat_id: int, new_name: str):
    """Переименовывает чат."""
    conn = get_db()
    now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    conn.execute(
        "UPDATE chats SET name=?, updated_at=? WHERE chat_id=?",
        (new_name, now, chat_id)
    )
    conn.commit()
    # conn is _db_connection (RAM), do not close
    request_save()


def delete_chat(chat_id: int):
    """Удаляет чат (soft delete)."""
    conn = get_db()
    conn.execute("UPDATE chats SET is_active=0 WHERE chat_id=?", (chat_id,))
    conn.execute("DELETE FROM chat_messages WHERE chat_id=?", (chat_id,))
    conn.commit()
    # conn is _db_connection (RAM), do not close
    request_save()


def get_current_chat_id(user_id: int) -> int:
    """Возвращает ID текущего чата пользователя. Создаёт если нет."""
    u = get_user(user_id)
    current_id = u.get("current_chat_id", 0)
    
    # Проверяем существует ли чат
    if current_id:
        chat = get_chat(current_id)
        if chat and chat["is_active"]:
            return current_id
    
    # Создаём новый чат
    return create_chat(user_id, "Новый чат")


def save_chat_message(chat_id: int, user_id: int, role: str, content: str, tokens: int = 0):
    """Сохраняет сообщение в чат."""
    conn = get_db()
    now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    conn.execute(
        "INSERT INTO chat_messages (chat_id, user_id, role, content, created_at, tokens_used) "
        "VALUES (?, ?, ?, ?, ?, ?)",
        (chat_id, user_id, role, content, now, tokens)
    )
    # Обновляем счётчик сообщений в чате
    conn.execute(
        "UPDATE chats SET message_count = message_count + 1, updated_at = ? WHERE chat_id = ?",
        (now, chat_id)
    )
    conn.commit()
    # conn is _db_connection (RAM), do not close


def load_chat_messages(chat_id: int, limit: int = 100) -> list:
    """Загружает сообщения чата."""
    conn = get_db()
    c = conn.cursor()
    c.execute(
        "SELECT role, content FROM chat_messages WHERE chat_id=? ORDER BY msg_id DESC LIMIT ?",
        (chat_id, limit)
    )
    rows = c.fetchall()
    # conn is _db_connection (RAM), do not close
    # Возвращаем в хронологическом порядке
    return [{"role": r["role"], "content": r["content"]} for r in reversed(rows)]


# ════════════════════════════════════════════════════
#  ⚙️ НАСТРОЙКИ ПОЛЬЗОВАТЕЛЯ
# ════════════════════════════════════════════════════
def get_user_settings(user_id: int) -> dict:
    """Возвращает настройки пользователя."""
    conn = get_db()
    c = conn.cursor()
    c.execute("SELECT * FROM user_settings WHERE user_id=?", (user_id,))
    row = c.fetchone()
    if not row:
        # Создаём дефолтные настройки
        c.execute(
            "INSERT INTO user_settings (user_id) VALUES (?)",
            (user_id,)
        )
        conn.commit()
        c.execute("SELECT * FROM user_settings WHERE user_id=?", (user_id,))
        row = c.fetchone()
    # conn is _db_connection (RAM), do not close
    return dict(row) if row else {
        "response_style": "detailed",
        "bot_personality": "friendly",
        "auto_compress": 1,
        "notifications": 1
    }


def update_user_settings(user_id: int, **kwargs):
    """Обновляет настройки пользователя."""
    # Сначала создаём запись если нет
    get_user_settings(user_id)
    
    if not kwargs:
        return
    
    sets = []
    vals = []
    for k, v in kwargs.items():
        sets.append(f"{k}=?")
        vals.append(v)
    vals.append(user_id)
    
    conn = get_db()
    conn.execute(f"UPDATE user_settings SET {', '.join(sets)} WHERE user_id=?", vals)
    conn.commit()
    # conn is _db_connection (RAM), do not close
    request_save()


def get_response_style_text(style: str) -> str:
    """Возвращает текст стиля ответа для промпта."""
    styles = {
        "brief":    "Отвечай максимально кратко — 1-3 предложения. Без воды и повторов.",
        "detailed": "Отвечай подробно и структурированно. Используй списки где уместно.",
        "expert":   "Отвечай как эксперт: с технической точностью, глубиной и примерами."
    }
    return styles.get(style, styles["detailed"])


def get_personality_text(personality: str) -> str:
    """Возвращает текст характера бота для промпта."""
    personalities = {
        "strict": "Ты строгий и требовательный. Исправляй ошибки жёстко.",
        "friendly": "Ты дружелюбный и поддерживающий. Объясняй терпеливо.",
        "sarcastic": "Ты саркастичный и остроумный. Можешь подшучивать, но по делу."
    }
    return personalities.get(personality, personalities["friendly"])


# ════════════════════════════════════════════════════
#  💳 ПЛАТЕЖИ — история
# ════════════════════════════════════════════════════
def add_payment(user_id: int, plan: str, amount: float, currency: str, invoice_id: int):
    """Добавляет запись об успешном платеже."""
    conn = get_db()
    now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    conn.execute(
        "INSERT INTO payments (user_id, plan, amount, currency, paid_at, invoice_id, status) "
        "VALUES (?, ?, ?, ?, ?, ?, 'completed')",
        (user_id, plan, amount, currency, now, invoice_id)
    )
    conn.commit()
    # conn is _db_connection (RAM), do not close
    request_save()


def get_user_payments(user_id: int) -> list:
    """Возвращает историю платежей пользователя."""
    conn = get_db()
    c = conn.cursor()
    c.execute(
        "SELECT * FROM payments WHERE user_id=? ORDER BY paid_at DESC",
        (user_id,)
    )
    rows = c.fetchall()
    # conn is _db_connection (RAM), do not close
    return [dict(r) for r in rows]


# ════════════════════════════════════════════════════
#  📊 СТАТИСТИКА ПОЛЬЗОВАТЕЛЯ
# ════════════════════════════════════════════════════
def increment_user_stats(user_id: int, messages: int = 1, tokens: int = 0):
    """Увеличивает статистику пользователя."""
    conn = get_db()
    conn.execute(
        "UPDATE users SET total_messages = total_messages + ?, total_tokens = total_tokens + ? WHERE id=?",
        (messages, tokens, user_id)
    )
    conn.commit()
    # conn is _db_connection (RAM), do not close


def update_longest_chat(user_id: int, chat_length: int):
    """Обновляет рекорд самого длинного чата."""
    u = get_user(user_id)
    if chat_length > u.get("longest_chat", 0):
        update_user(user_id, longest_chat=chat_length)


def get_user_stats(user_id: int) -> dict:
    """Возвращает полную статистику пользователя."""
    u = get_user(user_id)
    payments = get_user_payments(user_id)
    total_paid = sum(p["amount"] for p in payments)
    
    return {
        "total_messages": u.get("total_messages", 0),
        "total_tokens": u.get("total_tokens", 0),
        "longest_chat": u.get("longest_chat", 0),
        "total_paid": total_paid,
        "payments_count": len(payments),
        "joined": u.get("joined", "—"),
        "used": u.get("used", 0),
        "limit": u.get("user_limit", u.get("limit", 50))
    }


def check_low_limit(user_id: int) -> int | None:
    """Проверяет осталось ли мало запросов. Возвращает остаток или None."""
    if is_premium(user_id):
        return None
    left = remaining_limit(user_id)
    if left <= 5000:
        return left
    return None


# ════════════════════════════════════════════════════
#  HTML-ФОРМАТИРОВАНИЕ
# ════════════════════════════════════════════════════
def escape_html(text):
    return text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def md_to_html(text):
    """Конвертация Markdown → HTML для Telegram (parse_mode=HTML)."""
    text = escape_html(text)
    # Заголовки
    text = re.sub(r'^### (.+)$', r'<b>▸ \1</b>', text, flags=re.MULTILINE)
    text = re.sub(r'^## (.+)$',  r'<b>◆ \1</b>', text, flags=re.MULTILINE)
    text = re.sub(r'^# (.+)$',   r'<b>🔷 \1</b>', text, flags=re.MULTILINE)
    # Жирный / курсив / зачёркнутый
    text = re.sub(r'\*\*\*(.+?)\*\*\*', r'<b><i>\1</i></b>', text)
    text = re.sub(r'\*\*(.+?)\*\*',     r'<b>\1</b>',        text)
    text = re.sub(r'__(.+?)__',          r'<b>\1</b>',        text)
    text = re.sub(r'(?<!\*)\*(?!\*)(.+?)(?<!\*)\*(?!\*)', r'<i>\1</i>', text)
    text = re.sub(r'(?<!_)_(?!_)(.+?)(?<!_)_(?!_)',       r'<i>\1</i>', text)
    text = re.sub(r'~~(.+?)~~', r'<s>\1</s>', text)
    # Инлайн-код: `код` → <code>код</code>
    text = re.sub(r'`([^`\n]+)`', r'<code>\1</code>', text)
    # Списки
    text = re.sub(r'^[ \t]*[-*•] (.+)$',       r'  • \1', text, flags=re.MULTILINE)
    text = re.sub(r'^[ \t]*(\d+)\. (.+)$',     r'  \1. \2', text, flags=re.MULTILINE)
    # Горизонтальный разделитель
    text = re.sub(r'^(?:---+|___+|\*\*\*+)$', '──────────────', text, flags=re.MULTILINE)
    return text


# ════════════════════════════════════════════════════
#  🎨 ЦВЕТОВАЯ СИСТЕМА ЧЕРЕЗ ЭМОДЗИ
# ════════════════════════════════════════════════════


def sanitize_html(text: str) -> str:
    """Закрывает незакрытые HTML теги чтобы Telegram не падал."""
    allowed = ["b", "i", "s", "u", "code", "pre"]
    stack = []
    import re as _re
    tag_pattern = _re.compile(r'<(/?)(\w+)[^>]*?>')
    for m in tag_pattern.finditer(text):
        closing, tag = m.group(1), m.group(2).lower()
        if tag not in allowed:
            continue
        if closing:
            if stack and stack[-1] == tag:
                stack.pop()
            else:
                # Mismatched closing tag — strip it
                text = text[:m.start()] + text[m.end():]
        else:
            stack.append(tag)
    # Close any remaining open tags
    for tag in reversed(stack):
        text += f'</{tag}>'
    return text

def fmt_ok(text: str) -> str:
    """🟢 Успех"""
    return f"🟢 <b>{text}</b>"

def fmt_err(text: str) -> str:
    """🔴 Ошибка"""
    return f"🔴 <b>{text}</b>"

def fmt_warn(text: str) -> str:
    """🟡 Предупреждение"""
    return f"🟡 <b>{text}</b>"

def fmt_info(text: str) -> str:
    """🔵 Информация"""
    return f"🔵 {text}"

def fmt_divider() -> str:
    """Разделитель ━━━━━━━━━━━━━━"""
    return "━━━━━━━━━━━━━━"

def loading_bar(percent: int) -> str:
    """Псевдо-загрузка: ▰▰▰▰▱▱▱ 60%"""
    total  = 7
    filled = round(total * percent / 100)
    bar    = "▰" * filled + "▱" * (total - filled)
    return f"{bar} {percent}%"

def fmt_message(title: str, summary: str = "", details: str = "") -> str:
    """
    Единый шаблон сообщения:
    [Заголовок]
    ━━━━━━━━━━━━━━
    [Суть]
    [Детали]
    """
    parts = [f"<b>{title}</b>", fmt_divider()]
    if summary:
        parts.append(summary)
    if details:
        if summary:
            parts.append("")   # пустая строка между summary и details
        parts.append(details)
    return "\n".join(parts)

def fmt_status_bar(elapsed: float, from_cache: bool, search_used: bool,
                   user_id: int, left: int) -> str:
    """
    Строка статуса в конце каждого ответа AI.
    Пример: ⏱ 1.2с • 🔍 поиск • ⚡ из кэша • 💎 Premium
    """
    parts = [f"⏱ <code>{elapsed}с</code>"]
    if search_used:
        parts.append("🔍 поиск")
    if from_cache:
        parts.append("⚡ кэш")
    model_short = CFG.get("groq_model", "").replace("llama", "Cicada").split("-")[0]  # убираем llama
    parts.append(f"🤖 <code>Cicada-AI</code>")
    if user_id == ADMIN_ID or is_premium(user_id):
        parts.append("💎 Premium")
    else:
        parts.append(f"💬 ост. <b>{left//1000}К</b> симв.")
    return "  ·  ".join(parts)


def parse_response(text):
    parts    = []
    pattern  = re.compile(r'```(\w*)\n(.*?)```', re.DOTALL)
    last_end = 0
    for match in pattern.finditer(text):
        before = text[last_end:match.start()].strip()
        if before:
            parts.append({"type": "text", "content": before})
        lang = match.group(1) or "code"
        code = match.group(2).strip()
        parts.append({"type": "code", "lang": lang, "content": code})
        last_end = match.end()
    after = text[last_end:].strip()
    if after:
        parts.append({"type": "text", "content": after})
    if not parts:
        parts.append({"type": "text", "content": text})
    return parts


# ════════════════════════════════════════════════════
#  ЭКСПОРТ ИСТОРИИ
# ════════════════════════════════════════════════════
def export_history(user_id, fmt="txt"):
    history  = get_user_history(user_id)
    filename = f"{FILES_DIR}/export_{user_id}_{datetime.now().strftime('%Y%m%d_%H%M%S')}.{fmt}"
    with open(filename, "w", encoding="utf-8") as f:
        if fmt == "md":
            f.write("# Cicada-AI Chat\n\n")
        for msg in history:
            role = "Ты" if msg["role"] == "user" else "AI"
            if fmt == "md":
                f.write(f"**{role}:**\n{msg['content']}\n\n---\n\n")
            else:
                f.write(f"{role}:\n{msg['content']}\n\n{'─'*40}\n\n")
    return filename


# ════════════════════════════════════════════════════
#  CRYPTOBOT — СОЗДАНИЕ ИНВОЙСА
# ════════════════════════════════════════════════════
PLAN_LABELS = {"day": "1 день", "week": "1 неделя", "month": "1 месяц"}
CURRENCIES  = ["USDT", "TRX", "LTC"]


async def create_invoice(user_id: int, plan: str, currency: str) -> dict | None:
    if not CRYPTOBOT_TOKEN:
        return None
    price_map = {
        "day":   cfg_float("price_day"),
        "week":  cfg_float("price_week"),
        "month": cfg_float("price_month"),
    }
    amount = price_map.get(plan)
    if not amount:
        return None
    payload = {
        "currency_type": "crypto",
        "asset":          currency,
        "amount":         str(amount),
        "description":    f"Cicada-AI Premium — {PLAN_LABELS[plan]}",
        "payload":        json.dumps({"user_id": user_id, "plan": plan}),
        "expires_in":     3600,
    }
    try:
        async with httpx.AsyncClient() as http:
            resp = await http.post(
                f"{CRYPTOBOT_API}/createInvoice",
                headers={"Crypto-Pay-API-Token": CRYPTOBOT_TOKEN},
                json=payload,
                timeout=10,
            )
        data = resp.json()
        if data.get("ok"):
            inv = data["result"]
            return {
                "invoice_id": inv["invoice_id"],
                "pay_url":    inv["pay_url"],
                "amount":     inv["amount"],
            }
    except Exception:
        pass
    return None


async def check_invoice(invoice_id: int) -> str:
    try:
        async with httpx.AsyncClient() as http:
            resp = await http.get(
                f"{CRYPTOBOT_API}/getInvoices",
                headers={"Crypto-Pay-API-Token": CRYPTOBOT_TOKEN},
                params={"invoice_ids": str(invoice_id)},
                timeout=10,
            )
        data = resp.json()
        if data.get("ok"):
            items = data["result"].get("items", [])
            if items:
                return items[0].get("status", "unknown")
    except Exception:
        pass
    return "unknown"


async def create_invoice_amount(user_id: int, amount: str, currency: str) -> dict | None:
    """Создаёт инвойс для произвольной суммы (новая система пополнения)."""
    if not CRYPTOBOT_TOKEN:
        return None
    
    try:
        payload = {
            "currency_type": "crypto",
            "asset":          currency,
            "amount":         str(amount),
            "description":    f"Cicada-AI — Пополнение на ${amount}",
            "payload":        json.dumps({"user_id": user_id, "amount": amount, "type": "balance"}),
            "expires_in":     3600,
        }
        
        async with httpx.AsyncClient() as http:
            resp = await http.post(
                f"{CRYPTOBOT_API}/createInvoice",
                headers={"Crypto-Pay-API-Token": CRYPTOBOT_TOKEN},
                json=payload,
                timeout=10,
            )
        data = resp.json()
        if data.get("ok"):
            inv = data["result"]
            return {
                "invoice_id": inv["invoice_id"],
                "pay_url":    inv["pay_url"],
                "amount":     inv["amount"],
            }
    except Exception as e:
        logger.error(f"Ошибка создания инвойса: {e}")
    return None


def activate_premium(user_id: int, plan: str):
    """
    Активирует Premium. Поддерживает форматы:
      - "premium_7d"  → 7 дней (новая система)
      - "premium_1m"  → 1 месяц (устаревшая система)
      - "day" / "week" / "month"  → legacy
    """
    # Новый формат: premium_Xd (дни)
    if plan.startswith("premium_") and plan.endswith("d"):
        try:
            days = int(plan.replace("premium_", "").replace("d", ""))
            delta = timedelta(days=days)
        except ValueError:
            delta = timedelta(days=1)
    # Старый формат: premium_Xm (месяцы)
    elif plan.startswith("premium_") and plan.endswith("m"):
        try:
            months = int(plan.replace("premium_", "").replace("m", ""))
            delta = timedelta(days=30 * months)
        except ValueError:
            delta = timedelta(days=30)
    else:
        delta_map = {
            "day":   timedelta(days=1),
            "week":  timedelta(weeks=1),
            "month": timedelta(days=30),
        }
        delta = delta_map.get(plan, timedelta(days=1))

    u = get_user(user_id)
    current_until = u.get("premium_until")
    if current_until:
        try:
            base  = datetime.fromisoformat(current_until)
            until = (base + delta) if base > datetime.now() else (datetime.now() + delta)
        except Exception:
            until = datetime.now() + delta
    else:
        until = datetime.now() + delta
    update_user(user_id, premium=True, premium_until=until.isoformat(), is_trial=False)


# ════════════════════════════════════════════════════
#  КЛАВИАТУРЫ — ПОЛЬЗОВАТЕЛЬ (Premium UX)
# ════════════════════════════════════════════════════
def main_keyboard(user_id=None):
    """Главное меню — 6 разделов как на схеме."""
    buttons = [
        [
            InlineKeyboardButton("🧠 Мои чаты",     callback_data="my_chats"),
            InlineKeyboardButton("⚙️ Настройки",    callback_data="my_settings"),
        ],
        [
            InlineKeyboardButton("💎 Подписка",     callback_data="subscription_menu"),
            InlineKeyboardButton("📊 Статистика",   callback_data="my_stats"),
        ],
        [
            InlineKeyboardButton("🛠 Инструменты",  callback_data="tools_menu"),
            InlineKeyboardButton("ℹ️ О боте",       callback_data="about_menu"),
        ],
    ]
    if user_id and get_user_file(user_id):
        buttons.append([
            InlineKeyboardButton("💾 Скачать файл", callback_data="download_file"),
            InlineKeyboardButton("❌ Удалить файл", callback_data="clear_file"),
        ])
    if user_id == ADMIN_ID:
        buttons.append([InlineKeyboardButton("🛡 Админ-панель", callback_data="admin_panel")])
    return InlineKeyboardMarkup(buttons)


def after_reply_keyboard(user_id=None):
    """Клавиатура после ответа AI — делает бот 'живым'."""
    buttons = [
        [
            InlineKeyboardButton("🔊 Озвучить",    callback_data="tts"),
        ],
        [
            InlineKeyboardButton("🔄 Повторить",   callback_data="retry"),
            InlineKeyboardButton("🗑 Очистить",    callback_data="clear"),
        ],
        [InlineKeyboardButton("◀️ Главное меню", callback_data="back_menu")],
    ]
    if user_id and get_user_file(user_id):
        buttons.insert(2, [
            InlineKeyboardButton("💾 Скачать файл", callback_data="download_file"),
            InlineKeyboardButton("❌ Удалить файл", callback_data="clear_file"),
        ])
    if user_id and user_id in _last_code_files and _last_code_files[user_id]:
        buttons.insert(0, [
            InlineKeyboardButton("📦 Скачать код архивом", callback_data="download_zip"),
        ])
    if user_id == ADMIN_ID:
        buttons.append([InlineKeyboardButton("🛡 Админ-панель", callback_data="admin_panel")])
    return InlineKeyboardMarkup(buttons)


def file_keyboard():
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton("💾 Скачать изменённый файл", callback_data="download_file"),
            InlineKeyboardButton("❌ Удалить файл",            callback_data="clear_file"),
        ],
        [InlineKeyboardButton("🔊 Озвучить ответ", callback_data="tts")],
    ])


def export_keyboard():
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton("📄 TXT", callback_data="export_txt"),
            InlineKeyboardButton("📝 MD",  callback_data="export_md"),
        ],
        [InlineKeyboardButton("◀️ Назад", callback_data="back_menu")],
    ])


def confirm_clear_keyboard():
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton("✅ Да, очистить", callback_data="confirm_clear"),
            InlineKeyboardButton("❌ Отмена",       callback_data="back_menu"),
        ]
    ])


def retry_error_keyboard():
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton("🔄 Попробовать снова", callback_data="retry"),
            InlineKeyboardButton("🗑 Очистить",          callback_data="clear"),
        ]
    ])


# ════════════════════════════════════════════════════
#  🧠 КЛАВИАТУРЫ — МУЛЬТИ-ЧАТЫ
# ════════════════════════════════════════════════════
def my_chats_menu_keyboard():
    """Главное меню раздела 'Мои чаты' — 3 действия."""
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("➕ Новый чат",  callback_data="create_chat")],
        [InlineKeyboardButton("💬 Мои чаты",  callback_data="chats_list")],
        [InlineKeyboardButton("🗑 Удалить чат", callback_data="delete_chat_menu")],
        [InlineKeyboardButton("◀️ Назад",      callback_data="back_menu")],
    ])


def chats_list_keyboard(user_id: int, chats: list, current_chat_id: int):
    """Список чатов — при нажатии на чат открывается меню действий."""
    buttons = []
    for chat in chats[:10]:
        cid = chat["chat_id"]
        name = chat["name"][:22]
        count = chat.get("message_count", 0)
        prefix = "▶️ " if cid == current_chat_id else "💬 "
        buttons.append([InlineKeyboardButton(
            f"{prefix}{name} ({count})",
            callback_data=f"chat_menu_{cid}"
        )])
    buttons.append([InlineKeyboardButton("◀️ Назад", callback_data="my_chats")])
    return InlineKeyboardMarkup(buttons)


def chat_actions_keyboard(chat_id: int):
    """Действия с конкретным чатом: Переименовать / Экспортировать / Удалить."""
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("✏️ Переименовать",  callback_data=f"chat_rename_{chat_id}")],
        [InlineKeyboardButton("📤 Экспортировать", callback_data=f"chat_export_{chat_id}")],
        [InlineKeyboardButton("🗑 Удалить",         callback_data=f"chat_delete_{chat_id}")],
        [InlineKeyboardButton("◀️ Назад",           callback_data="chats_list")],
    ])


# ════════════════════════════════════════════════════
#  ⚙️ КЛАВИАТУРЫ — НАСТРОЙКИ
# ════════════════════════════════════════════════════
def settings_keyboard(user_id: int):
    """Клавиатура настроек — показывает текущие значения."""
    settings = get_user_settings(user_id)
    style = settings.get("response_style", "detailed")
    personality = settings.get("bot_personality", "friendly")
    notif = bool(settings.get("notifications", 1))

    style_labels = {"brief": "📄 Кратко", "detailed": "📋 Подробно", "expert": "🎓 Эксперт"}
    pers_labels = {"strict": "👔 Строгий", "friendly": "🤗 Дружелюбный", "sarcastic": "😏 Саркастичный"}
    notif_status = "вкл ✅" if notif else "выкл ❌"

    return InlineKeyboardMarkup([
        [InlineKeyboardButton(f"📝 Стиль: {style_labels.get(style, style)}", callback_data="settings_style_menu")],
        [InlineKeyboardButton(f"🎭 Характер: {pers_labels.get(personality, personality)}", callback_data="settings_personality_menu")],
        [InlineKeyboardButton("🌐 Язык",                              callback_data="settings_language_menu")],
        [InlineKeyboardButton(f"🔔 Уведомления: {notif_status}",       callback_data="settings_notifications")],
        [InlineKeyboardButton("🧠 Память бота",                       callback_data="settings_memory_menu")],
        [InlineKeyboardButton("◀️ Назад",                             callback_data="back_menu")],
    ])


def style_select_keyboard():
    """Выбор стиля ответа."""
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("📄 Кратко — без воды", callback_data="set_style_brief")],
        [InlineKeyboardButton("📋 Подробно — структурированно", callback_data="set_style_detailed")],
        [InlineKeyboardButton("🎓 Эксперт — технически", callback_data="set_style_expert")],
        [InlineKeyboardButton("◀️ Назад", callback_data="my_settings")],
    ])


def personality_select_keyboard():
    """Выбор характера бота."""
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("👔 Строгий — исправляет ошибки", callback_data="set_personality_strict")],
        [InlineKeyboardButton("🤗 Дружелюбный — терпеливо", callback_data="set_personality_friendly")],
        [InlineKeyboardButton("😏 Саркастичный — остроумно", callback_data="set_personality_sarcastic")],
        [InlineKeyboardButton("◀️ Назад", callback_data="my_settings")],
    ])


# ════════════════════════════════════════════════════
#  📊 КЛАВИАТУРЫ — СТАТИСТИКА
# ════════════════════════════════════════════════════
def stats_keyboard():
    """Клавиатура статистики — как на схеме."""
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("📊 Общая статистика",   callback_data="stats_general")],
        [InlineKeyboardButton("🔤 Расход токенов",     callback_data="stats_tokens")],
        [InlineKeyboardButton("💬 Кол-во сообщений",  callback_data="stats_messages")],
        [InlineKeyboardButton("🏆 Достижения",         callback_data="stats_achievements")],
        [InlineKeyboardButton("◀️ Назад",              callback_data="back_menu")],
    ])


def cabinet_keyboard(user_id=None):
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton("📊 Статистика чата",  callback_data="stats"),
            InlineKeyboardButton("🗑 Очистить историю", callback_data="clear"),
        ],
        [InlineKeyboardButton("💎 Управление подпиской", callback_data="subscription_menu")],
        [InlineKeyboardButton("◀️ Назад",          callback_data="back_menu")],
    ])


# ════════════════════════════════════════════════════
#  💎 КЛАВИАТУРЫ — ПОДПИСКА (как на схеме)
# ════════════════════════════════════════════════════
def subscription_menu_keyboard():
    """Главное меню подписки."""
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("📋 Мой план",         callback_data="my_plan")],
        [InlineKeyboardButton("📜 История платежей", callback_data="payments_history")],
        [InlineKeyboardButton("🎁 Ввести промокод",  callback_data="enter_promo")],
        [InlineKeyboardButton("◀️ Назад",            callback_data="back_menu")],
    ])


def my_plan_keyboard():
    """Клавиатура для 'Мой план' — кнопка покупки ведёт на выбор дней."""
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("💎 Купить Premium", callback_data="add_balance")],
        [InlineKeyboardButton("📊 Полная статистика", callback_data="my_stats")],
        [InlineKeyboardButton("◀️ Назад", callback_data="subscription_menu")],
    ])


def buy_days_keyboard():
    """Красивые кнопки покупки Premium — по дням, $1/день."""
    plans = [
        ("1",  "1️⃣",  "1 день",   "$1"),
        ("3",  "3️⃣",  "3 дня",    "$3"),
        ("7",  "7️⃣",  "7 дней",   "$7"),
        ("15", "🔥",  "15 дней",  "$15"),
        ("30", "💎",  "30 дней",  "$30"),
    ]
    buttons = []
    for days, icon, label, price in plans:
        buttons.append([InlineKeyboardButton(
            f"{icon}  {label}  —  {price}",
            callback_data=f"pay_days_{days}"
        )])
    buttons.append([InlineKeyboardButton("◀️ Назад", callback_data="my_plan")])
    return InlineKeyboardMarkup(buttons)


def currency_for_days_keyboard(days: str, amount: str):
    """Выбор валюты после выбора дней."""
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("💵 USDT", callback_data=f"pay_daycur_USDT_{days}_{amount}")],
        [InlineKeyboardButton("🔺 TRX",  callback_data=f"pay_daycur_TRX_{days}_{amount}")],
        [InlineKeyboardButton("🪙 LTC",  callback_data=f"pay_daycur_LTC_{days}_{amount}")],
        [InlineKeyboardButton("◀️ Назад", callback_data="add_balance")],
    ])


def add_balance_keyboard():
    """Клавиатура покупки Premium — 1/3/5/7 месяцев."""
    p1 = cfg_float("price_1month")
    p3 = cfg_float("price_3month")
    p5 = cfg_float("price_5month")
    p7 = cfg_float("price_7month")
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton(f"1 мес — ${p1}",  callback_data="pay_months_1"),
            InlineKeyboardButton(f"3 мес — ${p3}",  callback_data="pay_months_3"),
        ],
        [
            InlineKeyboardButton(f"5 мес — ${p5}",  callback_data="pay_months_5"),
            InlineKeyboardButton(f"7 мес — ${p7}",  callback_data="pay_months_7"),
        ],
        [InlineKeyboardButton("◀️ Назад", callback_data="subscription_menu")],
    ])


def currency_keyboard(amount: str):
    """Выбор валюты для оплаты."""
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("💵 USDT", callback_data=f"pay_currency_USDT_{amount}")],
        [InlineKeyboardButton("🔺 TRX",  callback_data=f"pay_currency_TRX_{amount}")],
        [InlineKeyboardButton("🪙 LTC",  callback_data=f"pay_currency_LTC_{amount}")],
        [InlineKeyboardButton("◀️ Назад", callback_data="add_balance")],
    ])


def currency_keyboard_legacy(plan: str):
    """Старый выбор валюты (для обратной совместимости)."""
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("💵 USDT", callback_data=f"pay_{plan}_USDT")],
        [InlineKeyboardButton("🔺 TRX",  callback_data=f"pay_{plan}_TRX")],
        [InlineKeyboardButton("🪙 LTC",  callback_data=f"pay_{plan}_LTC")],
        [InlineKeyboardButton("◀️ Назад", callback_data="subscription_menu")],
    ])


def payments_history_keyboard():
    """Клавиатура для истории платежей."""
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("🔄 Обновить", callback_data="payments_history")],
        [InlineKeyboardButton("◀️ Назад", callback_data="subscription_menu")],
    ])


# ════════════════════════════════════════════════════
#  🛠 ИНСТРУМЕНТЫ — клавиатуры
# ════════════════════════════════════════════════════
def tools_menu_keyboard():
    """Меню инструментов — как на схеме."""
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("✏️ Рерайт текста",       callback_data="tool_rewrite")],
        [InlineKeyboardButton("🌐 Переводчик",           callback_data="tool_translate")],
        [InlineKeyboardButton("💻 Генерация кода",       callback_data="tool_codegen")],
        [InlineKeyboardButton("📄 Резюме текста",        callback_data="tool_summarize")],
        [InlineKeyboardButton("🖼 Генерация изображений", callback_data="tool_imagegen")],
        [InlineKeyboardButton("🔊 Озвучка текста",       callback_data="tool_tts_menu")],
        [InlineKeyboardButton("◀️ Назад",               callback_data="back_menu")],
    ])


def translate_language_keyboard():
    """Выбор языка перевода."""
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("🇬🇧 English",   callback_data="translate_en")],
        [InlineKeyboardButton("🇩🇪 Deutsch",   callback_data="translate_de")],
        [InlineKeyboardButton("🇫🇷 Français",  callback_data="translate_fr")],
        [InlineKeyboardButton("🇪🇸 Español",   callback_data="translate_es")],
        [InlineKeyboardButton("🇨🇳 中文",       callback_data="translate_zh")],
        [InlineKeyboardButton("◀️ Назад",       callback_data="tools_menu")],
    ])


def codegen_language_keyboard():
    """Выбор языка генерации кода."""
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("🐍 Python",     callback_data="codegen_python")],
        [InlineKeyboardButton("🟨 JavaScript", callback_data="codegen_javascript")],
        [InlineKeyboardButton("☕ Java",        callback_data="codegen_java")],
        [InlineKeyboardButton("💜 C#",          callback_data="codegen_csharp")],
        [InlineKeyboardButton("➕ Другой",      callback_data="codegen_other")],
        [InlineKeyboardButton("◀️ Назад",       callback_data="tools_menu")],
    ])


# ════════════════════════════════════════════════════
#  ℹ️ О БОТЕ — клавиатуры
# ════════════════════════════════════════════════════
def about_menu_keyboard():
    """Меню о боте — как на схеме."""
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("❓ Как использовать", callback_data="about_howto")],
        [InlineKeyboardButton("📜 Правила",           callback_data="about_rules")],
        [InlineKeyboardButton("🔒 Конфиденциальность", callback_data="about_privacy")],
        [InlineKeyboardButton("🆘 Поддержка",         callback_data="about_support")],
        [InlineKeyboardButton("⭐ Оценить бота",      callback_data="about_rate")],
        [InlineKeyboardButton("◀️ Назад",             callback_data="back_menu")],
    ])


# ════════════════════════════════════════════════════
#  ⚙️ НАСТРОЙКИ — дополнительные клавиатуры
# ════════════════════════════════════════════════════
def settings_model_keyboard():
    """Выбор модели AI в настройках."""
    current = CFG.get("groq_model", "")
    buttons = []
    for model in AVAILABLE_MODELS:
        mark = "✅ " if model == current else ""
        buttons.append([InlineKeyboardButton(f"{mark}{model}", callback_data=f"set_model_{model}")])
    buttons.append([InlineKeyboardButton("◀️ Назад", callback_data="my_settings")])
    return InlineKeyboardMarkup(buttons)


def settings_language_keyboard():
    """Выбор языка интерфейса."""
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("🇷🇺 Русский",    callback_data="set_lang_ru")],
        [InlineKeyboardButton("🇬🇧 English",    callback_data="set_lang_en")],
        [InlineKeyboardButton("🇺🇦 Українська", callback_data="set_lang_uk")],
        [InlineKeyboardButton("◀️ Назад",        callback_data="my_settings")],
    ])


def settings_memory_keyboard():
    """Управление памятью бота."""
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("🗑 Очистить историю",     callback_data="memory_clear_history")],
        [InlineKeyboardButton("📤 Экспорт TXT",          callback_data="export_txt")],
        [InlineKeyboardButton("📝 Экспорт MD",           callback_data="export_md")],
        [InlineKeyboardButton("◀️ Назад",                callback_data="my_settings")],
    ])


# Legacy keyboards (для обратной совместимости)
def premium_plans_keyboard():
    """Старые планы (day/week/month) — можно удалить позже."""
    pd = cfg_float("price_day")
    pw = cfg_float("price_week")
    pm = cfg_float("price_month")
    return InlineKeyboardMarkup([
        [InlineKeyboardButton(f"⚡ День — ${pd}",    callback_data="plan_day")],
        [InlineKeyboardButton(f"📅 Неделя — ${pw}", callback_data="plan_week")],
        [InlineKeyboardButton(f"🌟 Месяц — ${pm}",  callback_data="plan_month")],
        [InlineKeyboardButton("◀️ Назад",            callback_data="subscription_menu")],
    ])


def invoice_keyboard(pay_url: str, invoice_id: int):
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("💳 Оплатить",         url=pay_url)],
        [InlineKeyboardButton("✅ Проверить оплату", callback_data=f"check_invoice_{invoice_id}")],
        [InlineKeyboardButton("◀️ Отмена",           callback_data="buy_premium")],
    ])


# ════════════════════════════════════════════════════
#  🛡 КЛАВИАТУРЫ — АДМИН-ПАНЕЛЬ (как на схеме)
# ════════════════════════════════════════════════════
def admin_panel_keyboard():
    """Главное меню админ-панели — 6 разделов."""
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton("👥 Пользователи",  callback_data="admin_users"),
            InlineKeyboardButton("📢 Рассылки",      callback_data="admin_broadcast"),
        ],
        [
            InlineKeyboardButton("💳 Платежи",       callback_data="admin_payments"),
            InlineKeyboardButton("📊 Статистика",    callback_data="admin_stats"),
        ],
        [
            InlineKeyboardButton("🤖 Модели AI",    callback_data="admin_models_menu"),
            InlineKeyboardButton("📝 Логи",         callback_data="admin_logs"),
        ],
        [
            InlineKeyboardButton("📊 Счётчики API", callback_data="admin_api_stats"),
            InlineKeyboardButton("⚙️ Настройки",    callback_data="admin_bot_settings"),
        ],
        [
            InlineKeyboardButton("◀️ Главное меню",   callback_data="back_menu"),
        ],
    ])


def admin_bot_settings_keyboard():
    """Настройки бота — Цены, БД, Токены, Перезагрузка."""
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("💰 Цены Premium",     callback_data="admin_prices")],
        [
            InlineKeyboardButton("💾 Скачать БД",     callback_data="admin_download_db"),
            InlineKeyboardButton("💾 Сохранить БД",   callback_data="admin_save_db"),
        ],
        [InlineKeyboardButton("📤 Загрузить БД",    callback_data="admin_upload_db")],
        [InlineKeyboardButton("🔑 Токены API",      callback_data="admin_tokens")],
        [InlineKeyboardButton("🔄 Перезагрузить бота", callback_data="admin_restart_bot")],
        [InlineKeyboardButton("⚠️ Бот на тех работах", callback_data="admin_maintenance")],
        [InlineKeyboardButton("◀️ Назад",            callback_data="admin_panel")],
    ])


def admin_tokens_keyboard():
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("🔑 Сменить GROQ токен",   callback_data="admin_set_groq_token")],
        [InlineKeyboardButton("🔑 Сменить Tavily токен", callback_data="admin_set_tavily_token")],
        [InlineKeyboardButton("🔑 Сменить Bot токен",    callback_data="admin_set_bot_token")],
        [InlineKeyboardButton("🚨 Порог уведомлений",    callback_data="admin_alert_threshold")],
        [InlineKeyboardButton("◀️ Назад", callback_data="admin_bot_settings")],
    ])


def admin_alert_threshold_keyboard():
    groq_t  = CFG.get("groq_alert_threshold", "800")
    tav_t   = CFG.get("tavily_alert_threshold", "800")
    return InlineKeyboardMarkup([
        [InlineKeyboardButton(f"🤖 Groq порог: {groq_t}",   callback_data="admin_set_groq_threshold")],
        [InlineKeyboardButton(f"🔍 Tavily порог: {tav_t}",  callback_data="admin_set_tavily_threshold")],
        [InlineKeyboardButton("◀️ Назад", callback_data="admin_tokens")],
    ])


def admin_prices_keyboard():
    """Клавиатура для изменения цен Premium — 1/3/5/7 месяцев."""
    p1 = cfg_float("price_1month")
    p3 = cfg_float("price_3month")
    p5 = cfg_float("price_5month")
    p7 = cfg_float("price_7month")
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton(f"1 мес: ${p1}", callback_data="admin_setprice_1month"),
            InlineKeyboardButton(f"3 мес: ${p3}", callback_data="admin_setprice_3month"),
        ],
        [
            InlineKeyboardButton(f"5 мес: ${p5}", callback_data="admin_setprice_5month"),
            InlineKeyboardButton(f"7 мес: ${p7}", callback_data="admin_setprice_7month"),
        ],
        [InlineKeyboardButton("◀️ Назад", callback_data="admin_bot_settings")],
    ])


def admin_model_keyboard():
    buttons = []
    current = CFG["groq_model"]
    for model in AVAILABLE_MODELS:
        mark = "✅ " if model == current else ""
        buttons.append([InlineKeyboardButton(f"{mark}{model}", callback_data=f"admin_setmodel_{model}")])
    buttons.append([InlineKeyboardButton("◀️ Назад", callback_data="admin_panel")])
    return InlineKeyboardMarkup(buttons)


def admin_user_keyboard(uid: str, is_banned_flag: bool):
    ban_label = "🔓 Разбанить" if is_banned_flag else "🔨 Забанить"
    ban_cb    = f"admin_unban_{uid}" if is_banned_flag else f"admin_ban_{uid}"
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton(ban_label,             callback_data=ban_cb),
            InlineKeyboardButton("🗑 Удалить",          callback_data=f"admin_delete_{uid}"),
        ],
        [
            InlineKeyboardButton("➕ Добавить лимит",   callback_data=f"admin_addlimit_{uid}"),
            InlineKeyboardButton("➖ Уменьшить лимит",  callback_data=f"admin_sublimit_{uid}"),
        ],
        [
            InlineKeyboardButton("🔄 Сбросить счётчик", callback_data=f"admin_resetused_{uid}"),
            InlineKeyboardButton("💎 Дать Premium",      callback_data=f"admin_givepremium_{uid}"),
        ],
        [InlineKeyboardButton("◀️ Назад", callback_data="admin_users")],
    ])


def admin_users_keyboard(users: dict, page: int = 0):
    items    = list(users.items())
    per_page = 8
    start    = page * per_page
    end      = start + per_page
    chunk    = items[start:end]
    buttons  = []
    for uid, u in chunk:
        name  = u.get("first_name") or u.get("username") or uid
        icon  = "🚫" if u.get("banned") else ("💎" if u.get("premium") else "✅")
        lim   = u.get("user_limit", u.get("limit", 50))
        left  = max(0, lim - u.get("used", 0))
        label = f"{icon} {name[:18]} [{left}/{lim}]"
        buttons.append([InlineKeyboardButton(label, callback_data=f"admin_user_{uid}")])
    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton("⬅️", callback_data=f"admin_users_page_{page-1}"))
    if end < len(items):
        nav.append(InlineKeyboardButton("➡️", callback_data=f"admin_users_page_{page+1}"))
    if nav:
        buttons.append(nav)
    buttons.append([InlineKeyboardButton("◀️ Назад", callback_data="admin_panel")])
    return InlineKeyboardMarkup(buttons)


# ════════════════════════════════════════════════════
#  /start
# ════════════════════════════════════════════════════
async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user    = update.effective_user
    user_id = user.id
    update_user(user_id, username=user.username or "", first_name=user.first_name or "")
    if MAINTENANCE_MODE and user_id != ADMIN_ID:
        await update.message.reply_text(
            "🔧 <b>Технические работы</b>\n\nБот временно недоступен. Скоро вернёмся! ⏳",
            parse_mode=ParseMode.HTML,
        )
        return
    if is_banned(user_id):
        await update.message.reply_text(fmt_err("Доступ заблокирован"), parse_mode=ParseMode.HTML)
        return
    u    = get_user(user_id)
    left = remaining_limit(user_id)
    prem_tag = ""
    if is_premium(user_id) and user_id != ADMIN_ID:
        until = u.get("premium_until", "")
        try:
            exp = datetime.fromisoformat(until).strftime("%d.%m.%Y %H:%M")
        except Exception:
            exp = until
        prem_tag = f"\n💎 <b>Premium</b> до {exp}"
    elif u.get("is_trial", 1):
        lim = u.get("user_limit", u.get("limit", 50))
        prem_tag = f"\n🎁 Триал: <b>{left//1000}К / {lim//1000}К</b> символов"
    await update.message.reply_text(
        fmt_message(
            f"👋 Привет, {escape_html(user.first_name or 'разработчик')}!",
            f"<b>Cicada AI</b> <code>v4.5</code> — готов к работе{prem_tag}",
            "🧠 Код · 🔧 Рефакторинг · 📎 Файлы · 🎤 Голос · 🔍 Поиск\n\n"
            "💡 Напиши задачу или закинь файл"
        ),
        parse_mode=ParseMode.HTML,
        reply_markup=main_keyboard(user_id),
    )


# ════════════════════════════════════════════════════
#  ОБРАБОТКА ДОКУМЕНТОВ
# ════════════════════════════════════════════════════
# ════════════════════════════════════════════════════
#  ОБРАБОТКА БОЛЬШОГО ФАЙЛА ПО ЧАНКАМ
# ════════════════════════════════════════════════════
CHUNK_SIZE = 3000  # символов на один запрос к AI

def split_into_chunks(text: str, chunk_size: int = CHUNK_SIZE) -> list:
    """Разбивает текст на куски по chunk_size символов, стараясь резать по строкам."""
    chunks = []
    while len(text) > chunk_size:
        # Ищем последний перенос строки в пределах chunk_size
        cut = text.rfind('\n', 0, chunk_size)
        if cut == -1:
            cut = chunk_size
        chunks.append(text[:cut])
        text = text[cut:].lstrip('\n')
    if text.strip():
        chunks.append(text)
    return chunks


async def process_file_in_chunks(message, context, user_id: int, user_input: str, filename: str, content: str):
    """
    Обрабатывает большой файл по чанкам:
    1. Анализирует каждый чанк
    2. Собирает итоговый ответ
    3. Отправляет пользователю
    """
    chunks = split_into_chunks(content, CHUNK_SIZE)
    total = len(chunks)

    status_msg = await message.reply_text(
        f"📂 <b>Файл большой ({len(content)//1000}КБ)</b>\nРазбиваю на <b>{total}</b> частей и анализирую...\n\n⏳ Часть 1 / {total}",
        parse_mode="HTML",
    )

    partial_results = []
    loop = asyncio.get_running_loop()

    for i, chunk in enumerate(chunks, 1):
        try:
            await status_msg.edit_text(
                f"📂 <b>Обрабатываю файл</b>\n⏳ Часть {i} / {total}\n{'█' * i}{'░' * (total - i)} {i*100//total}%",
                parse_mode="HTML",
            )
        except Exception:
            pass

        system_msg = (
            f"Ты — Cicada AI, AI-ассистент для разработчиков. "
            f"Анализируешь файл «{filename}» по частям. "
            f"Это часть {i} из {total}. "
            f"Запрос пользователя: {user_input}\n\n"
            f"Проанализируй эту часть и выдай краткий результат. "
            f"Если часть последняя — дай итоговый вывод."
        )
        api_messages = [
            {"role": "system", "content": system_msg},
            {"role": "user", "content": f"Часть {i}/{total} файла:\n```\n{chunk}\n```"},
        ]
        if partial_results:
            # Добавляем краткое резюме предыдущих частей
            prev_summary = "\n".join(partial_results[-2:])  # последние 2 результата
            api_messages.insert(1, {
                "role": "assistant",
                "content": f"Результаты предыдущих частей:\n{prev_summary}"
            })

        try:
            last_exc = None
            for _attempt in range(len(_GROQ_KEYS) or 1):
                _client = _get_groq_client()  # FIX: клиент создаётся при каждой попытке
                def _call(_c=_client):
                    return _c.chat.completions.create(
                        model=CFG["groq_model"],
                        messages=api_messages,
                        max_tokens=2048,
                    )
                try:
                    chat = await loop.run_in_executor(None, _call)
                    result = chat.choices[0].message.content.strip()
                    last_exc = None
                    break
                except Exception as _e:
                    last_exc = _e
                    err_str = str(_e)
                    # При 429 ждём дольше перед следующим ключом
                    wait = 15 if "429" in err_str or "rate_limit" in err_str.lower() else 3
                    logger.warning(f"Chunk {i}, попытка {_attempt+1}: {_e}, ждём {wait}с")
                    await asyncio.sleep(wait)
            if last_exc:
                raise last_exc
            partial_results.append(f"[Часть {i}]:\n{result}")
        except Exception as e:
            err = str(e)
            await status_msg.edit_text(
                f"❌ <b>Ошибка на части {i}/{total}</b>\n<code>{escape_html(err)}</code>",
                parse_mode="HTML",
            )
            return
        # Пауза убрана — ротация ключей справляется сама

    # Финальная сборка
    try:
        await status_msg.edit_text(
            f"✅ <b>Все {total} части обработаны</b>\nФормирую итог...",
            parse_mode="HTML",
        )
    except Exception:
        pass

    final_system = (
        f"Ты — Cicada AI. Собери итоговый ответ на запрос пользователя "
        f"по файлу «{filename}» на основе анализа всех частей. "
        f"Запрос: {user_input}"
    )
    final_messages = [
        {"role": "system", "content": final_system},
        {"role": "user", "content": "\n\n".join(partial_results)},
    ]

    try:
        last_exc = None
        for _attempt in range(len(_GROQ_KEYS) or 1):
            _client_final = _get_groq_client()  # FIX: клиент создаётся при каждой попытке
            def _call_final(_c=_client_final):
                return _c.chat.completions.create(
                    model=CFG["groq_model"],
                    messages=final_messages,
                    max_tokens=4096,
                )
            try:
                chat = await loop.run_in_executor(None, _call_final)
                final_reply = chat.choices[0].message.content.strip()
                last_exc = None
                break
            except Exception as _e:
                last_exc = _e
                err_str = str(_e)
                wait = 15 if "429" in err_str or "rate_limit" in err_str.lower() else 3
                logger.warning(f"Финальная сборка, попытка {_attempt+1}: {_e}, ждём {wait}с")
                await asyncio.sleep(wait)
        if last_exc:
            raise last_exc
    except Exception as e:
        await status_msg.edit_text(
            f"❌ <b>Ошибка финальной сборки</b>\n<code>{escape_html(str(e))}</code>",
            parse_mode="HTML",
        )
        return

    try:
        await status_msg.delete()
    except Exception:
        pass

    last_ai_reply[user_id] = final_reply
    # Сохраняем в историю
    history = get_user_history(user_id)
    history.append({"role": "user", "content": user_input})
    history.append({"role": "assistant", "content": final_reply})
    user_histories[user_id] = history
    save_history(user_id, history)

    # Отправляем ответ через стандартный рендер
    parts = parse_response(final_reply)
    last_index = len(parts) - 1
    elapsed = 0
    left = remaining_limit(user_id)
    status_bar = "\n" + fmt_divider() + "\n" + fmt_status_bar(elapsed, False, False, user_id, left)
    for i, part in enumerate(parts):
        is_last = (i == last_index)
        if part["type"] == "text":
            html = md_to_html(part["content"])
            if is_last:
                html += status_bar
            await message.reply_text(
                sanitize_html(html),
                parse_mode=ParseMode.HTML,
                reply_markup=after_reply_keyboard(user_id) if is_last else None,
            )
        elif part["type"] == "code":
            lang = part["lang"]
            code = part["content"]
            header = f"💻 <b>Код</b> <code>[{lang}]</code>" if lang and lang not in ("code","text","") else "💻 <b>Код:</b>"
            safe_code = escape_html(code)
            timing = status_bar if is_last else ""
            kb = after_reply_keyboard(user_id) if is_last else None
            await message.reply_text(
                f"{header}\n<pre><code>{safe_code}</code></pre>{timing}",
                parse_mode=ParseMode.HTML,
                reply_markup=kb,
            )


async def handle_file(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    if MAINTENANCE_MODE and user_id != ADMIN_ID:
        await update.message.reply_text(
            "🔧 <b>Технические работы</b>\n\nБот временно недоступен. Скоро вернёмся! ⏳",
            parse_mode="HTML",
        )
        return
    if is_banned(user_id):
        await update.message.reply_text(fmt_err("Доступ заблокирован"), parse_mode=ParseMode.HTML)
        return
    doc = update.message.document
    if doc.file_size > 500_000:
        await update.message.reply_text(
            fmt_err("Файл слишком большой") + "\n\n🔵 Максимум: <code>500 КБ</code>",
            parse_mode=ParseMode.HTML,
        )
        return
    file     = await context.bot.get_file(doc.file_id)
    filepath = f"{FILES_DIR}/{user_id}_{doc.file_name}"
    await file.download_to_drive(filepath)
    try:
        with open(filepath, "r", encoding="utf-8") as f:
            content = f.read()
    except UnicodeDecodeError:
        await update.message.reply_text(
            fmt_err("Неподдерживаемый формат") + "\n\n🔵 Только текстовые файлы",
            parse_mode=ParseMode.HTML,
        )
        return
    finally:
        os.remove(filepath)
    set_user_file(user_id, doc.file_name, content)
    user_histories[user_id] = []
    save_history(user_id, [])
    caption = update.message.caption
    is_large = len(content) > CHUNK_SIZE
    if caption:
        if is_large:
            # Большой файл — обрабатываем по чанкам
            await process_file_in_chunks(update.message, context, user_id, caption, doc.file_name, content)
        else:
            await update.message.reply_text(
                f"📎 <b>{escape_html(doc.file_name)}</b> загружен!\nОбрабатываю запрос...",
                parse_mode=ParseMode.HTML,
            )
            await send_ai_response(update.message, context, user_id, caption)
    else:
        if is_large:
            await update.message.reply_text(
                f"📎 <b>{escape_html(doc.file_name)}</b> загружен! ({len(content)//1000}КБ)\n\n"
                f"⚠️ Файл большой — будет обработан по частям.\n"
                "Напиши, что с ним сделать.\n"
                "Например: <i>«найди баги»</i> или <i>«объясни код»</i>",
                parse_mode=ParseMode.HTML,
                reply_markup=main_keyboard(user_id),
            )
        else:
            await update.message.reply_text(
                f"📎 <b>{escape_html(doc.file_name)}</b> загружен!\n\n"
                "Напиши, что с ним сделать.\n"
                "Например: <i>«добавь логирование»</i> или <i>«исправь ошибки»</i>",
                parse_mode=ParseMode.HTML,
                reply_markup=main_keyboard(user_id),
            )


# ════════════════════════════════════════════════════
#  ГОЛОСОВОЙ ВВОД
# ════════════════════════════════════════════════════
async def handle_voice(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    if MAINTENANCE_MODE and user_id != ADMIN_ID:
        await update.message.reply_text(
            "🔧 <b>Технические работы</b>\n\nБот временно недоступен. Скоро вернёмся! ⏳",
            parse_mode="HTML",
        )
        return
    if is_banned(user_id):
        await update.message.reply_text(fmt_err("Доступ заблокирован"), parse_mode=ParseMode.HTML)
        return
    voice    = update.message.voice
    wait_msg = await update.message.reply_text("🎤 Распознаю голос...")
    file     = await context.bot.get_file(voice.file_id)
    filepath = f"{FILES_DIR}/{user_id}_voice.ogg"
    await file.download_to_drive(filepath)
    try:
        with open(filepath, "rb") as f:
            transcription = client.audio.transcriptions.create(
                model="whisper-large-v3",
                file=f,
                response_format="text",
            )
        text = transcription.strip() if isinstance(transcription, str) else transcription.text.strip()
    except Exception as e:
        await wait_msg.edit_text(
            fmt_err("Не удалось распознать голос") + f"\n\n<code>{escape_html(str(e))}</code>",
            parse_mode=ParseMode.HTML,
        )
        return
    finally:
        os.remove(filepath)
    await wait_msg.edit_text(
        f"🟢 <b>Распознано:</b> <i>{escape_html(text)}</i>",
        parse_mode=ParseMode.HTML,
    )
    await send_ai_response(update.message, context, user_id, text)


# ════════════════════════════════════════════════════
#  TTS
# ════════════════════════════════════════════════════
async def send_tts(message, user_id):
    reply_text = last_ai_reply.get(user_id)
    if not reply_text:
        await message.reply_text(
            fmt_err("Нет текста для озвучки"),
            parse_mode=ParseMode.HTML,
        )
        return
    clean = re.sub(r'<[^>]+>', '', reply_text)
    max_c = cfg_int("tts_max_chars")
    short = clean[:max_c] + ("..." if len(clean) > max_c else "")
    try:
        tts = gTTS(text=short, lang=CFG["tts_lang"])
        buf = io.BytesIO()
        tts.write_to_fp(buf)
        buf.seek(0)
        buf.name = "response.mp3"
        await message.reply_voice(buf, caption="🔊 Ответ голосом")
    except Exception as e:
        await message.reply_text(
            fmt_err("Ошибка TTS") + f"\n\n<code>{escape_html(str(e))}</code>",
            parse_mode=ParseMode.HTML,
        )


# ════════════════════════════════════════════════════
#  ПРОВЕРКА ЛИМИТОВ GROQ ЧЕРЕЗ ЗАГОЛОВКИ ОТВЕТА
# ════════════════════════════════════════════════════
async def check_groq_limits(api_key: str) -> dict | None:
    """
    Делает минимальный запрос к Groq и читает rate-limit заголовки.
    Возвращает dict с лимитами или None при ошибке.
    """
    try:
        async with httpx.AsyncClient(timeout=15) as http_client:
            resp = await http_client.post(
                "https://api.groq.com/openai/v1/chat/completions",
                headers={
                    "Authorization": f"Bearer {api_key}",
                    "Content-Type": "application/json",
                },
                json={
                    "model": CFG.get("groq_model", "llama-3.1-8b-instant"),
                    "messages": [{"role": "user", "content": "1"}],
                    "max_tokens": 1,
                },
            )
        h = resp.headers
        return {
            "req_limit":      h.get("x-ratelimit-limit-requests", "?"),
            "req_remaining":  h.get("x-ratelimit-remaining-requests", "?"),
            "req_reset":      h.get("x-ratelimit-reset-requests", "?"),
            "tok_limit":      h.get("x-ratelimit-limit-tokens", "?"),
            "tok_remaining":  h.get("x-ratelimit-remaining-tokens", "?"),
            "tok_reset":      h.get("x-ratelimit-reset-tokens", "?"),
            "status":         resp.status_code,
        }
    except Exception as e:
        logger.error(f"check_groq_limits error: {e}")
        return None


# ════════════════════════════════════════════════════
#  ПАРСИНГ ФАЙЛОВ ИЗ ОТВЕТА AI + ZIP
# ════════════════════════════════════════════════════
def extract_files_from_reply(reply: str) -> dict:
    """
    Парсит ответ AI и возвращает dict {filename: code}.
    Ищет имя файла в до 5 строках перед блоком кода или в первой строке-комментарии.
    """
    files = {}
    lines = reply.split('\n')
    i = 0
    code_blocks = []
    while i < len(lines):
        # Начало блока кода?
        if lines[i].startswith('```'):
            lang = lines[i][3:].strip()
            # Собираем до 5 предыдущих строк для поиска имени файла
            prev_lines = [lines[j].strip() for j in range(max(0, i - 5), i)]
            code_lines = []
            i += 1
            while i < len(lines) and not lines[i].startswith('```'):
                code_lines.append(lines[i])
                i += 1
            code = '\n'.join(code_lines).strip()
            code_blocks.append({'lang': lang, 'code': code, 'prev_lines': prev_lines})
        i += 1

    ext_map = {
        'php': '.php', 'python': '.py', 'py': '.py',
        'javascript': '.js', 'js': '.js', 'typescript': '.ts',
        'html': '.html', 'css': '.css', 'sql': '.sql',
        'bash': '.sh', 'sh': '.sh', 'json': '.json',
        'xml': '.xml', 'yaml': '.yaml', 'cpp': '.cpp',
        'c': '.c', 'java': '.java', 'go': '.go', 'rust': '.rs',
    }

    for idx, block in enumerate(code_blocks):
        lang = block['lang'].lower()
        code = block['code']
        prev_lines = block['prev_lines']

        # Ищем имя файла в предыдущих строках (снизу вверх, ближайшие первыми)
        fname = None
        for prev in reversed(prev_lines):
            # Убираем markdown-разметку: **, *, #, `
            clean = re.sub(r'[*#`]', '', prev).strip()
            m = re.search(r'([\w\-]+\.\w{1,6})', clean)
            if m:
                fname = m.group(1)
                break

        if not fname:
            # Ищем в первой строке кода (комментарий)
            first = code.split('\n')[0] if code else ''
            m2 = re.search(r'([\w\-]+\.\w{1,6})', first)
            if m2:
                fname = m2.group(1)
            else:
                ext = ext_map.get(lang, '.txt')
                fname = f'file{idx+1}{ext}'

        # Избегаем дублей
        if fname in files:
            base, ext = fname.rsplit('.', 1) if '.' in fname else (fname, 'txt')
            fname = f'{base}_{idx+1}.{ext}'
        files[fname] = code

    return files


def create_zip_from_files(files: dict, zip_path: str):
    """Создаёт zip-архив из dict {filename: code}."""
    with zipfile.ZipFile(zip_path, 'w', zipfile.ZIP_DEFLATED) as zf:
        for fname, code in files.items():
            zf.writestr(fname, code)


# Хранилище: последние распаршенные файлы по user_id
_last_code_files: dict = {}


# ════════════════════════════════════════════════════
#  ОТПРАВКА ОТВЕТА AI
# ════════════════════════════════════════════════════
async def send_ai_response(message, context, user_id, user_input, bypass_cache=False):
    if not check_rate_limit(user_id):
        wait = rate_limit_wait(user_id)
        await message.reply_text(
            fmt_message(
                "🟡 Подожди!",
                f"Лимит запросов: <code>{cfg_int('rate_limit_per_minute')}/мин</code>",
                f"🔵 Попробуй через <code>{wait} сек</code>"
            ),
            parse_mode=ParseMode.HTML,
        )
        return

    if not has_limit(user_id):
        await message.reply_text(
            fmt_message(
                "🔴 Лимит исчерпан",
                "Бесплатный лимит символов исчерпан",
                "💎 Купи Premium для безлимитного доступа"
            ),
            parse_mode=ParseMode.HTML,
            reply_markup=main_keyboard(user_id),
        )
        return

    history   = get_user_history(user_id)
    user_file = get_user_file(user_id)

    # ── Веб-поиск (если нужен) ──────────────────────
    search_context = ""
    search_tag = ""
    if needs_web_search(user_input) and not bypass_cache:
        if not has_search_limit(user_id):
            left_s = remaining_search_limit(user_id)
            await message.reply_text(
                f"{fmt_err('Поиск недоступен')}\n\n"
                f"🔵 Лимит: <code>{cfg_int('default_search_limit')}</code> запросов\n"
                f"💎 Premium → безлимит",
                parse_mode=ParseMode.HTML,
                reply_markup=main_keyboard(user_id),
            )
            return
        search_tag = " 🔍"
        wait_msg = await message.reply_text("🔍 Ищу в интернете...")
        search_context = await web_search(user_input, bot=context.bot)
        consume_search_limit(user_id)
        try:
            await wait_msg.delete()
        except Exception:
            pass

    # ⚙️ Загружаем настройки пользователя
    settings = get_user_settings(user_id)
    response_style = settings.get("response_style", "detailed")
    personality = settings.get("bot_personality", "friendly")
    
    system_msg = (
        "Ты — Cicada AI, AI-ассистент для разработчиков. "
        "Пишешь чистый код. Объясняешь понятно. "
        "Отвечаешь на русском, если не попросят иначе. "
        "Отвечай КРАТКО и по делу — без вводных фраз вроде 'Конечно!', 'Отличный вопрос!', 'Привет!'. "
        "Не повторяй вопрос пользователя. Сразу давай ответ. "
        "Код — в блоках ``` с указанием языка. "
        "Если ответ короткий — так и оставь, не растягивай. "
        f"{get_response_style_text(response_style)} "
        f"{get_personality_text(personality)}"
    )

    if search_context:
        system_msg += (
            f"\n\nРезультаты веб-поиска по запросу пользователя:\n\n"
            f"{search_context}\n\n"
            "Используй эти данные для ответа. Ссылки можно упомянуть."
        )

    if user_file:
        max_fc = cfg_int("max_file_chars")
        file_content = user_file["content"]
        truncated = len(file_content) > max_fc
        snippet = file_content[:max_fc]
        trunc_note = f"\n[⚠️ Файл обрезан: показано {max_fc} из {len(file_content)} символов]" if truncated else ""
        system_msg += (
            f"\n\nПользователь загрузил файл «{user_file['filename']}»:{trunc_note}\n\n"
            f"```\n{snippet}\n```\n"
            "Работай с этим файлом по запросу пользователя. "
            "Верни полный изменённый код в блоке ```."
        )

    api_messages = [{"role": "system", "content": system_msg}]
    max_hist = cfg_int("max_history_messages")
    api_messages += history[-max_hist:]
    api_messages.append({"role": "user", "content": user_input})

    from_cache = False
    reply      = None

    if not bypass_cache:
        reply = get_cached(api_messages)
        if reply:
            from_cache = True

    start_t = time.time()

    # ⚡ Анимированный прогресс-бар пока AI думает
    loading_msg = None
    stop_anim   = asyncio.Event()

    async def _animate(msg):
        """Обновляет сообщение с прогрессом пока не выставлен stop_anim."""
        frames = [
            ("⏳ Обрабатываю...", 0),
            ("⏳ Обрабатываю...", 28),
            ("⏳ Обрабатываю...", 57),
            ("⏳ Обрабатываю...", 85),
        ]
        i = 0
        while not stop_anim.is_set():
            title, pct = frames[i % len(frames)]
            try:
                await msg.edit_text(
                    f"{title}\n{loading_bar(pct)}",
                    parse_mode=ParseMode.HTML,
                )
            except Exception:
                pass
            i += 1
            await asyncio.sleep(0.9)

    if not from_cache:
        loading_msg = await message.reply_text(
            f"⏳ Обрабатываю...\n{loading_bar(0)}",
            parse_mode=ParseMode.HTML,
        )
        anim_task = asyncio.create_task(_animate(loading_msg))

    if not from_cache:
        await compress_history(user_id)
        try:
            # ── Роутинг: Ollama (код) или Groq (всё остальное) ──
            use_local = needs_local_model(user_input)
            reply = None

            if use_local:
                logger.info(f"[{user_id}] → Ollama ({OLLAMA_MODEL})")
                reply = await call_ollama(api_messages)
                if reply is None:
                    logger.warning(f"[{user_id}] Ollama не ответила → Groq")

            if reply is None:
                # Groq — ротация ключей + retry
                loop = asyncio.get_running_loop()
                last_exc = None
                for _attempt in range(len(_GROQ_KEYS) or 1):
                    _client_groq = _get_groq_client()  # FIX: клиент создаётся при каждой попытке
                    def _call_groq(_c=_client_groq):
                        return _c.chat.completions.create(
                            model=CFG["groq_model"],
                            messages=api_messages,
                            max_tokens=4096,
                        )
                    try:
                        chat = await loop.run_in_executor(None, _call_groq)
                        reply = chat.choices[0].message.content.strip()
                        last_exc = None
                        break
                    except Exception as _e:
                        last_exc = _e
                        err_str = str(_e)
                        wait = 15 if "429" in err_str or "rate_limit" in err_str.lower() else 2
                        logger.warning(f"[{user_id}] Groq ключ {_attempt+1} ошибка: {_e}, ждём {wait}с")
                        await asyncio.sleep(wait)
                if last_exc is not None:
                    raise last_exc
                g_today, _ = increment_groq_counter()
                asyncio.create_task(check_and_notify_limits("groq", g_today, context.bot))

            set_cached(api_messages, reply)
        except Exception as e:
            stop_anim.set()
            if loading_msg:
                try: await loading_msg.delete()
                except Exception: pass
            err = str(e)
            if "rate_limit" in err.lower():
                await message.reply_text(
                    f"{fmt_warn('Cicada-AI перегружен')}\n\n"
                    f"🔵 Подожди немного и повтори запрос",
                    parse_mode=ParseMode.HTML,
                    reply_markup=retry_error_keyboard(),
                )
            else:
                await message.reply_text(
                    f"{fmt_err('Ошибка API')}\n\n"
                    f"<code>{escape_html(err)}</code>",
                    parse_mode=ParseMode.HTML,
                    reply_markup=retry_error_keyboard(),
                )
            return
        finally:
            stop_anim.set()
            if loading_msg:
                # Показываем 100% перед удалением
                try:
                    await loading_msg.edit_text(
                        f"✅ Готово\n{loading_bar(100)}",
                        parse_mode=ParseMode.HTML,
                    )
                    await asyncio.sleep(0.3)
                    await loading_msg.delete()
                except Exception:
                    pass

    elapsed = round(time.time() - start_t, 1)
    history.append({"role": "user",      "content": user_input})
    history.append({"role": "assistant", "content": reply})
    user_histories[user_id] = history
    save_history(user_id, history)
    last_ai_reply[user_id] = reply
    _chars_used = len(user_input) + len(reply)
    consume_limit(user_id, _chars_used)
    
    # 💬 Сохраняем в систему чатов
    chat_id = get_current_chat_id(user_id)
    save_chat_message(chat_id, user_id, "user", user_input)
    # Оцениваем токены примерно (1 токен ≈ 4 символа)
    estimated_tokens = len(reply) // 4
    save_chat_message(chat_id, user_id, "assistant", reply, estimated_tokens)
    
    # 📊 Обновляем статистику
    increment_user_stats(user_id, messages=2, tokens=estimated_tokens)
    update_longest_chat(user_id, len(history))

    if user_file:
        code_blocks = re.findall(r'```\w*\n(.*?)```', reply, re.DOTALL)
        if code_blocks:
            new_content = max(code_blocks, key=len).strip()
            set_user_file(user_id, user_file["filename"], new_content)

    left = remaining_limit(user_id)
    if user_id == ADMIN_ID or is_premium(user_id):
        limit_tag = ""   # будет внутри fmt_status_bar
    else:
        limit_tag = ""   # тоже там

    status_bar = "\n" + fmt_divider() + "\n" + fmt_status_bar(
        elapsed, from_cache, bool(search_tag), user_id, left
    )

    parts      = parse_response(reply)
    last_index = len(parts) - 1
    cache_tag  = ""   # теперь всё в status_bar
    # search_tag уже определён выше (пустая строка или " 🔍")

    # Парсим файлы из ответа для архива
    _parsed_files = extract_files_from_reply(reply)
    if _parsed_files:
        _last_code_files[user_id] = _parsed_files

    # Определяем режим визуала для первого текстового блока
    def _get_text_header(content: str, part_index: int) -> str:
        """Возвращает заголовок в зависимости от типа ответа."""
        if part_index != 0:
            return ""
        c = content.strip()
        # Короткий ответ (≤ 280 символов и нет переносов строк как абзацев)
        if len(c) <= 280 and c.count("\n\n") == 0:
            return "📌 <b>Коротко:</b>\n"
        # Ответ содержит объяснение (ключевые слова)
        lower = c.lower()
        explain_kw = ("потому что", "это значит", "имеется в виду", "объяснение",
                      "суть в том", "проще говоря", "иными словами", "то есть")
        if any(k in lower for k in explain_kw):
            return "📖 <b>Объяснение:</b>\n"
        # Стандартный ответ
        return "💬 <b>Cicada AI:</b>\n"

    for i, part in enumerate(parts):
        is_last = (i == last_index)
        if part["type"] == "text":
            prefix = _get_text_header(part["content"], i)
            html   = prefix + md_to_html(part["content"])
            if is_last:
                html += status_bar
            chunks = [html[j:j+4000] for j in range(0, len(html), 4000)]
            for k, chunk in enumerate(chunks):
                is_last_chunk = is_last and (k == len(chunks) - 1)
                await message.reply_text(
                    sanitize_html(chunk),
                    parse_mode=ParseMode.HTML,
                    reply_markup=after_reply_keyboard(user_id) if is_last_chunk else None,
                )
        elif part["type"] == "code":
            lang      = part["lang"]
            code      = part["content"]
            # Определяем имя файла для этого блока кода
            block_idx = i  # индекс блока
            parsed_fnames = list(_last_code_files.get(user_id, {}).keys())
            # Считаем порядковый номер среди code-блоков
            code_block_num = sum(1 for p in parts[:i] if p["type"] == "code")
            if code_block_num < len(parsed_fnames):
                fname_label = parsed_fnames[code_block_num]
                header = f"💻 <b>Код</b> <code>[{fname_label}]</code>"
            elif lang and lang not in ("code", "text", ""):
                header = f"💻 <b>Код</b> <code>[{lang}]</code>"
            else:
                header = "💻 <b>Код:</b>"
            safe_code = escape_html(code)
            chunks    = [safe_code[j:j+3900] for j in range(0, len(safe_code), 3900)]
            for k, chunk in enumerate(chunks):
                is_last_chunk = is_last and (k == len(chunks) - 1)
                kb     = None
                timing = ""
                if is_last_chunk:
                    kb     = file_keyboard() if user_file else after_reply_keyboard(user_id)
                    timing = status_bar
                await message.reply_text(
                    f"{header}\n<pre><code>{chunk}</code></pre>{timing}",
                    parse_mode=ParseMode.HTML,
                    reply_markup=kb,
                )


# ════════════════════════════════════════════════════
#  ТЕКСТОВЫЕ СООБЩЕНИЯ
# ════════════════════════════════════════════════════
# ════════════════════════════════════════════════════
#  ОБНОВЛЕНИЕ .ENV ФАЙЛА
# ════════════════════════════════════════════════════
def _update_env(key: str, value: str):
    """Обновляем или добавляем переменную в .env файл."""
    lines = []
    found = False
    if os.path.exists(ENV_FILE):
        with open(ENV_FILE, "r", encoding="utf-8") as f:
            lines = f.readlines()
    new_lines = []
    for line in lines:
        if line.startswith(f"{key}="):
            new_lines.append(f"{key}={value}\n")
            found = True
        else:
            new_lines.append(line)
    if not found:
        new_lines.append(f"{key}={value}\n")
    with open(ENV_FILE, "w", encoding="utf-8") as f:
        f.writelines(new_lines)


async def handle_message(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    update_user(user_id,
                username=update.effective_user.username or "",
                first_name=update.effective_user.first_name or "")
    if MAINTENANCE_MODE and user_id != ADMIN_ID:
        await update.message.reply_text(
            "🔧 <b>Технические работы</b>\n\nБот временно недоступен. Скоро вернёмся! ⏳",
            parse_mode=ParseMode.HTML,
        )
        return
    if is_banned(user_id):
        await update.message.reply_text(fmt_err("Доступ заблокирован"), parse_mode=ParseMode.HTML)
        return
    if context.user_data.get("awaiting_price"):
        plan = context.user_data.pop("awaiting_price")
        text = update.message.text.strip()
        try:
            val = float(text)
            if val <= 0:
                raise ValueError
            CFG[f"price_{plan}"] = str(val)
            _config_set(f"price_{plan}", str(val))
            # Формируем название периода
            if plan.endswith("month"):
                months = plan.replace("month", "")
                period_name = f"{months} мес"
            else:
                period_name = PLAN_LABELS.get(plan, plan)
            await update.message.reply_text(
                f"✅ Цена за <b>{period_name}</b> изменена на <b>${val}</b>",
                parse_mode=ParseMode.HTML,
                reply_markup=admin_prices_keyboard(),
            )
        except ValueError:
            await update.message.reply_text(
                "❌ Неверный формат. Введи число, например: <code>4.5</code>",
                parse_mode=ParseMode.HTML,
            )
        return

    # Обработка ввода токенов и порогов
    awaiting = context.user_data.get("awaiting_input")
    if awaiting and user_id == ADMIN_ID:
        context.user_data.pop("awaiting_input")
        text = update.message.text.strip()

        if awaiting == "groq_token_input":
            global GROQ_TOKEN, client, _GROQ_KEYS, _groq_key_index
            GROQ_TOKEN = text
            # Обновляем .env
            _update_env("GROQ_TOKEN", text)
            client = Groq(api_key=GROQ_TOKEN)
            _GROQ_KEYS = [k for k in [GROQ_TOKEN, GROQ_TOKEN_2, GROQ_TOKEN_3] if k]
            _groq_key_index = 0
            await update.message.reply_text(
                f"✅ <b>Groq токен обновлён!</b>\n\nТокен: <code>...{text[-6:]}</code>\n\n"
                f"Нажми кнопку ниже чтобы перезапустить бота:",
                parse_mode=ParseMode.HTML,
                reply_markup=InlineKeyboardMarkup([
                    [InlineKeyboardButton("🔄 Перезапустить бот", callback_data="admin_restart_bot")],
                    [InlineKeyboardButton("◀️ Назад к токенам",   callback_data="admin_tokens")],
                ]),
            )

        elif awaiting == "tavily_token_input":
            global TAVILY_TOKEN
            TAVILY_TOKEN = text
            _update_env("TAVILY_TOKEN", text)
            await update.message.reply_text(
                f"✅ <b>Tavily токен обновлён!</b>\n\nТокен: <code>...{text[-6:]}</code>\n\n"
                f"Нажми кнопку ниже чтобы перезапустить бота:",
                parse_mode=ParseMode.HTML,
                reply_markup=InlineKeyboardMarkup([
                    [InlineKeyboardButton("🔄 Перезапустить бот", callback_data="admin_restart_bot")],
                    [InlineKeyboardButton("◀️ Назад к токенам",   callback_data="admin_tokens")],
                ]),
            )

        elif awaiting == "bot_token_input":
            global BOT_TOKEN
            BOT_TOKEN = text
            _update_env("BOT_TOKEN", text)
            await update.message.reply_text(
                f"✅ <b>Bot токен обновлён!</b>\n\nТокен: <code>...{text[-6:]}</code>\n\n"
                f"🔄 Перезапускаю бота...",
                parse_mode=ParseMode.HTML,
            )
            await asyncio.sleep(2)
            os.execv(sys.executable, [sys.executable] + sys.argv)

        elif awaiting == "groq_threshold_input":
            try:
                val = int(text)
                if val <= 0:
                    raise ValueError
                CFG["groq_alert_threshold"] = str(val)
                CFG["groq_alert_sent"] = "0"
                _config_set("groq_alert_threshold", str(val))
                _config_set("groq_alert_sent", "0")
                await update.message.reply_text(
                    f"✅ Порог уведомлений Groq установлен: <b>{val}</b> запросов/день",
                    parse_mode=ParseMode.HTML,
                    reply_markup=admin_alert_threshold_keyboard(),
                )
            except ValueError:
                await update.message.reply_text("❌ Введи целое число, например: <code>800</code>", parse_mode=ParseMode.HTML)

        elif awaiting == "tavily_threshold_input":
            try:
                val = int(text)
                if val <= 0:
                    raise ValueError
                CFG["tavily_alert_threshold"] = str(val)
                CFG["tavily_alert_sent"] = "0"
                _config_set("tavily_alert_threshold", str(val))
                _config_set("tavily_alert_sent", "0")
                await update.message.reply_text(
                    f"✅ Порог уведомлений Tavily установлен: <b>{val}</b> запросов/день",
                    parse_mode=ParseMode.HTML,
                    reply_markup=admin_alert_threshold_keyboard(),
                )
            except ValueError:
                await update.message.reply_text("❌ Введи целое число, например: <code>800</code>", parse_mode=ParseMode.HTML)
        return

    # 🧠 Переименование чата
    awaiting_rename = context.user_data.get("awaiting_chat_rename")
    if awaiting_rename:
        context.user_data.pop("awaiting_chat_rename")
        new_name = update.message.text.strip()
        if new_name:
            rename_chat(awaiting_rename, new_name)
            await update.message.reply_text(
                f"✅ Чат переименован в: <b>{escape_html(new_name)}</b>",
                parse_mode=ParseMode.HTML,
                reply_markup=InlineKeyboardMarkup([
                    [InlineKeyboardButton("◀️ Назад к чату", callback_data=f"chat_menu_{awaiting_rename}")],
                    [InlineKeyboardButton("🏠 Главное меню", callback_data="back_menu")],
                ]),
            )
        else:
            await update.message.reply_text(
                "❌ Имя не может быть пустым",
                reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("◀️ Назад", callback_data=f"chat_menu_{awaiting_rename}")]]),
            )
        return

    # 🎁 Промокод
    if context.user_data.get("awaiting_promo"):
        context.user_data.pop("awaiting_promo")
        promo = update.message.text.strip().upper()
        # Пока просто заглушка
        await update.message.reply_text(
            f"🎁 Промокод <code>{escape_html(promo)}</code>\n\n"
            f"<i>Промокоды в разработке... Скоро будет работать!</i>",
            parse_mode=ParseMode.HTML,
            reply_markup=subscription_menu_keyboard(),
        )
        return

    # 🆘 Поддержка — сообщение от пользователя
    if context.user_data.get("awaiting_support"):
        context.user_data.pop("awaiting_support")
        support_text = update.message.text.strip()
        u = get_user(user_id)
        name = u.get("first_name") or u.get("username") or str(user_id)
        try:
            from telegram.ext import ContextTypes as _CT
            await update.get_bot().send_message(
                chat_id=ADMIN_ID,
                text=(
                    f"🆘 <b>Обращение в поддержку</b>\n\n"
                    f"👤 {escape_html(name)} (ID: <code>{user_id}</code>)\n\n"
                    f"📝 {escape_html(support_text)}"
                ),
                parse_mode=ParseMode.HTML,
            )
        except Exception as e:
            logger.error(f"Ошибка отправки в поддержку: {e}")
        await update.message.reply_text(
            "🆘 <b>Сообщение отправлено!</b>\n\nМы постараемся помочь как можно скорее. 🤝",
            parse_mode=ParseMode.HTML,
            reply_markup=about_menu_keyboard(),
        )
        return

    # 🛠 Инструменты — обработка ввода текста для инструментов
    awaiting_tool = context.user_data.get("awaiting_tool")
    if awaiting_tool:
        context.user_data.pop("awaiting_tool")
        text = update.message.text.strip()
        tool_prompts = {
            "rewrite":   f"Перепиши следующий текст по-новому, сохрани смысл но измени формулировки:\n\n{text}",
            "summarize": f"Сделай краткое резюме следующего текста в 3-5 предложениях:\n\n{text}",
            "tts_text":  None,  # Обработаем отдельно
        }
        if awaiting_tool.startswith("translate_"):
            lang_map = {"en": "английский", "de": "немецкий", "fr": "французский", "es": "испанский", "zh": "китайский"}
            lang = awaiting_tool.replace("translate_", "")
            prompt = f"Переведи следующий текст на {lang_map.get(lang, lang)} язык:\n\n{text}"
        elif awaiting_tool.startswith("codegen_"):
            lang = awaiting_tool.replace("codegen_", "")
            prompt = f"Напиши код на {lang.upper()} для следующей задачи:\n\n{text}"
        elif awaiting_tool == "tts_text":
            # Голосовое озвучивание через gTTS
            last_ai_reply[user_id] = text
            await send_tts(update.message, user_id)
            return
        else:
            prompt = tool_prompts.get(awaiting_tool, text)
        await send_ai_response(update.message, context, user_id, prompt)
        return

    # 🔥 Проверка на мало оставшихся запросов
    low_limit = check_low_limit(user_id)
    if low_limit is not None:
        # Отправляем предупреждение
        await update.message.reply_text(
            f"⚠️ <b>Внимание!</b>\n\n"
            f"Осталось: <b>{low_limit//1000}К символов</b>\n\n"
            f"💎 <b>Premium:</b>\n"
            f"1 мес — ${cfg_float('price_1month')}\n"
            f"3 мес — ${cfg_float('price_3month')}\n"
            f"5 мес — ${cfg_float('price_5month')}\n"
            f"7 мес — ${cfg_float('price_7month')}",
            parse_mode=ParseMode.HTML,
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("💎 Апгрейд", callback_data="subscription_menu")],
                [InlineKeyboardButton("◀️ Продолжить", callback_data="dismiss_warning")],
            ]),
        )
        # Всё равно обрабатываем сообщение дальше

    text = update.message.text
    user_file = get_user_file(user_id)
    if user_file and len(user_file.get("content", "")) > CHUNK_SIZE:
        # Большой файл — обрабатываем по чанкам
        await process_file_in_chunks(
            update.message, context, user_id,
            text, user_file["filename"], user_file["content"]
        )
    else:
        await send_ai_response(update.message, context, user_id, text)


# ════════════════════════════════════════════════════
#  ОБРАБОТКА КНОПОК
# ════════════════════════════════════════════════════
async def button_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query   = update.callback_query
    user_id = query.from_user.id
    data    = query.data

    # Вспомогательная функция — отвечает ровно один раз
    _answered = False
    async def answer(text: str = "", show_alert: bool = False):
        nonlocal _answered
        if _answered:
            return
        _answered = True
        try:
            await query.answer(text, show_alert=show_alert)
        except Exception:
            pass

    if MAINTENANCE_MODE and user_id != ADMIN_ID:
        await answer("🔧 Технические работы. Бот временно недоступен.", show_alert=True)
        return


    # Скрытие предупреждения о лимите
    if data == "dismiss_warning":
        await query.edit_message_text(
            "🤖 <b>Cicada AI</b>\n\n"
            "Продолжай использовать бота! 💪",
            parse_mode=ParseMode.HTML,
            reply_markup=main_keyboard(user_id),
        )
        return

    if data == "clear":
        await query.edit_message_text(
            "⚠️ Очистить историю диалога?",
            reply_markup=confirm_clear_keyboard(),
        )

    elif data == "confirm_clear":
        user_histories[user_id] = []
        save_history(user_id, [])
        await query.edit_message_text("🗑 История очищена!", reply_markup=main_keyboard(user_id))

    elif data == "retry":
        history = get_user_history(user_id)
        if len(history) >= 2:
            last_user = history[-2]["content"]
            history.pop(); history.pop()
            save_history(user_id, history)
            await query.edit_message_text("🔄 Повторяю запрос...")
            await send_ai_response(query.message, context, user_id, last_user, bypass_cache=True)
        else:
            await answer("❌ Нет сообщений для повтора", show_alert=True)

    elif data == "simplify_last":
        """Упростить последний ответ."""
        history = get_user_history(user_id)
        if not history or len(history) < 1:
            await answer("❌ Нет ответа для упрощения", show_alert=True)
            return
        last_reply = history[-1]["content"] if history[-1]["role"] == "assistant" else None
        if not last_reply:
            await answer("❌ Нет ответа AI", show_alert=True)
            return
        await query.edit_message_text("✏️ <b>Упрощаю...</b>", parse_mode=ParseMode.HTML)
        prompt = f"Упрости и объясни проще:\n\n{last_reply}"
        await send_ai_response(query.message, context, user_id, prompt, bypass_cache=True)

    elif data == "explain_last":
        """Объяснить подробнее последний ответ."""
        history = get_user_history(user_id)
        if not history or len(history) < 1:
            await answer("❌ Нет ответа для объяснения", show_alert=True)
            return
        last_reply = history[-1]["content"] if history[-1]["role"] == "assistant" else None
        if not last_reply:
            await answer("❌ Нет ответа AI", show_alert=True)
            return
        await query.edit_message_text("📖 <b>Объясняю подробнее...</b>", parse_mode=ParseMode.HTML)
        prompt = f"Объясни подробнее и развернуто:\n\n{last_reply}"
        await send_ai_response(query.message, context, user_id, prompt, bypass_cache=True)

    elif data == "code_last":
        """Показать только код из последнего ответа."""
        history = get_user_history(user_id)
        if not history or len(history) < 1:
            await answer("❌ Нет ответа", show_alert=True)
            return
        last_reply = history[-1]["content"] if history[-1]["role"] == "assistant" else None
        if not last_reply:
            await answer("❌ Нет ответа AI", show_alert=True)
            return
        await query.edit_message_text("💻 <b>Выделяю код...</b>", parse_mode=ParseMode.HTML)
        prompt = f"Покажи только код из этого ответа, без объяснений:\n\n{last_reply}"
        await send_ai_response(query.message, context, user_id, prompt, bypass_cache=True)

    elif data == "tts":
        await send_tts(query.message, user_id)

    elif data == "export_menu":
        await query.edit_message_text("📤 Выбери формат:", reply_markup=export_keyboard())

    elif data == "export_txt":
        filename = export_history(user_id, "txt")
        await query.message.reply_document(open(filename, "rb"))
        await answer("✅ Экспортировано!")
        os.remove(filename)

    elif data == "export_md":
        filename = export_history(user_id, "md")
        await query.message.reply_document(open(filename, "rb"))
        await answer("✅ Экспортировано!")
        os.remove(filename)

    elif data == "stats":
        history   = get_user_history(user_id)
        user_msgs = sum(1 for m in history if m["role"] == "user")
        ai_msgs   = sum(1 for m in history if m["role"] == "assistant")
        file_info = ""
        if get_user_file(user_id):
            f = get_user_file(user_id)
            file_info = f"\n📎 Загружен файл: <b>{escape_html(f['filename'])}</b>"
        await query.edit_message_text(
            f"📊 <b>Статистика чата</b>\n\n"
            f"👤 Твоих сообщений: {user_msgs}\n"
            f"🤖 Ответов AI: {ai_msgs}\n"
            f"📝 Всего: {len(history)}\n"
            f"💾 Записей в кэше: {len(_response_cache)}"
            f"{file_info}",
            parse_mode=ParseMode.HTML,
            reply_markup=main_keyboard(user_id),
        )

    elif data == "clear_file":
        clear_user_file(user_id)
        await answer("✅ Файл удалён", show_alert=True)
        await query.edit_message_reply_markup(reply_markup=main_keyboard(user_id))

    elif data == "download_file":
        f = get_user_file(user_id)
        if f:
            filepath = f"{FILES_DIR}/output_{user_id}_{f['filename']}"
            with open(filepath, "w", encoding="utf-8") as file:
                file.write(f["content"])
            await query.message.reply_document(
                open(filepath, "rb"),
                filename=f["filename"],
                caption=f"📎 {f['filename']}",
            )
            os.remove(filepath)

    elif data == "download_zip":
        files = _last_code_files.get(user_id)
        if not files:
            await answer("❌ Нет файлов для архива", show_alert=True)
            return
        zip_path = f"{FILES_DIR}/code_{user_id}.zip"
        try:
            create_zip_from_files(files, zip_path)
            fnames_list = "\n".join(f"• {fn}" for fn in files.keys())
            await query.message.reply_document(
                open(zip_path, "rb"),
                filename="code.zip",
                caption=f"📦 <b>Архив с кодом</b>\n\n{fnames_list}",
                parse_mode=ParseMode.HTML,
            )
            await answer("✅ Архив отправлен!")
        except Exception as e:
            await answer(f"❌ Ошибка: {e}", show_alert=True)
        finally:
            if os.path.exists(zip_path):
                os.remove(zip_path)

    elif data == "help":
        await query.edit_message_text(
            fmt_message(
                "🤖 Cicada AI — Помощь",
                "Основные команды и возможности",
                "🗑 Очистить — удалить историю\n"
                "🔄 Повторить — повторить запрос\n"
                "📤 Экспорт — сохранить чат\n"
                "📊 Кабинет — лимиты и Premium\n"
                "🔊 Озвучить — голосом\n\n"
                f"{fmt_divider()}\n\n"
                "📎 Отправь файл для редактирования\n"
                "🎤 Голосовые команды поддерживаются\n"
                "🔍 Веб-поиск: «найди», «github»\n\n"
                f"{fmt_divider()}\n\n"
                "🎁 Триал: <b>50 000</b> символов\n"
                "💎 Premium: <b>безлимит</b>"
            ),
            parse_mode=ParseMode.HTML,
            reply_markup=main_keyboard(user_id),
        )

    elif data == "back_menu":
        await query.edit_message_text(
            fmt_message(
                "🤖 Cicada AI",
                "Готов к работе",
                "Напиши задачу или выбери раздел ниже"
            ),
            parse_mode=ParseMode.HTML,
            reply_markup=main_keyboard(user_id),
        )

    elif data == "my_cabinet":
        u    = get_user(user_id)
        left = remaining_limit(user_id)
        name = escape_html(u.get("first_name") or u.get("username") or str(user_id))
        hist = get_user_history(user_id)
        compressed = any(
            m.get("role") == "system" and "[Сжатая история]" in m.get("content", "")
            for m in hist
        )
        comp_tag = "\n🗜 История сжата (резюме)" if compressed else ""
        if is_premium(user_id) and user_id != ADMIN_ID:
            until = u.get("premium_until", "")
            try:
                exp = datetime.fromisoformat(until).strftime("%d.%m.%Y %H:%M")
            except Exception:
                exp = until
            status_line = f"💎 <b>Premium</b> до {exp}\n♾ Безлимитный доступ"
        else:
            lim = u.get("user_limit", u.get("limit", 50))
            sleft = remaining_search_limit(user_id)
            slim  = cfg_int("default_search_limit")
            status_line = (
                f"🎁 Триал: <b>{left}/{lim}</b> запросов\n"
                f"🔍 Поиск: <b>{sleft}/{slim}</b> запросов\n"
                f"📨 Использовано: {u['used']}"
            )
        await query.edit_message_text(
            f"👤 <b>Мой кабинет</b>\n\n"
            f"Имя: <b>{name}</b>\n"
            f"ID: <code>{user_id}</code>\n"
            f"Дата регистрации: {u.get('joined', '—')}\n\n"
            f"{status_line}\n"
            f"📝 Сообщений в истории: {len(hist)}"
            f"{comp_tag}",
            parse_mode=ParseMode.HTML,
            reply_markup=cabinet_keyboard(user_id),
        )

    # ════════════════════════════════════════════════════
    #  🧠 МУЛЬТИ-ЧАТЫ — обработчики
    # ════════════════════════════════════════════════════
    elif data == "my_chats":
        """Главное меню раздела: Новый чат / Мои чаты / Удалить чат."""
        await query.edit_message_text(
            "🧠 <b>Мои чаты</b>\n\nВыбери действие:",
            parse_mode=ParseMode.HTML,
            reply_markup=my_chats_menu_keyboard(),
        )

    elif data == "chats_list":
        """Список чатов — нажатие открывает меню действий чата."""
        chats = get_user_chats(user_id)
        current_chat_id = get_current_chat_id(user_id)
        if not chats:
            create_chat(user_id, "Новый чат")
            chats = get_user_chats(user_id)
        await query.edit_message_text(
            "💬 <b>Мои чаты</b>\n\n▶️ — активный чат\nНажми на чат для управления:",
            parse_mode=ParseMode.HTML,
            reply_markup=chats_list_keyboard(user_id, chats, current_chat_id),
        )

    elif data == "create_chat":
        """Создаёт новый чат и возвращает в главное меню раздела."""
        create_chat(user_id, f"Чат {len(get_user_chats(user_id)) + 1}")
        user_histories[user_id] = []
        save_history(user_id, [])
        await answer("✅ Новый чат создан!", show_alert=True)
        await query.edit_message_text(
            "🧠 <b>Мои чаты</b>\n\nВыбери действие:",
            parse_mode=ParseMode.HTML,
            reply_markup=my_chats_menu_keyboard(),
        )

    elif data.startswith("chat_menu_"):
        """Нажали на конкретный чат — показываем меню: Переименовать / Экспортировать / Удалить."""
        chat_id = int(data.replace("chat_menu_", ""))
        chat = get_chat(chat_id)
        if not chat or chat["user_id"] != user_id:
            await answer("❌ Чат не найден", show_alert=True)
            return
        # Переключаемся на этот чат
        if switch_chat(user_id, chat_id):
            messages = load_chat_messages(chat_id)
            user_histories[user_id] = messages
        count = chat.get("message_count", 0)
        await query.edit_message_text(
            f"💬 <b>{escape_html(chat['name'])}</b>\n\n"
            f"📝 Сообщений: <b>{count}</b>\n"
            f"📅 Создан: {chat.get('created_at', '—')[:10]}\n\n"
            f"Выбери действие:",
            parse_mode=ParseMode.HTML,
            reply_markup=chat_actions_keyboard(chat_id),
        )

    elif data.startswith("switch_chat_"):
        """Legacy: переключение чата."""
        chat_id = int(data.replace("switch_chat_", ""))
        if switch_chat(user_id, chat_id):
            messages = load_chat_messages(chat_id)
            user_histories[user_id] = messages
            chat = get_chat(chat_id)
            await answer(f"✅ Переключено: {chat['name']}", show_alert=True)
        else:
            await answer("❌ Чат не найден", show_alert=True)
        chats = get_user_chats(user_id)
        await query.edit_message_text(
            "💬 <b>Мои чаты</b>\n\n▶️ — активный чат\nНажми на чат для управления:",
            parse_mode=ParseMode.HTML,
            reply_markup=chats_list_keyboard(user_id, chats, chat_id),
        )

    elif data == "rename_chat_menu":
        """Legacy меню переименования через список."""
        chats = get_user_chats(user_id)
        buttons = []
        for chat in chats:
            buttons.append([InlineKeyboardButton(
                f"✏️ {chat['name'][:25]}",
                callback_data=f"chat_rename_{chat['chat_id']}"
            )])
        buttons.append([InlineKeyboardButton("◀️ Назад", callback_data="chats_list")])
        await query.edit_message_text(
            "✏️ <b>Переименовать чат</b>\n\nВыбери чат:",
            parse_mode=ParseMode.HTML,
            reply_markup=InlineKeyboardMarkup(buttons),
        )

    elif data.startswith("chat_rename_"):
        """Запрашивает новое имя для чата."""
        chat_id = int(data.replace("chat_rename_", ""))
        chat = get_chat(chat_id)
        if not chat or chat["user_id"] != user_id:
            await answer("❌ Чат не найден", show_alert=True)
            return
        context.user_data["awaiting_chat_rename"] = chat_id
        await query.edit_message_text(
            f"✏️ <b>Переименовать чат</b>\n\n"
            f"Текущее имя: <b>{escape_html(chat['name'])}</b>\n\n"
            f"Введи новое имя:",
            parse_mode=ParseMode.HTML,
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("◀️ Назад", callback_data=f"chat_menu_{chat_id}")]]),
        )

    elif data.startswith("chat_export_"):
        """Экспортирует чат в файл TXT."""
        chat_id = int(data.replace("chat_export_", ""))
        chat = get_chat(chat_id)
        if not chat or chat["user_id"] != user_id:
            await answer("❌ Чат не найден", show_alert=True)
            return
        # Загружаем историю этого чата и экспортируем
        messages = load_chat_messages(chat_id)
        old_history = user_histories.get(user_id, [])
        user_histories[user_id] = messages
        filename = export_history(user_id, "txt")
        user_histories[user_id] = old_history
        await query.message.reply_document(
            open(filename, "rb"),
            filename=f"{chat['name']}.txt",
            caption=f"📤 Экспорт чата: {escape_html(chat['name'])}",
        )
        import os as _os; _os.remove(filename)
        await answer("✅ Экспортировано!", show_alert=True)

    elif data == "delete_chat_menu":
        """Список чатов для удаления."""
        chats = get_user_chats(user_id)
        buttons = []
        for chat in chats:
            buttons.append([InlineKeyboardButton(
                f"🗑 {chat['name'][:25]} ({chat.get('message_count', 0)})",
                callback_data=f"chat_delete_{chat['chat_id']}"
            )])
        buttons.append([InlineKeyboardButton("◀️ Назад", callback_data="my_chats")])
        await query.edit_message_text(
            "🗑 <b>Удалить чат</b>\n\n⚠️ Сообщения удалятся безвозвратно!\n\nВыбери чат:",
            parse_mode=ParseMode.HTML,
            reply_markup=InlineKeyboardMarkup(buttons),
        )

    elif data.startswith("chat_delete_"):
        """Удаляет чат."""
        chat_id = int(data.replace("chat_delete_", ""))
        chat = get_chat(chat_id)
        if not chat or chat["user_id"] != user_id:
            await answer("❌ Чат не найден", show_alert=True)
            return
        current_id = get_current_chat_id(user_id)
        if chat_id == current_id:
            other_chats = [c for c in get_user_chats(user_id) if c["chat_id"] != chat_id]
            if other_chats:
                switch_chat(user_id, other_chats[0]["chat_id"])
                user_histories[user_id] = load_chat_messages(other_chats[0]["chat_id"])
            else:
                new_id = create_chat(user_id, "Новый чат")
                user_histories[user_id] = []
        delete_chat(chat_id)
        await answer("🗑 Чат удалён", show_alert=True)
        await query.edit_message_text(
            "🧠 <b>Мои чаты</b>\n\nВыбери действие:",
            parse_mode=ParseMode.HTML,
            reply_markup=my_chats_menu_keyboard(),
        )

    # ════════════════════════════════════════════════════
    #  ⚙️ НАСТРОЙКИ — обработчики
    # ════════════════════════════════════════════════════
    elif data == "my_settings":
        """Показывает настройки пользователя со всеми статусами."""
        settings = get_user_settings(user_id)
        style_labels = {"brief": "📄 Кратко", "detailed": "📋 Подробно", "expert": "🎓 Эксперт"}
        pers_labels = {"strict": "👔 Строгий", "friendly": "🤗 Дружелюбный", "sarcastic": "😏 Саркастичный"}
        
        style = settings.get("response_style", "detailed")
        personality = settings.get("bot_personality", "friendly")
        notif = bool(settings.get("notifications", 1))
        notif_status = "включены ✅" if notif else "выключены ❌"
        
        await query.edit_message_text(
            f"⚙️ <b>Настройки</b>\n\n"
            f"📝 <b>Стиль ответа:</b> {style_labels.get(style, style)}\n"
            f"   <i>{get_response_style_text(style)}</i>\n\n"
            f"🎭 <b>Характер бота:</b> {pers_labels.get(personality, personality)}\n"
            f"   <i>{get_personality_text(personality)[:60]}...</i>\n\n"
            f"🔔 <b>Уведомления:</b> {notif_status}",
            parse_mode=ParseMode.HTML,
            reply_markup=settings_keyboard(user_id),
        )

    elif data == "settings_style_menu":
        """Меню выбора стиля ответа."""
        settings = get_user_settings(user_id)
        style = settings.get("response_style", "detailed")
        style_labels = {"brief": "📄 Кратко", "detailed": "📋 Подробно", "expert": "🎓 Эксперт"}
        
        await query.edit_message_text(
            f"📝 <b>Стиль ответа</b>\n\n"
            f"Текущий: <b>{style_labels.get(style, style)}</b>\n\n"
            f"Выбери новый стиль:",
            parse_mode=ParseMode.HTML,
            reply_markup=style_select_keyboard(),
        )

    elif data.startswith("set_style_"):
        """Устанавливает стиль ответа."""
        style = data.replace("set_style_", "")
        if style not in ["brief", "detailed", "expert"]:
            await answer("❌ Неизвестный стиль", show_alert=True); return
        
        update_user_settings(user_id, response_style=style)
        style_labels = {"brief": "📄 Кратко", "detailed": "📋 Подробно", "expert": "🎓 Эксперт"}
        await answer(f"✅ Стиль: {style_labels.get(style)}", show_alert=True)
        await query.edit_message_text(
            f"⚙️ <b>Настройки</b>\n\n"
            f"📝 <b>Стиль ответа:</b> {style_labels.get(style)}\n"
            f"   {get_response_style_text(style)}",
            parse_mode=ParseMode.HTML,
            reply_markup=settings_keyboard(user_id),
        )

    elif data == "settings_personality_menu":
        """Меню выбора характера бота."""
        settings = get_user_settings(user_id)
        personality = settings.get("bot_personality", "friendly")
        pers_labels = {"strict": "👔 Строгий", "friendly": "🤗 Дружелюбный", "sarcastic": "😏 Саркастичный"}
        
        await query.edit_message_text(
            f"🎭 <b>Характер бота</b>\n\n"
            f"Текущий: <b>{pers_labels.get(personality, personality)}</b>\n\n"
            f"Выбери новый характер:",
            parse_mode=ParseMode.HTML,
            reply_markup=personality_select_keyboard(),
        )

    elif data.startswith("set_personality_"):
        """Устанавливает характер бота."""
        personality = data.replace("set_personality_", "")
        if personality not in ["strict", "friendly", "sarcastic"]:
            await answer("❌ Неизвестный характер", show_alert=True); return
        
        update_user_settings(user_id, bot_personality=personality)
        pers_labels = {"strict": "👔 Строгий", "friendly": "🤗 Дружелюбный", "sarcastic": "😏 Саркастичный"}
        await answer(f"✅ Характер: {pers_labels.get(personality)}", show_alert=True)
        await query.edit_message_text(
            f"⚙️ <b>Настройки</b>\n\n"
            f"🎭 <b>Характер бота:</b> {pers_labels.get(personality)}\n"
            f"   {get_personality_text(personality)[:50]}...",
            parse_mode=ParseMode.HTML,
            reply_markup=settings_keyboard(user_id),
        )

    elif data == "settings_model_menu":
        """Меню выбора модели AI в настройках."""
        await query.edit_message_text(
            f"🤖 <b>Модель AI</b>\n\nТекущая: <code>{CFG.get('groq_model', '—')}</code>\n\nВыбери модель:",
            parse_mode=ParseMode.HTML,
            reply_markup=settings_model_keyboard(),
        )

    elif data.startswith("set_model_"):
        """Устанавливает модель через настройки пользователя."""
        new_model = data.replace("set_model_", "")
        if new_model not in AVAILABLE_MODELS:
            await answer("❌ Неизвестная модель", show_alert=True); return
        CFG["groq_model"] = new_model
        _config_set("groq_model", new_model)
        _response_cache.clear()
        await answer(f"✅ Модель: {new_model}", show_alert=True)
        await query.edit_message_text(
            f"🤖 <b>Модель AI</b>\n\nТекущая: <code>{new_model}</code>\n\nВыбери модель:",
            parse_mode=ParseMode.HTML,
            reply_markup=settings_model_keyboard(),
        )

    elif data == "settings_language_menu":
        """Меню выбора языка."""
        await query.edit_message_text(
            "🌐 <b>Язык интерфейса</b>\n\nВыбери язык:",
            parse_mode=ParseMode.HTML,
            reply_markup=settings_language_keyboard(),
        )

    elif data.startswith("set_lang_"):
        lang_map = {"ru": "🇷🇺 Русский", "en": "🇬🇧 English", "uk": "🇺🇦 Українська"}
        lang = data.replace("set_lang_", "")
        label = lang_map.get(lang, lang)
        await answer(f"✅ Язык: {label}", show_alert=True)
        await query.edit_message_text(
            f"🌐 <b>Язык интерфейса</b>\n\nТекущий: <b>{label}</b>\n\n(Полная локализация в разработке)",
            parse_mode=ParseMode.HTML,
            reply_markup=settings_language_keyboard(),
        )

    elif data == "settings_notifications":
        settings = get_user_settings(user_id)
        notif = bool(settings.get("notifications", 1))
        new_val = 0 if notif else 1
        update_user_settings(user_id, notifications=new_val)
        status = "включены ✅" if new_val else "выключены ❌"
        await answer(f"Уведомления {status}", show_alert=True)
        await query.edit_message_text(
            f"🔔 <b>Уведомления</b>\n\nСтатус: <b>{status}</b>",
            parse_mode=ParseMode.HTML,
            reply_markup=settings_keyboard(user_id),
        )

    elif data == "settings_memory_menu":
        history = get_user_history(user_id)
        await query.edit_message_text(
            f"🧠 <b>Память бота</b>\n\n"
            f"📝 Сообщений в памяти: <b>{len(history)}</b>\n\n"
            f"Управляй историей диалога:",
            parse_mode=ParseMode.HTML,
            reply_markup=settings_memory_keyboard(),
        )

    elif data == "memory_clear_history":
        user_histories[user_id] = []
        save_history(user_id, [])
        await answer("✅ История очищена!", show_alert=True)
        await query.edit_message_text(
            "🧠 <b>Память бота</b>\n\n✅ История диалога очищена.",
            parse_mode=ParseMode.HTML,
            reply_markup=settings_memory_keyboard(),
        )

    # ════════════════════════════════════════════════════
    #  📊 СТАТИСТИКА — подразделы
    # ════════════════════════════════════════════════════
    elif data == "stats_general":
        stats = get_user_stats(user_id)
        chats = get_user_chats(user_id)
        estimated_savings = stats["total_messages"] * 0.01
        await query.edit_message_text(
            f"📊 <b>Общая статистика</b>\n\n"
            f"📨 Всего сообщений: <b>{stats['total_messages']}</b>\n"
            f"💬 За сегодня: <b>{stats['used']}</b>\n"
            f"🔤 Токенов потрачено: <b>{stats['total_tokens']:,}</b>\n"
            f"💰 Сэкономлено: <b>~${estimated_savings:.2f}</b>\n\n"
            f"📅 Зарегистрирован: {stats['joined']}\n"
            f"💬 Всего чатов: {len(chats)}",
            parse_mode=ParseMode.HTML,
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("◀️ Назад", callback_data="my_stats")]]),
        )

    elif data == "stats_tokens":
        stats = get_user_stats(user_id)
        tokens = stats["total_tokens"]
        saved_pct = min(int(tokens / 10000), 100) if tokens else 0
        await query.edit_message_text(
            f"🔤 <b>Расход токенов</b>\n\n"
            f"📊 Всего токенов: <b>{tokens:,}</b>\n"
            f"📉 Использовано: <b>{saved_pct}%</b> от лимита\n"
            f"💡 ~1 токен ≈ 4 символа",
            parse_mode=ParseMode.HTML,
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("◀️ Назад", callback_data="my_stats")]]),
        )

    elif data == "stats_messages":
        stats = get_user_stats(user_id)
        await query.edit_message_text(
            f"💬 <b>Количество сообщений</b>\n\n"
            f"📨 Всего отправлено: <b>{stats['total_messages']}</b>\n"
            f"🏆 Самый длинный чат: <b>{stats['longest_chat']}</b> сообщений\n"
            f"💎 Платежей: <b>{stats['payments_count']}</b> на <b>${stats['total_paid']:.2f}</b>",
            parse_mode=ParseMode.HTML,
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("◀️ Назад", callback_data="my_stats")]]),
        )

    elif data == "stats_achievements":
        stats = get_user_stats(user_id)
        msgs = stats["total_messages"]
        achievements = []
        if msgs >= 10:   achievements.append("🔥 Первые шаги — 10 сообщений")
        if msgs >= 100:  achievements.append("💬 Общительный — 100 сообщений")
        if msgs >= 1000: achievements.append("🎓 Эрудит — 1000 сообщений")
        if msgs >= 5000: achievements.append("🏆 Мастер слова — 5000 сообщений")
        if not achievements:
            achievements.append("🌱 Начни общаться чтобы получить достижения!")
        ach_text = "\n".join(achievements)
        await query.edit_message_text(
            f"🏆 <b>Достижения</b>\n\n{ach_text}",
            parse_mode=ParseMode.HTML,
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("◀️ Назад", callback_data="my_stats")]]),
        )

    # ════════════════════════════════════════════════════
    #  🛠 ИНСТРУМЕНТЫ — обработчики
    # ════════════════════════════════════════════════════
    elif data == "tools_menu":
        await query.edit_message_text(
            "🛠 <b>Инструменты</b>\n\nПолезные функции для работы с текстом и кодом:",
            parse_mode=ParseMode.HTML,
            reply_markup=tools_menu_keyboard(),
        )

    elif data == "tool_rewrite":
        context.user_data["awaiting_tool"] = "rewrite"
        await query.edit_message_text(
            "✏️ <b>Рерайт текста</b>\n\n"
            "Пришли мне текст, и я перепишу его по-новому 😎\n\n"
            "Просто отправь следующее сообщение с текстом:",
            parse_mode=ParseMode.HTML,
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("◀️ Назад", callback_data="tools_menu")]]),
        )

    elif data == "tool_translate":
        await query.edit_message_text(
            "🌐 <b>Переводчик</b>\n\nВыбери язык перевода:",
            parse_mode=ParseMode.HTML,
            reply_markup=translate_language_keyboard(),
        )

    elif data.startswith("translate_"):
        lang_map = {"en": "английский", "de": "немецкий", "fr": "французский", "es": "испанский", "zh": "китайский"}
        lang = data.replace("translate_", "")
        context.user_data["awaiting_tool"] = f"translate_{lang}"
        await query.edit_message_text(
            f"🌐 <b>Переводчик → {lang_map.get(lang, lang)}</b>\n\nОтправь текст для перевода:",
            parse_mode=ParseMode.HTML,
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("◀️ Назад", callback_data="tool_translate")]]),
        )

    elif data == "tool_codegen":
        await query.edit_message_text(
            "💻 <b>Генерация кода</b>\n\nВыбери язык программирования:",
            parse_mode=ParseMode.HTML,
            reply_markup=codegen_language_keyboard(),
        )

    elif data.startswith("codegen_"):
        lang = data.replace("codegen_", "")
        context.user_data["awaiting_tool"] = f"codegen_{lang}"
        await query.edit_message_text(
            f"💻 <b>Генерация кода — {lang.upper()}</b>\n\nОпиши что нужно написать:",
            parse_mode=ParseMode.HTML,
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("◀️ Назад", callback_data="tool_codegen")]]),
        )

    elif data == "tool_summarize":
        context.user_data["awaiting_tool"] = "summarize"
        await query.edit_message_text(
            "📄 <b>Резюме текста</b>\n\nОтправь текст и я кратко перескажу его суть:",
            parse_mode=ParseMode.HTML,
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("◀️ Назад", callback_data="tools_menu")]]),
        )

    elif data == "tool_imagegen":
        await query.edit_message_text(
            "🖼 <b>Генерация изображений</b>\n\n"
            "⚠️ Функция в разработке.\n\nСкоро здесь будет генерация изображений по описанию! 🎨",
            parse_mode=ParseMode.HTML,
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("◀️ Назад", callback_data="tools_menu")]]),
        )

    elif data == "tool_tts_menu":
        context.user_data["awaiting_tool"] = "tts_text"
        await query.edit_message_text(
            "🔊 <b>Озвучка текста</b>\n\nОтправь текст и я озвучу его голосовым сообщением:",
            parse_mode=ParseMode.HTML,
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("◀️ Назад", callback_data="tools_menu")]]),
        )

    # ════════════════════════════════════════════════════
    #  ℹ️ О БОТЕ — обработчики
    # ════════════════════════════════════════════════════
    elif data == "about_menu":
        await query.edit_message_text(
            "🤖 <b>Cicada AI</b>\n"
            "<code>v4.4</code>\n\n"
            "⚡ AI-кодер нового поколения\n\n"
            "Выбери раздел:",
            parse_mode=ParseMode.HTML,
            reply_markup=about_menu_keyboard(),
        )

    elif data == "about_howto":
        await query.edit_message_text(
            "❓ <b>Как использовать</b>\n\n"
            "Просто напиши мне сообщение, и я помогу тебе!\n\n"
            "Используй /help для списка команд.\n\n"
            "<b>Быстрые команды:</b>\n"
            "/start — Главное меню\n"
            "/help — Помощь\n"
            "/stats — Моя статистика\n"
            "/clear — Очистить чат\n"
            "/premium — Подписка",
            parse_mode=ParseMode.HTML,
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("◀️ Назад", callback_data="about_menu")]]),
        )

    elif data == "about_rules":
        await query.edit_message_text(
            "📜 <b>Правила использования</b>\n\n"
            "1. Запрещён спам и злоупотребления\n"
            "2. Не использовать для вредоносных целей\n"
            "3. Соблюдать законодательство\n"
            "4. Не передавать аккаунт третьим лицам\n\n"
            "Нарушение правил ведёт к блокировке.",
            parse_mode=ParseMode.HTML,
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("◀️ Назад", callback_data="about_menu")]]),
        )

    elif data == "about_privacy":
        await query.edit_message_text(
            "🔒 <b>Конфиденциальность</b>\n\n"
            "🔐 База данных зашифрована (AES-GCM)\n"
            "💬 История хранится только на сервере бота\n"
            "🚫 Данные не передаются третьим лицам\n"
            "🗑 Ты можешь удалить историю в любой момент",
            parse_mode=ParseMode.HTML,
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("◀️ Назад", callback_data="about_menu")]]),
        )

    elif data == "about_support":
        context.user_data["awaiting_support"] = True
        await query.edit_message_text(
            "🆘 <b>Поддержка</b>\n\n"
            "Мы поможем 🤝\n\n"
            "Опиши свою проблему и мы постараемся помочь как можно скорее.\n\n"
            "Отправь следующее сообщение с описанием проблемы:",
            parse_mode=ParseMode.HTML,
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("◀️ Назад", callback_data="about_menu")]]),
        )

    elif data == "about_rate":
        await query.edit_message_text(
            "⭐ <b>Оценить бота</b>\n\n"
            "Как тебе Cicada-AI?",
            parse_mode=ParseMode.HTML,
            reply_markup=InlineKeyboardMarkup([
                [
                    InlineKeyboardButton("⭐", callback_data="rate_1"),
                    InlineKeyboardButton("⭐⭐", callback_data="rate_2"),
                    InlineKeyboardButton("⭐⭐⭐", callback_data="rate_3"),
                ],
                [
                    InlineKeyboardButton("⭐⭐⭐⭐", callback_data="rate_4"),
                    InlineKeyboardButton("⭐⭐⭐⭐⭐", callback_data="rate_5"),
                ],
                [InlineKeyboardButton("◀️ Назад", callback_data="about_menu")],
            ]),
        )

    elif data.startswith("rate_"):
        stars = int(data.replace("rate_", ""))
        star_str = "⭐" * stars
        await answer(f"Спасибо за оценку {star_str}!", show_alert=True)
        await query.edit_message_text(
            f"⭐ <b>Спасибо за оценку!</b>\n\n{star_str}\n\nТвоё мнение очень важно для нас! 🙏",
            parse_mode=ParseMode.HTML,
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("◀️ Назад", callback_data="about_menu")]]),
        )


        await query.edit_message_text(
            f"📝 <b>Стиль ответа</b>\n\n"
            f"Выбери как бот будет отвечать:",
            parse_mode=ParseMode.HTML,
            reply_markup=style_select_keyboard(),
        )

    elif data.startswith("set_style_"):
        """Устанавливает стиль ответа."""
        style = data.replace("set_style_", "")
        update_user_settings(user_id, response_style=style)
        await answer(f"✅ Стиль: {style}", show_alert=True)
        # Возвращаемся в настройки
        settings = get_user_settings(user_id)
        style_labels = {"brief": "📄 Кратко", "detailed": "📋 Подробно", "expert": "🎓 Эксперт"}
        pers_labels = {"strict": "👔 Строгий", "friendly": "🤗 Дружелюбный", "sarcastic": "😏 Саркастичный"}
        personality = settings.get("bot_personality", "friendly")
        await query.edit_message_text(
            f"⚙️ <b>Настройки</b>\n\n"
            f"📝 <b>Стиль ответа:</b> {style_labels.get(style, style)}\n"
            f"   {get_response_style_text(style)}\n\n"
            f"🎭 <b>Характер бота:</b> {pers_labels.get(personality, personality)}\n"
            f"   {get_personality_text(personality)[:50]}...",
            parse_mode=ParseMode.HTML,
            reply_markup=settings_keyboard(user_id),
        )

    elif data == "settings_personality_menu":
        """Меню выбора характера бота."""
        await query.edit_message_text(
            f"🎭 <b>Характер бота</b>\n\n"
            f"Выбери поведение бота:",
            parse_mode=ParseMode.HTML,
            reply_markup=personality_select_keyboard(),
        )

    elif data.startswith("set_personality_"):
        """Устанавливает характер бота."""
        personality = data.replace("set_personality_", "")
        update_user_settings(user_id, bot_personality=personality)
        await answer(f"✅ Характер: {personality}", show_alert=True)
        # Возвращаемся в настройки
        settings = get_user_settings(user_id)
        style_labels = {"brief": "📄 Кратко", "detailed": "📋 Подробно", "expert": "🎓 Эксперт"}
        pers_labels = {"strict": "👔 Строгий", "friendly": "🤗 Дружелюбный", "sarcastic": "😏 Саркастичный"}
        style = settings.get("response_style", "detailed")
        await query.edit_message_text(
            f"⚙️ <b>Настройки</b>\n\n"
            f"📝 <b>Стиль ответа:</b> {style_labels.get(style, style)}\n"
            f"   {get_response_style_text(style)}\n\n"
            f"🎭 <b>Характер бота:</b> {pers_labels.get(personality, personality)}\n"
            f"   {get_personality_text(personality)[:50]}...",
            parse_mode=ParseMode.HTML,
            reply_markup=settings_keyboard(user_id),
        )

    # ════════════════════════════════════════════════════
    #  📊 СТАТИСТИКА — обработчики
    # ════════════════════════════════════════════════════
    elif data == "my_stats":
        """Показывает меню статистики."""
        stats = get_user_stats(user_id)
        await query.edit_message_text(
            f"📊 <b>Твоя активность</b>\n\n"
            f"📨 Всего сообщений: <b>{stats['total_messages']}</b>\n"
            f"🔤 Токенов: <b>{stats['total_tokens']:,}</b>\n"
            f"💎 Платежей: <b>{stats['payments_count']}</b> на <b>${stats['total_paid']:.2f}</b>\n\n"
            f"Выбери раздел статистики:",
            parse_mode=ParseMode.HTML,
            reply_markup=stats_keyboard(),
        )

    # ════════════════════════════════════════════════════
    #  💎 ПОДПИСКА — новая система (как на схеме)
    # ════════════════════════════════════════════════════
    elif data == "subscription_menu":
        """Главное меню подписки."""
        await query.edit_message_text(
            fmt_message(
                "💎 Управление подпиской",
                "Выбери действие",
                "📋 Мой план — статус и покупка Premium\n"
                "📜 История — все платежи\n"
                "🎁 Промокод — ввести код"
            ),
            parse_mode=ParseMode.HTML,
            reply_markup=subscription_menu_keyboard(),
        )

    elif data == "my_plan":
        """Показывает информацию о текущем плане."""
        u = get_user(user_id)
        left = remaining_limit(user_id)
        
        if is_premium(user_id):
            until = u.get("premium_until", "")
            try:
                exp = datetime.fromisoformat(until).strftime("%d.%m.%Y %H:%M")
            except Exception:
                exp = until
            plan_info = (
                f"💎 <b>План:</b> Premium\n"
                f"✅ Действует до: <b>{exp}</b>\n"
                f"♾ Безлимитный доступ"
            )
        else:
            lim = u.get("user_limit", u.get("limit", 50))
            used = u.get("used", 0)
            plan_info = (
                f"🎁 <b>План:</b> Free (Триал)\n"
                f"💬 Сообщений осталось: <b>{left}/{lim}</b>\n"
                f"📨 Использовано: <b>{used}</b>\n\n"
                f"💎 Апгрейд на Premium для безлимита!"
            )
        
        await query.edit_message_text(
            fmt_message(
                "📋 Мой план",
                plan_info,
            ),
            parse_mode=ParseMode.HTML,
            reply_markup=my_plan_keyboard(),
        )

    elif data == "add_balance":
        """Меню покупки Premium — по дням, $1/день."""
        await query.edit_message_text(
            fmt_message(
                "💎 Купить Premium",
                "Выбери срок подписки",
                "💡 Цена: <b>$1 за день</b>\n"
                "⚡ Активируется сразу после оплаты"
            ),
            parse_mode=ParseMode.HTML,
            reply_markup=buy_days_keyboard(),
        )

    elif data.startswith("pay_days_"):
        """Выбран срок в днях — показываем валюты."""
        days   = data.replace("pay_days_", "")
        amount = int(days) * 1  # $1 за день
        day_labels = {
            "1": "1 день", "3": "3 дня", "7": "7 дней",
            "15": "15 дней", "30": "30 дней"
        }
        label = day_labels.get(days, f"{days} дней")
        await query.edit_message_text(
            fmt_message(
                f"💎 Premium — {label}",
                f"Сумма к оплате: <b>${amount}</b>",
                "Выбери удобную валюту 👇"
            ),
            parse_mode=ParseMode.HTML,
            reply_markup=currency_for_days_keyboard(days, str(amount)),
        )

    elif data.startswith("pay_daycur_"):
        """Создание инвойса: pay_daycur_USDT_7_7"""
        parts_d = data.split("_")
        # pay / daycur / CURRENCY / DAYS / AMOUNT
        if len(parts_d) >= 5:
            currency   = parts_d[2]
            days       = parts_d[3]
            amount_str = parts_d[4]
            day_labels = {
                "1": "1 день", "3": "3 дня", "7": "7 дней",
                "15": "15 дней", "30": "30 дней"
            }
            label = day_labels.get(days, f"{days} дней")

            await query.edit_message_text(
                f"⏳ Создаю инвойс...\n{loading_bar(30)}",
                parse_mode=ParseMode.HTML,
            )

            invoice = await create_invoice_amount(user_id, amount_str, currency)
            if not invoice:
                await query.edit_message_text(
                    fmt_message(
                        "🔴 Ошибка",
                        "Не удалось создать инвойс",
                        "Попробуй позже или выбери другую валюту"
                    ),
                    parse_mode=ParseMode.HTML,
                    reply_markup=buy_days_keyboard(),
                )
                return

            inv_id     = invoice["invoice_id"]
            pay_url    = invoice["pay_url"]
            inv_amount = invoice["amount"]

            save_invoice(inv_id, user_id, f"premium_{days}d", query.message.chat.id, query.message.message_id)

            await query.edit_message_text(
                fmt_message(
                    "💳 Инвойс создан!",
                    f"Premium: <b>{label}</b>  ·  <b>${amount_str}</b>",
                    f"К оплате: <b>{inv_amount} {currency}</b>\n\n"
                    f"После оплаты нажми <b>«✅ Проверить»</b>"
                ),
                parse_mode=ParseMode.HTML,
                reply_markup=InlineKeyboardMarkup([
                    [InlineKeyboardButton("💳 Оплатить", url=pay_url)],
                    [InlineKeyboardButton("✅ Проверить оплату", callback_data=f"check_invoice_{inv_id}")],
                    [InlineKeyboardButton("◀️ Назад", callback_data="add_balance")],
                ]),
            )

    elif data == "payments_history":
        """Показывает историю платежей."""
        payments = get_user_payments(user_id)
        
        if not payments:
            payments_text = "📜 Пока нет платежей.\n\n💎 Купи Premium чтобы увидеть историю здесь!"
        else:
            payments_text = "📜 <b>История платежей</b>\n\n"
            for p in payments[:10]:  # последние 10
                date = p.get("paid_at", "—")[:10]
                amount = p.get("amount", 0)
                plan = p.get("plan", "—")
                status = "✅" if p.get("status") == "completed" else "⏳"
                payments_text += f"{status} {date} — ${amount:.2f} ({plan})\n"
        
        await query.edit_message_text(
            payments_text,
            parse_mode=ParseMode.HTML,
            reply_markup=payments_history_keyboard(),
        )

    elif data == "enter_promo":
        """Запрашиваем промокод."""
        context.user_data["awaiting_promo"] = True
        await query.edit_message_text(
            f"🎁 <b>Ввести промокод</b>\n\n"
            f"Введи промокод:\n"
            f"<i>(пока не работает — в разработке)</i>",
            parse_mode=ParseMode.HTML,
        )

    # Legacy: старая система (для обратной совместимости)
    elif data == "buy_premium":
        await query.edit_message_text(
            f"💎 <b>Управление подпиской</b>\n\n"
            f"Выбери действие:",
            parse_mode=ParseMode.HTML,
            reply_markup=subscription_menu_keyboard(),
        )

    elif data in ("plan_day", "plan_week", "plan_month"):
        plan = data.replace("plan_", "")
        await query.edit_message_text(
            f"💳 <b>Оплата: {PLAN_LABELS[plan]}</b>\n\nВыбери валюту:",
            parse_mode=ParseMode.HTML,
            reply_markup=currency_keyboard_legacy(plan),
        )

    elif data.startswith("pay_") and not data.startswith("pay_amount_") and not data.startswith("pay_currency_"):
        parts = data.split("_")
        if len(parts) != 3:
            await answer("❌ Ошибка", show_alert=True)
            return
        _, plan, currency = parts
        if not CRYPTOBOT_TOKEN:
            await answer("❌ CryptoBot не настроен.", show_alert=True)
            return
        await query.edit_message_text(f"⏳ Создаю инвойс для оплаты {currency}...")
        invoice = await create_invoice(user_id, plan, currency)
        if not invoice:
            await query.edit_message_text(
                "❌ Не удалось создать инвойс. Попробуй позже.",
                reply_markup=currency_keyboard(plan),
            )
            return
        inv_id  = invoice["invoice_id"]
        pay_url = invoice["pay_url"]
        amount  = invoice["amount"]
        save_invoice(inv_id, user_id, plan, query.message.chat.id, query.message.message_id)
        await query.edit_message_text(
            f"💳 <b>Инвойс создан!</b>\n\n"
            f"Тариф: <b>{PLAN_LABELS[plan]}</b>\n"
            f"Сумма: <b>{amount} {currency}</b>\n\n"
            f"Нажми кнопку ниже для оплаты через CryptoBot.\n"
            f"После оплаты нажми <b>«✅ Проверить оплату»</b>.",
            parse_mode=ParseMode.HTML,
            reply_markup=invoice_keyboard(pay_url, inv_id),
        )

    elif data.startswith("check_invoice_"):
        inv_id = int(data.replace("check_invoice_", ""))
        info   = get_invoice(inv_id)
        if not info:
            await answer("❌ Инвойс не найден или уже обработан.", show_alert=True)
            return
        status = await check_invoice(inv_id)
        if status == "paid":
            plan = info["plan"]
            
            # Новая система: premium_Xm — Premium на X месяцев
            if plan.startswith("premium_") and plan.endswith("m"):
                months = int(plan.replace("premium_", "").replace("m", ""))
                price_key = f"price_{months}month"
                amount = cfg_float(price_key)
                # Записываем платёж
                add_payment(user_id, f"{months} мес", amount, "USD", inv_id)
                # Активируем Premium на указанное количество месяцев
                from datetime import timedelta
                u = get_user(user_id)
                current_until = u.get("premium_until")
                base = datetime.now()
                if current_until:
                    try:
                        current = datetime.fromisoformat(current_until)
                        if current > base:
                            base = current
                    except:
                        pass
                new_until = base + timedelta(days=30*months)
                update_user(user_id, premium=True, premium_until=new_until.isoformat(), is_trial=False)
                delete_invoice(inv_id)
                request_save()
                await query.edit_message_text(
                    f"🎉 <b>Premium активирован!</b>\n\n"
                    f"Срок: <b>{months} {'месяц' if months == 1 else 'месяца' if months in [3, 5] else 'месяцев'}</b>\n"
                    f"Сумма: <b>${amount:.2f}</b>\n"
                    f"Действует до: <b>{new_until.strftime('%d.%m.%Y')}</b>\n\n"
                    f"Безлимитный доступ включён! 🚀",
                    parse_mode=ParseMode.HTML,
                    reply_markup=main_keyboard(user_id),
                )
            # Старая система: balance_X — пополнение на сумму
            elif plan.startswith("balance_"):
                amount = float(plan.replace("balance_", "0"))
                # Записываем платёж
                add_payment(user_id, f"${amount}", amount, "USD", inv_id)
                # Активируем Premium на основе суммы (примерно $10 = 1 месяц)
                days = int(amount * 3)  # $10 ≈ 30 дней
                temp_plan = f"custom_{days}d"
                # Создаём запись о Premium на рассчитанный период
                from datetime import timedelta
                u = get_user(user_id)
                current_until = u.get("premium_until")
                base = datetime.now()
                if current_until:
                    try:
                        current = datetime.fromisoformat(current_until)
                        if current > base:
                            base = current
                    except:
                        pass
                new_until = base + timedelta(days=days)
                update_user(user_id, premium=True, premium_until=new_until.isoformat(), is_trial=False)
                delete_invoice(inv_id)
                request_save()
                await query.edit_message_text(
                    f"🎉 <b>Баланс пополнен!</b>\n\n"
                    f"Сумма: <b>${amount:.2f}</b>\n"
                    f"Premium продлён на: <b>{days} дней</b>\n"
                    f"Действует до: <b>{new_until.strftime('%d.%m.%Y')}</b>\n\n"
                    f"Безлимитный доступ включён! 🚀",
                    parse_mode=ParseMode.HTML,
                    reply_markup=main_keyboard(user_id),
                )
            else:
                # Старая система: day/week/month
                price_map = {
                    "day": cfg_float("price_day"),
                    "week": cfg_float("price_week"),
                    "month": cfg_float("price_month"),
                }
                amount = price_map.get(plan, 0)
                # Записываем платёж
                add_payment(user_id, plan, amount, "USD", inv_id)
                activate_premium(user_id, plan)
                delete_invoice(inv_id)
                request_save()  # 💰 запланированное сохранение (оплата прошла)
                u     = get_user(user_id)
                until = u.get("premium_until", "")
                try:
                    exp = datetime.fromisoformat(until).strftime("%d.%m.%Y %H:%M")
                except Exception:
                    exp = until
                await query.edit_message_text(
                    f"🎉 <b>Premium активирован!</b>\n\n"
                    f"Тариф: <b>{PLAN_LABELS.get(plan, plan)}</b>\n"
                    f"Доступ до: <b>{exp}</b>\n\n"
                    f"Безлимитный доступ включён. Приятного использования! 🚀",
                    parse_mode=ParseMode.HTML,
                    reply_markup=main_keyboard(user_id),
                )
        elif status in ("active", "pending"):
            await answer("⏳ Оплата ещё не поступила. Попробуй через несколько секунд.", show_alert=True)
        elif status == "expired":
            delete_invoice(inv_id)
            await query.edit_message_text("❌ Инвойс истёк. Создай новый.", reply_markup=subscription_menu_keyboard())
        else:
            await answer(f"Статус: {status}. Попробуй позже.", show_alert=True)

    # ════════════════════════════════════════════════════
    #  🛡 АДМИН-ПАНЕЛЬ — новая структура (как на схеме)
    # ════════════════════════════════════════════════════
    elif data == "admin_panel":
        if user_id != ADMIN_ID:
            await answer("⛔ Нет доступа", show_alert=True); return
        _reset_daily_counters_if_needed()
        all_users   = load_users()
        premium_cnt = sum(1 for u in all_users.values() if u.get("premium"))
        g_today = CFG.get("groq_requests_today", "0")
        t_today = CFG.get("tavily_requests_today", "0")
        g_total = CFG.get("groq_requests_total", "0")
        t_total = CFG.get("tavily_requests_total", "0")
        await query.edit_message_text(
            f"🛡 <b>Админ-панель</b>\n\n"
            f"Выбери раздел:\n\n"
            f"👥 Пользователей: <b>{len(all_users)}</b>\n"
            f"💎 Premium: <b>{premium_cnt}</b>\n"
            f"🤖 Модель: <code>{CFG.get('groq_model', '—')}</code>\n"
            f"💾 БД: <b>RAM + AES-GCM</b>",
            parse_mode=ParseMode.HTML,
            reply_markup=admin_panel_keyboard(),
        )

    elif data == "admin_bot_settings":
        """Настройки бота — подменю."""
        if user_id != ADMIN_ID:
            await answer("⛔ Нет доступа", show_alert=True); return
        await query.edit_message_text(
            f"⚙️ <b>Настройки бота</b>\n\n"
            f"Управление ценами, БД, токенами и системой.",
            parse_mode=ParseMode.HTML,
            reply_markup=admin_bot_settings_keyboard(),
        )

    elif data == "admin_payments":
        """Управление платежами — подменю."""
        if user_id != ADMIN_ID:
            await answer("⛔ Нет доступа", show_alert=True); return
        # Считаем статистику платежей
        conn = get_db()
        c = conn.cursor()
        c.execute("SELECT COUNT(*) as cnt, SUM(amount) as total FROM payments WHERE status='completed'")
        row = c.fetchone()
        # conn is _db_connection (RAM), do not close
        total_payments = row["cnt"] if row else 0
        total_amount = row["total"] if row and row["total"] else 0
        
        await query.edit_message_text(
            f"💳 <b>Управление платежами</b>\n\n"
            f"✅ Успешных платежей: <b>{total_payments}</b>\n"
            f"💰 Общая сумма: <b>${total_amount:.2f}</b>\n\n"
            f"Выбери действие:",
            parse_mode=ParseMode.HTML,
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("📋 Все платежи", callback_data="admin_all_payments")],
                [InlineKeyboardButton("✅ Успешные", callback_data="admin_success_payments")],
                [InlineKeyboardButton("⏳ Ожидающие", callback_data="admin_pending_payments")],
                [InlineKeyboardButton("❌ Отменённые", callback_data="admin_failed_payments")],
                [InlineKeyboardButton("📊 Экспорт", callback_data="admin_export_payments")],
                [InlineKeyboardButton("◀️ Назад", callback_data="admin_panel")],
            ]),
        )

    elif data == "admin_models_menu":
        """Управление моделями AI."""
        if user_id != ADMIN_ID:
            await answer("⛔ Нет доступа", show_alert=True); return
        current = CFG.get("groq_model", "—")
        await query.edit_message_text(
            f"🤖 <b>Модели AI</b>\n\n"
            f"Текущая: <code>{current}</code>\n\n"
            f"Выбери действие:",
            parse_mode=ParseMode.HTML,
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("📋 Список моделей", callback_data="admin_model")],
                [InlineKeyboardButton("➕ Добавить модель", callback_data="admin_add_model")],
                [InlineKeyboardButton("✏️ Редактировать", callback_data="admin_edit_model")],
                [InlineKeyboardButton("🗑 Удалить модель", callback_data="admin_delete_model")],
                [InlineKeyboardButton("🔀 По умолчанию", callback_data="admin_default_model")],
                [InlineKeyboardButton("◀️ Назад", callback_data="admin_panel")],
            ]),
        )

    elif data == "admin_broadcast":
        """Управление рассылками."""
        if user_id != ADMIN_ID:
            await answer("⛔ Нет доступа", show_alert=True); return
        await query.edit_message_text(
            f"📢 <b>Рассылки</b>\n\n"
            f"Создание и управление массовыми рассылками.",
            parse_mode=ParseMode.HTML,
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("✏️ Создать рассылку", callback_data="admin_create_broadcast")],
                [InlineKeyboardButton("👥 Выбрать аудиторию", callback_data="admin_broadcast_audience")],
                [InlineKeyboardButton("📜 История рассылок", callback_data="admin_broadcast_history")],
                [InlineKeyboardButton("📊 Статистика", callback_data="admin_broadcast_stats")],
                [InlineKeyboardButton("◀️ Назад", callback_data="admin_panel")],
            ]),
        )

    elif data == "admin_logs":
        """Системные логи."""
        if user_id != ADMIN_ID:
            await answer("⛔ Нет доступа", show_alert=True); return
        await query.edit_message_text(
            f"📝 <b>Системные логи</b>\n\n"
            f"Выбери тип логов:",
            parse_mode=ParseMode.HTML,
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("📨 Логи запросов", callback_data="admin_logs_requests")],
                [InlineKeyboardButton("⚠️ Логи ошибок", callback_data="admin_logs_errors")],
                [InlineKeyboardButton("💳 Логи платежей", callback_data="admin_logs_payments")],
                [InlineKeyboardButton("🔐 Логи авторизации", callback_data="admin_logs_auth")],
                [InlineKeyboardButton("📤 Экспорт логов", callback_data="admin_export_logs")],
                [InlineKeyboardButton("◀️ Назад", callback_data="admin_panel")],
            ]),
        )

    elif data == "admin_maintenance":
        """Режим технических работ."""
        if user_id != ADMIN_ID:
            await answer("⛔ Нет доступа", show_alert=True); return
        # Проверяем текущий статус (храним в CFG)
        maintenance = CFG.get("maintenance_mode", "0") == "1"
        status = "🚨 ВКЛЮЧЕН" if maintenance else "✅ ВЫКЛЮЧЕН"
        new_status = "0" if maintenance else "1"
        btn_text = "✅ Выключить" if maintenance else "⚠️ Включить"
        
        await query.edit_message_text(
            f"⚠️ <b>Технические работы</b>\n\n"
            f"Статус: <b>{status}</b>\n\n"
            f"При включении бот будет недоступен для пользователей.",
            parse_mode=ParseMode.HTML,
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton(btn_text, callback_data=f"admin_toggle_maintenance_{new_status}")],
                [InlineKeyboardButton("◀️ Назад", callback_data="admin_bot_settings")],
            ]),
        )

    elif data.startswith("admin_toggle_maintenance_"):
        """Переключение режима техработ."""
        if user_id != ADMIN_ID:
            await answer("⛔ Нет доступа", show_alert=True); return
        new_mode = data.replace("admin_toggle_maintenance_", "")
        CFG["maintenance_mode"] = new_mode
        _config_set("maintenance_mode", new_mode)
        status = "включён 🚨" if new_mode == "1" else "выключен ✅"
        await answer(f"Техработы {status}", show_alert=True)
        # Перезагружаем меню
        await query.edit_message_text(
            f"⚠️ <b>Технические работы</b>\n\n"
            f"Статус: <b>{status.upper()}</b>",
            parse_mode=ParseMode.HTML,
            reply_markup=admin_bot_settings_keyboard(),
        )

    elif data == "admin_restart_bot":
        """Перезагрузка бота."""
        if user_id != ADMIN_ID:
            await answer("⛔ Нет доступа", show_alert=True); return
        await query.edit_message_text(
            f"🔄 <b>Перезагрузка бота</b>\n\n"
            f"⚠️ Это остановит бота на несколько секунд.\n\n"
            f"Ты уверен?",
            parse_mode=ParseMode.HTML,
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("✅ Да, перезагрузить", callback_data="admin_confirm_restart")],
                [InlineKeyboardButton("❌ Отмена", callback_data="admin_bot_settings")],
            ]),
        )

    elif data == "admin_confirm_restart":
        """Подтверждение перезагрузки."""
        if user_id != ADMIN_ID:
            await answer("⛔ Нет доступа", show_alert=True); return
        await query.edit_message_text(
            f"🔄 <b>Перезагрузка...</b>\n\n"
            f"Бот перезапускается. Подожди 5-10 секунд.",
            parse_mode=ParseMode.HTML,
        )
        # Сохраняем БД перед перезагрузкой
        force_save(_SESSION_PASSWORD)
        await answer("🔄 Перезагрузка...", show_alert=True)
        # Выходим — systemd/docker перезапустит бота
        sys.exit(0)

    elif data == "admin_stats":
        if user_id != ADMIN_ID:
            await answer("⛔ Нет доступа", show_alert=True); return
        _reset_daily_counters_if_needed()
        all_users   = load_users()
        total       = len(all_users)
        banned      = sum(1 for u in all_users.values() if u.get("banned"))
        premium_cnt = sum(1 for u in all_users.values() if u.get("premium"))
        total_used  = sum(u.get("used", 0) for u in all_users.values())
        g_today  = CFG.get("groq_requests_today", "0")
        t_today  = CFG.get("tavily_requests_today", "0")
        g_total  = CFG.get("groq_requests_total", "0")
        t_total  = CFG.get("tavily_requests_total", "0")
        g_thresh = CFG.get("groq_alert_threshold", "800")
        t_thresh = CFG.get("tavily_alert_threshold", "800")
        today    = datetime.now().strftime("%d.%m.%Y")
        await query.edit_message_text(
            f"📈 <b>Статистика бота</b>\n\n"
            f"👥 Всего пользователей: {total}\n"
            f"💎 Premium подписок: {premium_cnt}\n"
            f"🚫 Заблокировано: {banned}\n"
            f"📨 Всего запросов пользователей: {total_used}\n"
            f"💾 Кэш: {len(_response_cache)} записей\n"
            f"🤖 Модель: {CFG['groq_model']}\n\n"
            f"<b>📊 API счётчики ({today}):</b>\n"
            f"🤖 Groq сегодня: <b>{g_today}</b> / порог {g_thresh}\n"
            f"🔍 Tavily сегодня: <b>{t_today}</b> / порог {t_thresh}\n"
            f"🤖 Groq всего: <b>{g_total}</b>\n"
            f"🔍 Tavily всего: <b>{t_total}</b>\n\n"
            f"💾 Следующее сохранение БД: <b>{get_time_until_next_save()}</b>",
            parse_mode=ParseMode.HTML,
            reply_markup=admin_panel_keyboard(),
        )

    elif data == "admin_download_db":
        if user_id != ADMIN_ID:
            await answer("⛔ Нет доступа", show_alert=True); return
        
        # Получаем зашифрованный дамп БД
        await answer("📦 Создаю зашифрованный дамп...", show_alert=False)
        
        db_bytes = get_encrypted_db_bytes(_SESSION_PASSWORD)
        if db_bytes is None:
            await answer("❌ Ошибка создания дампа", show_alert=True)
            return
        
        # Отправляем как файл
        backup_file = BytesIO(db_bytes)
        backup_file.name = f"cicada_backup_{datetime.now().strftime('%Y%m%d_%H%M%S')}.db.enc"
        
        await context.bot.send_document(
            chat_id=query.message.chat.id,
            document=backup_file,
            caption=(
                f"💾 <b>Бэкап БД</b>\n\n"
                f"📅 Создан: <code>{datetime.now().strftime('%d.%m.%Y %H:%M')}</code>\n"
                f"🔐 Зашифрован: AES-GCM\n"
                f"📦 Размер: {len(db_bytes)} bytes\n\n"
                f"<b>⚠️ Храни этот файл и пароль безопасно!</b>"
            ),
            parse_mode=ParseMode.HTML
        )
        await answer("✅ Бэкап отправлен", show_alert=True)

    elif data == "admin_save_db":
        if user_id != ADMIN_ID:
            await answer("⛔ Нет доступа", show_alert=True); return
        
        await answer("💾 Сохраняю БД...", show_alert=False)
        
        if force_save(_SESSION_PASSWORD):
            next_save = get_time_until_next_save()
            await answer(f"✅ Сохранено! Следующее: {next_save}", show_alert=True)
        else:
            await answer("❌ Ошибка сохранения", show_alert=True)

    elif data == "admin_prices":
        if user_id != ADMIN_ID:
            await answer("⛔ Нет доступа", show_alert=True); return
        p1 = cfg_float("price_1month")
        p3 = cfg_float("price_3month")
        p5 = cfg_float("price_5month")
        p7 = cfg_float("price_7month")
        await query.edit_message_text(
            f"💰 <b>Цены Premium</b>\n\n"
            f"1 мес: <b>${p1}</b>\n"
            f"3 мес: <b>${p3}</b>\n"
            f"5 мес: <b>${p5}</b>\n"
            f"7 мес: <b>${p7}</b>\n\n"
            f"Нажми чтобы изменить цену.",
            parse_mode=ParseMode.HTML,
            reply_markup=admin_prices_keyboard(),
        )

    elif data.startswith("admin_setprice_"):
        if user_id != ADMIN_ID:
            await answer("⛔ Нет доступа", show_alert=True); return
        plan = data.replace("admin_setprice_", "")
        # Поддерживаем новые периоды 1/3/5/7 месяцев
        valid_plans = ("day", "week", "month", "1month", "3month", "5month", "7month")
        if plan not in valid_plans:
            await answer("❌ Неверный тариф", show_alert=True); return
        context.user_data["awaiting_price"] = plan
        # Формируем название периода
        if plan.endswith("month"):
            months = plan.replace("month", "")
            period_name = f"{months} мес"
        else:
            period_name = PLAN_LABELS.get(plan, plan)
        await query.edit_message_text(
            f"✏️ Введи новую цену для <b>{period_name}</b> (в USD).\n\n"
            f"Пример: <code>4.99</code>",
            parse_mode=ParseMode.HTML,
        )

    elif data == "admin_users" or data.startswith("admin_users_page_"):
        if user_id != ADMIN_ID:
            await answer("⛔ Нет доступа", show_alert=True); return
        page      = int(data.split("_")[-1]) if "page" in data else 0
        all_users = load_users()
        if not all_users:
            await query.edit_message_text("👥 Пользователей пока нет.", reply_markup=admin_panel_keyboard())
            return
        await query.edit_message_text(
            f"👥 <b>Пользователи</b> (стр. {page+1})\n"
            f"✅ активен | 💎 premium | 🚫 забанен | [остаток/лимит]",
            parse_mode=ParseMode.HTML,
            reply_markup=admin_users_keyboard(all_users, page),
        )

    elif data.startswith("admin_user_"):
        if user_id != ADMIN_ID:
            await answer("⛔ Нет доступа", show_alert=True); return
        uid       = data.replace("admin_user_", "")
        all_users = load_users()
        u         = all_users.get(uid)
        if not u:
            await answer("❌ Пользователь не найден", show_alert=True); return
        name = escape_html(u.get("first_name") or u.get("username") or uid)
        lim  = u.get("user_limit", u.get("limit", 50))
        left = max(0, lim - u.get("used", 0))
        prem_info = ""
        if u.get("premium"):
            until = u.get("premium_until", "")
            try:
                exp = datetime.fromisoformat(until).strftime("%d.%m.%Y %H:%M")
            except Exception:
                exp = until
            prem_info = f"\n💎 Premium до: {exp}"
        await query.edit_message_text(
            f"👤 <b>Пользователь</b>\n\n"
            f"Имя: <b>{name}</b>\n"
            f"ID: <code>{uid}</code>\n"
            f"Username: @{u.get('username') or '—'}\n"
            f"Статус: {'🚫 Забанен' if u.get('banned') else '✅ Активен'}"
            f"{prem_info}\n"
            f"Лимит: <b>{left}/{lim}</b>\n"
            f"Использовано: {u.get('used', 0)}\n"
            f"Регистрация: {u.get('joined', '—')}",
            parse_mode=ParseMode.HTML,
            reply_markup=admin_user_keyboard(uid, bool(u.get("banned"))),
        )

    elif data.startswith("admin_ban_"):
        if user_id != ADMIN_ID:
            await answer("⛔ Нет доступа", show_alert=True); return
        uid = data.replace("admin_ban_", "")
        update_user(int(uid), banned=True)
        await answer(f"🚫 Пользователь {uid} заблокирован", show_alert=True)
        await query.edit_message_reply_markup(reply_markup=admin_user_keyboard(uid, True))

    elif data.startswith("admin_unban_"):
        if user_id != ADMIN_ID:
            await answer("⛔ Нет доступа", show_alert=True); return
        uid = data.replace("admin_unban_", "")
        update_user(int(uid), banned=False)
        await answer(f"✅ Пользователь {uid} разблокирован", show_alert=True)
        await query.edit_message_reply_markup(reply_markup=admin_user_keyboard(uid, False))

    elif data.startswith("admin_delete_"):
        if user_id != ADMIN_ID:
            await answer("⛔ Нет доступа", show_alert=True); return
        uid = data.replace("admin_delete_", "")
        conn = get_db()
        conn.execute("DELETE FROM users WHERE id=?", (int(uid),))
        conn.execute("DELETE FROM histories WHERE user_id=?", (int(uid),))
        conn.commit()
        # conn is _db_connection (RAM), do not close
        request_save()  # 🗑 запланировать сохранение (удаление пользователя)
        user_histories.pop(int(uid), None)
        await answer(f"🗑 Пользователь {uid} удалён", show_alert=True)
        all_users = load_users()
        await query.edit_message_text(
            f"👥 <b>Пользователи</b>",
            parse_mode=ParseMode.HTML,
            reply_markup=admin_users_keyboard(all_users, 0),
        )

    elif data.startswith("admin_addlimit_"):
        if user_id != ADMIN_ID:
            await answer("⛔ Нет доступа", show_alert=True); return
        uid = data.replace("admin_addlimit_", "")
        u   = get_user(int(uid))
        new_lim = u.get("user_limit", u.get("limit", 50000)) + 10000
        update_user(int(uid), limit=new_lim)
        await answer(f"➕ Лимит увеличен до {new_lim}", show_alert=True)
        u    = get_user(int(uid))
        lim  = u.get("user_limit", u.get("limit", 50))
        left = max(0, lim - u.get("used", 0))
        name = escape_html(u.get("first_name") or u.get("username") or uid)
        await query.edit_message_text(
            f"👤 <b>Пользователь</b>\n\nИмя: <b>{name}</b>\nID: <code>{uid}</code>\n"
            f"Статус: {'🚫 Забанен' if u.get('banned') else '✅ Активен'}\n"
            f"Лимит: <b>{left}/{lim}</b>\nИспользовано: {u.get('used', 0)}",
            parse_mode=ParseMode.HTML,
            reply_markup=admin_user_keyboard(uid, bool(u.get("banned"))),
        )

    elif data.startswith("admin_sublimit_"):
        if user_id != ADMIN_ID:
            await answer("⛔ Нет доступа", show_alert=True); return
        uid = data.replace("admin_sublimit_", "")
        u   = get_user(int(uid))
        new_lim = max(0, u.get("user_limit", u.get("limit", 50000)) - 10000)
        update_user(int(uid), limit=new_lim)
        await answer(f"➖ Лимит уменьшен до {new_lim}", show_alert=True)
        u    = get_user(int(uid))
        lim  = u.get("user_limit", u.get("limit", 50))
        left = max(0, lim - u.get("used", 0))
        name = escape_html(u.get("first_name") or u.get("username") or uid)
        await query.edit_message_text(
            f"👤 <b>Пользователь</b>\n\nИмя: <b>{name}</b>\nID: <code>{uid}</code>\n"
            f"Статус: {'🚫 Забанен' if u.get('banned') else '✅ Активен'}\n"
            f"Лимит: <b>{left}/{lim}</b>\nИспользовано: {u.get('used', 0)}",
            parse_mode=ParseMode.HTML,
            reply_markup=admin_user_keyboard(uid, bool(u.get("banned"))),
        )

    elif data.startswith("admin_resetused_"):
        if user_id != ADMIN_ID:
            await answer("⛔ Нет доступа", show_alert=True); return
        uid = data.replace("admin_resetused_", "")
        update_user(int(uid), used=0)
        await answer("🔄 Счётчик запросов сброшен", show_alert=True)
        u    = get_user(int(uid))
        lim  = u.get("user_limit", u.get("limit", 50))
        left = max(0, lim - u.get("used", 0))
        name = escape_html(u.get("first_name") or u.get("username") or uid)
        await query.edit_message_text(
            f"👤 <b>Пользователь</b>\n\nИмя: <b>{name}</b>\nID: <code>{uid}</code>\n"
            f"Статус: {'🚫 Забанен' if u.get('banned') else '✅ Активен'}\n"
            f"Лимит: <b>{left}/{lim}</b>\nИспользовано: {u.get('used', 0)}",
            parse_mode=ParseMode.HTML,
            reply_markup=admin_user_keyboard(uid, bool(u.get("banned"))),
        )

    elif data.startswith("admin_givepremium_"):
        if user_id != ADMIN_ID:
            await answer("⛔ Нет доступа", show_alert=True); return
        uid = data.replace("admin_givepremium_", "")
        activate_premium(int(uid), "month")
        request_save()  # 💎 запланировать сохранение (выдача Premium)
        await answer(f"💎 Premium на месяц выдан пользователю {uid}", show_alert=True)
        u     = get_user(int(uid))
        lim   = u.get("user_limit", u.get("limit", 50))
        left  = max(0, lim - u.get("used", 0))
        name  = escape_html(u.get("first_name") or u.get("username") or uid)
        until = u.get("premium_until", "")
        try:
            exp = datetime.fromisoformat(until).strftime("%d.%m.%Y")
        except Exception:
            exp = until
        await query.edit_message_text(
            f"👤 <b>Пользователь</b>\n\nИмя: <b>{name}</b>\nID: <code>{uid}</code>\n"
            f"💎 Premium до: {exp}\nЛимит: <b>{left}/{lim}</b>\nИспользовано: {u.get('used', 0)}",
            parse_mode=ParseMode.HTML,
            reply_markup=admin_user_keyboard(uid, bool(u.get("banned"))),
        )

    elif data == "admin_api_stats":
        if user_id != ADMIN_ID:
            await answer("⛔ Нет доступа", show_alert=True); return
        _reset_daily_counters_if_needed()
        g_today  = CFG.get("groq_requests_today", "0")
        t_today  = CFG.get("tavily_requests_today", "0")
        g_total  = CFG.get("groq_requests_total", "0")
        t_total  = CFG.get("tavily_requests_total", "0")
        g_thresh = CFG.get("groq_alert_threshold", "800")
        t_thresh = CFG.get("tavily_alert_threshold", "800")
        g_alert  = "✅ отправлено" if CFG.get("groq_alert_sent") == "1" else "—"
        t_alert  = "✅ отправлено" if CFG.get("tavily_alert_sent") == "1" else "—"
        today    = datetime.now().strftime("%d.%m.%Y")
        await query.edit_message_text(
            f"📊 <b>Счётчики API запросов</b>\n\n"
            f"📅 Дата: {today}\n\n"
            f"🤖 <b>Groq API:</b>\n"
            f"  Сегодня: <b>{g_today}</b>\n"
            f"  Всего: <b>{g_total}</b>\n"
            f"  Порог SMS: {g_thresh}\n"
            f"  Уведомление: {g_alert}\n\n"
            f"🔍 <b>Tavily API:</b>\n"
            f"  Сегодня: <b>{t_today}</b>\n"
            f"  Всего: <b>{t_total}</b>\n"
            f"  Порог SMS: {t_thresh}\n"
            f"  Уведомление: {t_alert}",
            parse_mode=ParseMode.HTML,
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("📡 Лимиты Groq (live)", callback_data="admin_groq_limits")],
                [InlineKeyboardButton("🔄 Сбросить дневные счётчики", callback_data="admin_reset_counters")],
                [InlineKeyboardButton("◀️ Назад", callback_data="admin_panel")],
            ]),
        )

    elif data == "admin_groq_limits":
        if user_id != ADMIN_ID:
            await answer("⛔ Нет доступа", show_alert=True); return
        await answer("⏳ Проверяю лимиты...", show_alert=False)
        # Показываем сколько ключей нашли
        key_count = len(_GROQ_KEYS)
        lines = [f"🔑 Найдено ключей: <b>{key_count}</b>\n"]
        for idx, key in enumerate(_GROQ_KEYS, 1):
            masked = f"...{key[-6:]}" if key else "—"
            # Пауза между ключами чтобы окна лимитов не совпадали
            if idx > 1:
                await asyncio.sleep(2)
            info = await check_groq_limits(key)
            if info is None:
                lines.append(f"🔑 Ключ {idx} (<code>{masked}</code>): ❌ ошибка")
            else:
                req_used = int(info['req_limit']) - int(info['req_remaining']) if info['req_remaining'] != '?' else '?'
                tok_used = int(info['tok_limit']) - int(info['tok_remaining']) if info['tok_remaining'] != '?' else '?'
                lines.append(
                    f"🔑 Ключ {idx} (<code>{masked}</code>)\n"
                    f"  Запросы: <b>{info['req_remaining']}</b> / {info['req_limit']} (сброс: {info['req_reset']})\n"
                    f"  Токены:  <b>{info['tok_remaining']}</b> / {info['tok_limit']} (сброс: {info['tok_reset']})"
                )
        text = "📡 <b>Лимиты Groq API (live)</b>\n\n" + "\n\n".join(lines)
        await query.edit_message_text(
            text,
            parse_mode=ParseMode.HTML,
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("🔄 Обновить", callback_data="admin_groq_limits")],
                [InlineKeyboardButton("◀️ Назад", callback_data="admin_api_stats")],
            ]),
        )

    elif data == "admin_reset_counters":
        if user_id != ADMIN_ID:
            await answer("⛔ Нет доступа", show_alert=True); return
        CFG["groq_requests_today"] = "0"
        CFG["tavily_requests_today"] = "0"
        CFG["groq_alert_sent"] = "0"
        CFG["tavily_alert_sent"] = "0"
        _config_set("groq_requests_today", "0")
        _config_set("tavily_requests_today", "0")
        _config_set("groq_alert_sent", "0")
        _config_set("tavily_alert_sent", "0")
        await answer("✅ Дневные счётчики сброшены", show_alert=True)
        # Показываем обновлённую страницу счётчиков
        g_today  = CFG.get("groq_requests_today", "0")
        t_today  = CFG.get("tavily_requests_today", "0")
        g_total  = CFG.get("groq_requests_total", "0")
        t_total  = CFG.get("tavily_requests_total", "0")
        g_thresh = CFG.get("groq_alert_threshold", "800")
        t_thresh = CFG.get("tavily_alert_threshold", "800")
        today    = datetime.now().strftime("%d.%m.%Y")
        await query.edit_message_text(
            f"📊 <b>Счётчики API запросов</b>\n\n"
            f"📅 Дата: {today}\n\n"
            f"🤖 <b>Groq API:</b>\n"
            f"  Сегодня: <b>{g_today}</b>\n"
            f"  Всего: <b>{g_total}</b>\n"
            f"  Порог SMS: {g_thresh}\n\n"
            f"🔍 <b>Tavily API:</b>\n"
            f"  Сегодня: <b>{t_today}</b>\n"
            f"  Всего: <b>{t_total}</b>\n"
            f"  Порог SMS: {t_thresh}",
            parse_mode=ParseMode.HTML,
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("🔄 Сбросить дневные счётчики", callback_data="admin_reset_counters")],
                [InlineKeyboardButton("◀️ Назад", callback_data="admin_panel")],
            ]),
        )

    elif data == "admin_tokens":
        if user_id != ADMIN_ID:
            await answer("⛔ Нет доступа", show_alert=True); return
        groq_masked = f"...{GROQ_TOKEN[-6:]}" if GROQ_TOKEN else "не задан"
        tav_masked  = f"...{TAVILY_TOKEN[-6:]}" if TAVILY_TOKEN else "не задан"
        bot_masked  = f"...{BOT_TOKEN[-6:]}" if BOT_TOKEN else "не задан"
        await query.edit_message_text(
            f"🔑 <b>Управление токенами API</b>\n\n"
            f"🤖 Groq: <code>{groq_masked}</code>\n"
            f"🔍 Tavily: <code>{tav_masked}</code>\n"
            f"🤖 Bot: <code>{bot_masked}</code>\n\n"
            f"⚠️ После смены токена нажми <b>«🔄 Перезапустить бот»</b>",
            parse_mode=ParseMode.HTML,
            reply_markup=admin_tokens_keyboard(),
        )

    elif data == "admin_alert_threshold":
        if user_id != ADMIN_ID:
            await answer("⛔ Нет доступа", show_alert=True); return
        await query.edit_message_text(
            f"🚨 <b>Пороги уведомлений</b>\n\n"
            f"При достижении порога — тебе придёт сообщение в Telegram.\n\n"
            f"🤖 Groq порог: <b>{CFG.get('groq_alert_threshold', '800')}</b> запросов/день\n"
            f"🔍 Tavily порог: <b>{CFG.get('tavily_alert_threshold', '800')}</b> запросов/день",
            parse_mode=ParseMode.HTML,
            reply_markup=admin_alert_threshold_keyboard(),
        )

    elif data in ("admin_set_groq_token", "admin_set_tavily_token", "admin_set_bot_token",
                  "admin_set_groq_threshold", "admin_set_tavily_threshold"):
        if user_id != ADMIN_ID:
            await answer("⛔ Нет доступа", show_alert=True); return
        prompts = {
            "admin_set_groq_token":       ("groq_token_input",    "🤖 Введи новый <b>Groq API токен</b>:"),
            "admin_set_tavily_token":     ("tavily_token_input",  "🔍 Введи новый <b>Tavily API токен</b>:"),
            "admin_set_bot_token":        ("bot_token_input",     "🤖 Введи новый <b>Telegram Bot токен</b>:\n\n⚠️ Бот перезапустится автоматически!"),
            "admin_set_groq_threshold":   ("groq_threshold_input","🤖 Введи порог уведомлений для <b>Groq</b> (запросов/день):\n\nПример: <code>800</code>"),
            "admin_set_tavily_threshold": ("tavily_threshold_input","🔍 Введи порог уведомлений для <b>Tavily</b> (запросов/день):\n\nПример: <code>800</code>"),
        }
        state_key, prompt_text = prompts[data]
        context.user_data["awaiting_input"] = state_key
        await query.edit_message_text(prompt_text, parse_mode=ParseMode.HTML)

    elif data == "admin_restart_bot":
        if user_id != ADMIN_ID:
            await answer("⛔ Нет доступа", show_alert=True); return
        await query.edit_message_text(
            "🔄 <b>Перезапуск бота...</b>\n\nБот перезапустится через 2 секунды.",
            parse_mode=ParseMode.HTML,
        )
        await asyncio.sleep(2)
        os.execv(sys.executable, [sys.executable] + sys.argv)

    elif data == "admin_model":
        if user_id != ADMIN_ID:
            await answer("⛔ Нет доступа", show_alert=True); return
        await query.edit_message_text(
            f"🤖 <b>Выбор модели</b>\n\nТекущая: <code>{CFG['groq_model']}</code>\n\n"
            "Выбери модель — она применится сразу без перезапуска:",
            parse_mode=ParseMode.HTML,
            reply_markup=admin_model_keyboard(),
        )

    elif data.startswith("admin_setmodel_"):
        if user_id != ADMIN_ID:
            await answer("⛔ Нет доступа", show_alert=True); return
        new_model = data.replace("admin_setmodel_", "")
        if new_model not in AVAILABLE_MODELS:
            await answer("❌ Неизвестная модель", show_alert=True); return
        CFG["groq_model"] = new_model
        _config_set("groq_model", new_model)
        _response_cache.clear()
        await answer(f"✅ Модель: {new_model}", show_alert=True)
        await query.edit_message_text(
            f"🤖 <b>Выбор модели</b>\n\nТекущая: <code>{CFG['groq_model']}</code>\n\n"
            "Выбери модель — она применится сразу без перезапуска:",
            parse_mode=ParseMode.HTML,
            reply_markup=admin_model_keyboard(),
        )

    # Fallback: подтвердить callback если ни одна ветка не вызвала answer()
    await answer()



# ════════════════════════════════════════════════════
#  /maintenance — режим техработ (только админ)
# ════════════════════════════════════════════════════
async def cmd_maintenance(update: Update, context: ContextTypes.DEFAULT_TYPE):
    global MAINTENANCE_MODE
    user_id = update.effective_user.id
    if user_id != ADMIN_ID:
        await update.message.reply_text("⛔ Только для администратора.")
        return
    args = context.args
    if not args or args[0] not in ("on", "off"):
        status = "🔧 ВКЛ" if MAINTENANCE_MODE else "✅ ВЫКЛ"
        await update.message.reply_text(
            f"🔧 <b>Режим техработ</b>\n\nСтатус: <b>{status}</b>\n\n"
            f"Команды:\n/maintenance on — включить\n/maintenance off — выключить",
            parse_mode="HTML",
        )
        return
    if args[0] == "on":
        MAINTENANCE_MODE = True
        await update.message.reply_text(
            "🔧 <b>Техработы включены.</b>\n\nПользователи видят сообщение о недоступности.\nТы работаешь в обычном режиме.",
            parse_mode="HTML",
        )
    else:
        MAINTENANCE_MODE = False
        await update.message.reply_text(
            "✅ <b>Техработы завершены.</b>\n\nБот снова доступен всем пользователям.",
            parse_mode="HTML",
        )


# ════════════════════════════════════════════════════
#  /model — смена модели (только админ)
# ════════════════════════════════════════════════════
async def cmd_model(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    if user_id != ADMIN_ID:
        await update.message.reply_text("⛔ Только для администратора.")
        return
    if not context.args:
        models_list = "\n".join(f"• <code>{m}</code>" for m in AVAILABLE_MODELS)
        await update.message.reply_text(
            f"🤖 <b>Текущая модель:</b> <code>{CFG['groq_model']}</code>\n\n"
            f"<b>Доступные модели:</b>\n{models_list}\n\n"
            f"Используй: /model <code>название_модели</code>",
            parse_mode=ParseMode.HTML,
            reply_markup=admin_model_keyboard(),
        )
        return
    new_model = context.args[0].strip()
    if new_model not in AVAILABLE_MODELS:
        await update.message.reply_text(
            f"❌ Неизвестная модель: <code>{escape_html(new_model)}</code>\n\n"
            f"Доступные:\n" + "\n".join(f"• <code>{m}</code>" for m in AVAILABLE_MODELS),
            parse_mode=ParseMode.HTML,
        )
        return
    CFG["groq_model"] = new_model
    _config_set("groq_model", new_model)
    await update.message.reply_text(
        f"✅ Модель переключена на <code>{new_model}</code>",
        parse_mode=ParseMode.HTML,
        reply_markup=admin_model_keyboard(),
    )


# ════════════════════════════════════════════════════
#  ЗАПУСК
# ════════════════════════════════════════════════════
async def _auto_save_loop():
    """Фоновая задача: автосохранение БД каждые 60 секунд."""
    while True:
        await asyncio.sleep(10)  # проверяем каждые 10 сек
        try:
            save_if_needed(_SESSION_PASSWORD)
        except Exception as e:
            logger.error(f"Ошибка автосохранения: {e}")


def main():
    app = Application.builder().token(BOT_TOKEN).build()
    app.add_handler(CommandHandler("start",  start))
    app.add_handler(CommandHandler("model",  cmd_model))
    app.add_handler(CommandHandler("maintenance", cmd_maintenance))
    app.add_handler(CallbackQueryHandler(button_handler))
    app.add_handler(MessageHandler(filters.Document.ALL,            handle_file))
    app.add_handler(MessageHandler(filters.VOICE,                   handle_voice))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_message))

    async def post_init(application):
        asyncio.create_task(_auto_save_loop())
        logger.info("✅ Фоновое автосохранение БД запущено")

    app.post_init = post_init
    print("🤖 Cicada-AI v4.5-DB запущен...")
    app.run_polling()


if __name__ == "__main__":
    main()
