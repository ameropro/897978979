"""КрНУ КН-26-1: polling Telegram bot + HTML timetable watcher.

Requires Python 3.10+. Run: python bot.py --test (first), then python bot.py.
"""
import argparse
import contextlib
import hashlib
import html
import json
import logging
import os
import re
import sqlite3
import time
from datetime import datetime, timedelta, date
from pathlib import Path
from zoneinfo import ZoneInfo

import re
import requests
from bs4 import BeautifulSoup
from dotenv import load_dotenv

load_dotenv()
TOKEN = os.getenv('TELEGRAM_BOT_TOKEN', '')
CHAT_ID = int(os.getenv('TELEGRAM_CHAT_ID', '-1004354226990'))
OWNER_ID = int(os.getenv('TELEGRAM_OWNER_ID', '0'))
GROUP_ID = os.getenv('GROUP_ID', '3520')
FACULTY_ID = os.getenv('FACULTY_ID', '14')
COURSE = os.getenv('COURSE', '1')
URL = os.getenv('SCHEDULE_URL', 'http://193.189.127.179:5010/time-table/group?type=0')
TZ = ZoneInfo(os.getenv('TIMEZONE', 'Europe/Kyiv'))
INTERVAL = max(30, int(os.getenv('CHECK_INTERVAL_SECONDS', '60')))
REMINDER = int(os.getenv('REMINDER_MINUTES', '10'))
DB = Path(__file__).with_name('state.sqlite3')
LOG = logging.getLogger('kn26bot')
DATE_RE = re.compile(r'\b(\d{2})\.(\d{2})\.(\d{4})\b')
TIME_RE = re.compile(r'\b([01]?\d|2[0-3]):([0-5]\d)\b')
PAIR_RE = re.compile(r'(\d+)\s*пара', re.I)


@contextlib.contextmanager
def single_instance():
    """Avoid concurrent polling where OS file locks are supported."""
    lock_path = Path(__file__).with_name('bot.lock')
    with lock_path.open('a+b') as lock_file:
        lock_file.seek(0)
        lock_file.write(b'0')
        lock_file.flush()
        lock_file.seek(0)
        locked = False
        if os.name == 'nt':
            import msvcrt
            try:
                msvcrt.locking(lock_file.fileno(), msvcrt.LK_NBLCK, 1)
                locked = True
            except OSError:
                raise RuntimeError('Бот уже запущен. Второй экземпляр остановлен.') from None
        else:
            import errno
            import fcntl
            try:
                fcntl.flock(lock_file.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                locked = True
            except OSError as exc:
                if exc.errno in (errno.ENOSYS, errno.ENOTSUP, 52, 95):
                    LOG.warning('Файловая блокировка недоступна; запустите только один экземпляр бота')
                elif exc.errno in (errno.EAGAIN, errno.EACCES):
                    raise RuntimeError('Бот уже запущен. Второй экземпляр остановлен.') from exc
                else:
                    raise
        try:
            yield
        finally:
            if locked:
                if os.name == 'nt':
                    lock_file.seek(0)
                    msvcrt.locking(lock_file.fileno(), msvcrt.LK_UNLCK, 1)
                else:
                    fcntl.flock(lock_file.fileno(), fcntl.LOCK_UN)


def db_connect():
    conn = sqlite3.connect(DB)
    conn.execute('CREATE TABLE IF NOT EXISTS kv (key TEXT PRIMARY KEY, value TEXT NOT NULL)')
    conn.execute('CREATE TABLE IF NOT EXISTS sent (key TEXT PRIMARY KEY, at TEXT NOT NULL)')
    conn.execute('CREATE TABLE IF NOT EXISTS subscribers (chat_id INTEGER PRIMARY KEY, subscribed_at TEXT NOT NULL)')
    conn.execute('CREATE TABLE IF NOT EXISTS zoom_preferences (chat_id INTEGER PRIMARY KEY, show_zoom INTEGER NOT NULL DEFAULT 1)')
    conn.commit()
    return conn


def kv_get(db, key):
    row = db.execute('SELECT value FROM kv WHERE key=?', (key,)).fetchone()
    return row[0] if row else None


def kv_set(db, key, value):
    db.execute('INSERT OR REPLACE INTO kv VALUES (?,?)', (key, value))
    db.commit()


def claim(db, key):
    if db.execute('SELECT 1 FROM sent WHERE key=?', (key,)).fetchone():
        return False
    db.execute('INSERT INTO sent VALUES (?,?)', (key, datetime.now(TZ).isoformat()))
    db.commit()
    return True


def unclaim(db, key):
    db.execute('DELETE FROM sent WHERE key=?', (key,))
    db.commit()


def clean(node):
    return ' '.join(node.stripped_strings)


def get_csrf(soup):
    meta = soup.select_one('meta[name="csrf-token"]')
    if meta and meta.get('content'):
        return meta['content']
    inp = soup.select_one('input[name="_csrf-frontend"]')
    if inp and inp.get('value'):
        return inp['value']
    raise ValueError('Не найден CSRF-токен в HTML страницы')


def fetch_html(session, start, end):
    r = session.get(URL, timeout=25)
    r.raise_for_status()
    soup = BeautifulSoup(r.text, 'html.parser')
    csrf = get_csrf(soup)
    payload = {
        '_csrf-frontend': csrf,
        'TimeTableForm[facultyId]': FACULTY_ID,
        'TimeTableForm[course]': COURSE,
        'TimeTableForm[groupId]': GROUP_ID,
        'date-picker': f'{start:%d.%m.%Y} - {end:%d.%m.%Y}',
        'TimeTableForm[dateStart]': start.strftime('%d.%m.%Y'),
        'TimeTableForm[dateEnd]': end.strftime('%d.%m.%Y'),
        'TimeTableForm[indicationDays]': '5',
        'time-table-type': '1',
    }
    r = session.post(URL, data=payload, headers={'Referer': URL}, timeout=35)
    r.raise_for_status()
    html = r.text
    soup = BeautifulSoup(html, 'html.parser')
    sel = soup.select_one('select[name="TimeTableForm[groupId]"] option[selected]')
    if sel and sel.get('value') != GROUP_ID:
        raise ValueError(f'Сайт выбрал другую группу: {sel.get("value")}')
    if 'КН-26-1' not in soup.get_text(' ', strip=True) and not sel:
        raise ValueError('В ответе не обнаружена выбранная группа; проверьте параметры')
    return html


def parse_timetable(html):
    """Parse grid tables with date columns and lesson rows.

    Site HTML is not publicly reachable from this environment; --test saves a
    snapshot for diagnosis. Never silently interpret an unrecognized table as empty.
    """
    soup = BeautifulSoup(html, 'html.parser')
    matches = []
    candidates = 0
    for table in soup.find_all('table'):
        rows = table.find_all('tr')
        if not rows:
            continue
        date_columns = {}
        for tr in rows:
            cells = tr.find_all(['td', 'th'], recursive=False)
            dates = []
            for i, cell in enumerate(cells):
                m = DATE_RE.search(clean(cell))
                if m:
                    try:
                        d = date(int(m.group(3)), int(m.group(2)), int(m.group(1)))
                        dates.append((i, d))
                    except ValueError:
                        pass
            if dates and len(dates) >= 1:
                date_columns = dict(dates)
                candidates += 1
                continue
            if not date_columns or len(cells) < 2:
                continue
            first = clean(cells[0])
            pair_match = PAIR_RE.search(first)
            times = TIME_RE.findall(first)
            if not pair_match or not times:
                continue
            start_time = ':'.join(times[0])
            end_time = ':'.join(times[1]) if len(times) > 1 else None
            for col, day in date_columns.items():
                if col >= len(cells):
                    continue
                cell = cells[col]
                raw = clean(cell)
                if not raw or raw in ('—', '-', '–'):
                    continue
                # Preserve all text: multiple lessons in one cell may be combined.
                # The --test command allows validating this on the live HTML.
                matches.append({
                    'date': day.isoformat(), 'pair': int(pair_match.group(1)),
                    'start': start_time, 'end': end_time, 'description': raw,
                })
    if candidates == 0:
        raise ValueError('Не найдена таблица с колонками дат; нужен HTML для адаптации парсера')
    # Reject ambiguous duplicates instead of sending false notifications.
    seen = set()
    result = []
    for item in matches:
        key = (item['date'], item['pair'], item['start'], item['description'])
        if key not in seen:
            seen.add(key)
            result.append(item)
    return sorted(result, key=lambda x: (x['date'], x['start'], x['pair']))


def tg(method, payload, timeout=20):
    r = requests.post(f'https://api.telegram.org/bot{TOKEN}/{method}', json=payload, timeout=timeout)
    r.raise_for_status()
    obj = r.json()
    if not obj.get('ok'):
        raise RuntimeError(f'Telegram {method}: {obj.get("description")}')
    return obj['result']


ZOOM_LINKS = {
    'math': 'https://us02web.zoom.us/j/3077647729?pwd=WWQ1ekg3MTYyeUJpejJFaVNoY1dQUT09',
    'oit_naida': 'https://us05web.zoom.us/j/2531286862?pwd=kEbsnbSXQ4RScPq9MqhaNG3Cl2BRrS.1',
    'oit_rylova': 'https://us02web.zoom.us/j/4706770837?pwd=OXFrSUExOVdSOUZ1Tkp5NXNNWXVlUT09',
    'oit_sydorenko': 'https://us02web.zoom.us/j/86033350284?pwd=JQrNrbPR2SvmrUzSqXoa0gR1De97pq.1',
    'amps': 'https://us02web.zoom.us/j/87437416609?pwd=TmFYaHArdTk4dWcrSUpzWmJtSG1tdz09',
    'atp': 'https://us02web.zoom.us/j/5322174265?pwd=2ALRLn6liHkZcAGqzEP3jJm6SgXC5X.1',
}


def zoom_for(description):
    """Return Zoom URL only when subject (and if needed teacher) is recognized."""
    text = description.casefold().replace('і', 'i')
    subject = re.split(r'\s*\[', text, maxsplit=1)[0].strip()
    if subject in ('вм', 'дм', 'дискр.мат', 'дискр мат', 'дискретна математика'):
        return ZOOM_LINKS['math']
    if subject in ('оiт', 'оіт'):
        if 'найда' in text:
            return ZOOM_LINKS['oit_naida']
        if 'рилова' in text or 'рылова' in text:
            return ZOOM_LINKS['oit_rylova']
        if 'сидоренко' in text:
            return ZOOM_LINKS['oit_sydorenko']
        return None
    if subject == 'ампс':
        return ZOOM_LINKS['amps']
    if subject == 'атп':
        return ZOOM_LINKS['atp']
    return None


def send(text):
    tg('sendMessage', {'chat_id': CHAT_ID, 'text': text,
                       'parse_mode': 'HTML', 'disable_web_page_preview': True})


def pretty(item, db=None):
    line = f"{item['start']}{'–'+item['end'] if item['end'] else ''} | {item['pair']} пара"
    result = html.escape(line + '\n' + item['description'])
    link = zoom_for(item['description'])
    # The owner-controlled Zoom setting determines the displayed format.
    if link and (db is None or zoom_enabled_for_date(db, item['date'])):
        result += '\n💻 Дистант'
        result += f'\n🔗 <a href="{html.escape(link, quote=True)}">Подключиться к Zoom</a>'
    else:
        result += '\n🏫 Очная пара'
    return result


def show_day(items, day, db=None):
    lessons = [i for i in items if i['date'] == day.isoformat()]
    if not lessons:
        return f'📅 {day:%d.%m.%Y}\nПар не найдено в полученном расписании.'
    return f'📅 КН-26-1 | {day:%d.%m.%Y}\n\n' + '\n\n'.join(pretty(i, db) for i in lessons)


def show_week(items, today, db=None):
    monday = today - timedelta(days=today.weekday())
    blocks = [show_day(items, monday + timedelta(days=i), db) for i in range(7)
              if any(x['date'] == (monday + timedelta(days=i)).isoformat() for x in items)]
    return '\n\n'.join(blocks) if blocks else 'На эту неделю пары не найдены.'


def lesson_start(item):
    return datetime.fromisoformat(item['date'] + 'T' + item['start']).replace(tzinfo=TZ)


def lesson_end(item):
    if not item.get('end'):
        return None
    return datetime.fromisoformat(item['date'] + 'T' + item['end']).replace(tzinfo=TZ)


def show_next(items, now, db=None):
    upcoming = [item for item in items if lesson_start(item) > now]
    if not upcoming:
        return '📅 Следующих пар в загруженном расписании не найдено.'
    item = min(upcoming, key=lesson_start)
    return f"⏭ Следующая пара | {datetime.fromisoformat(item['date']):%d.%m.%Y}\n\n{pretty(item, db)}"


def show_now(items, now, db=None):
    active = [item for item in items if lesson_end(item) is not None
              and lesson_start(item) <= now < lesson_end(item)]
    if not active:
        return '☕ Сейчас пары нет.'
    return '📖 Сейчас идёт пара:\n\n' + '\n\n'.join(pretty(item, db) for item in active)


def split_message(message):
    if len(message) <= 3500:
        return [message]
    chunks = []
    current = ''
    for block in message.split('\n\n'):
        candidate = (current + '\n\n' + block) if current else block
        if len(candidate) > 3500 and current:
            chunks.append(current)
            current = block
        else:
            current = candidate
    if current:
        chunks.append(current)
    return chunks


def zoom_enabled(db):
    """Global Zoom visibility for the group and all private subscribers."""
    return kv_get(db, 'global_show_zoom') != '0'


def zoom_enabled_for_date(db, iso_date):
    """Master switch overrides all date-specific settings."""
    return zoom_enabled(db) and kv_get(db, 'zoom_day:' + iso_date) != '0'


def zoom_disabled_dates(db):
    return [row[0].removeprefix('zoom_day:') for row in db.execute(
        "SELECT key FROM kv WHERE key LIKE 'zoom_day:%' AND value='0' ORDER BY key")]


def set_zoom_date(db, iso_date, enabled):
    key = 'zoom_day:' + iso_date
    if enabled:
        db.execute('DELETE FROM kv WHERE key=?', (key,))
        db.commit()
    else:
        kv_set(db, key, '0')


def set_zoom_enabled(db, enabled):
    kv_set(db, 'global_show_zoom', '1' if enabled else '0')


def reply(chat_id, message, db=None):
    # Owner-controlled global preference applies to the group and all DMs.
    if db is not None and not zoom_enabled(db):
        message = re.sub(r'\n🔗 <a href="[^"]*">Подключиться к Zoom</a>', '', message)
        message = message.replace('\n💻 Дистант', '\n🏫 Очная пара')
    # Telegram limits a single message to 4096 characters.
    for chunk in split_message(message):
        tg('sendMessage', {'chat_id': chat_id, 'text': chunk,
                           'parse_mode': 'HTML', 'disable_web_page_preview': True})


def subscribe(db, chat_id):
    db.execute('INSERT OR IGNORE INTO subscribers (chat_id, subscribed_at) VALUES (?, ?)',
               (chat_id, datetime.now(TZ).isoformat()))
    db.commit()


def unsubscribe(db, chat_id):
    db.execute('DELETE FROM subscribers WHERE chat_id=?', (chat_id,))
    db.commit()


def notify_all(db, message):
    """Group first; subscriber failures cannot prevent other notifications."""
    try:
        reply(CHAT_ID, message, db=db)
    except Exception:
        LOG.exception('Не удалось отправить уведомление в группу')
    recipients = db.execute('SELECT chat_id FROM subscribers').fetchall()
    for (chat_id,) in recipients:
        try:
            reply(chat_id, message, db=db)
        except requests.HTTPError as exc:
            status = exc.response.status_code if exc.response is not None else None
            if status in (403, 400):
                unsubscribe(db, chat_id)
                LOG.warning('Подписчик %s удалён после ошибки Telegram %s', chat_id, status)
            else:
                LOG.exception('Ошибка уведомления подписчика %s', chat_id)
        except Exception:
            LOG.exception('Ошибка уведомления подписчика %s', chat_id)


def zoom_change_announcement(db, target_date=None):
    """Notify the group and DM subscribers about the selected lesson format."""
    if target_date is not None:
        label = date_label(target_date)
        remote = zoom_enabled_for_date(db, target_date)
        date_line = f'📅 <b>{html.escape(label)}</b>'
    else:
        remote = zoom_enabled(db)
        date_line = '📅 <b>Все дни расписания</b>'

    format_line = ('💻 Пары будут проходить <b>в дистанционном формате</b>.'
                   if remote else '🏫 Пары будут проходить <b>в очном формате</b>.')
    message = '📢 Изменения расписания КН-26-1\n\n' + date_line + '\n\n' + format_line
    if target_date is None and remote:
        excluded = zoom_disabled_dates(db)
        if excluded:
            message += ('\n\n📅 Исключения (очное обучение): ' + ', '.join(
                html.escape(date_label(d)) for d in excluded))
    return message


def process_updates(db, items):
    def reply(chat_id, message):
        return globals()["reply"](chat_id, message, db=db)
    offset = int(kv_get(db, 'offset') or 0)
    try:
        updates = tg('getUpdates', {'offset': offset, 'timeout': 1, 'allowed_updates': ['message']}, timeout=8)
    except Exception:
        LOG.exception('Telegram getUpdates')
        return
    for u in updates:
        update_id = u['update_id']
        if not claim(db, f'update:{update_id}'):
            offset = max(offset, update_id + 1)
            kv_set(db, 'offset', str(offset))
            continue
        offset = max(offset, update_id + 1)
        kv_set(db, 'offset', str(offset))
        msg = u.get('message', {})
        chat = msg.get('chat', {})
        chat_id = chat.get('id')
        is_private = chat.get('type') == 'private'
        if not is_private and chat_id != CHAT_ID:
            continue
        cmd = (msg.get('text') or '').split(' ', 1)[0].split('@', 1)[0].lower()
        user_id = msg.get('from', {}).get('id')
        if is_private and cmd == '/stop':
            if OWNER_ID and user_id == OWNER_ID:
                reply(chat_id, '🛑 Бот остановлен. Для запуска откройте start_hidden.vbs на компьютере.')
                LOG.info('Бот остановлен владельцем Telegram ID %s', user_id)
                raise SystemExit(0)
            reply(chat_id, '⛔ Нет доступа. Укажите свой TELEGRAM_OWNER_ID в .env.')
            continue
        if is_private and cmd == '/start':
            subscribe(db, chat_id)
            reply(chat_id, '✅ Ты подписан на уведомления КН-26-1!\n'
                           'Буду присылать изменения расписания и напоминания за 10 минут до пар.\n'
                           'Отключить уведомления: /unsubscribe\n'
                           'Команды расписания: /help')
            continue
        if is_private and cmd == '/unsubscribe':
            unsubscribe(db, chat_id)
            reply(chat_id, '🔕 Личные уведомления отключены. Чтобы включить снова, отправь /start.')
            continue
        if is_private and cmd == '/zoom':
            if not OWNER_ID or user_id != OWNER_ID:
                reply(chat_id, '⛔ Эта команда доступна только владельцу бота.')
                continue
            parts = (msg.get('text') or '').strip().split()
            arg = parts[1].lower() if len(parts) > 1 else ''
            if arg in ('list', 'список'):
                dates = zoom_disabled_dates(db)
                text = ('🔗 Zoom глобально: ' + ('включён' if zoom_enabled(db) else 'выключен') +
                        '\n📅 Даты без Zoom: ' +
                        (', '.join(date.fromisoformat(d).strftime('%d.%m.%Y') for d in dates)
                         if dates else 'нет'))
                reply(chat_id, text)
                continue
            if arg in ('clear', 'сброс') and len(parts) == 2:
                changed_dates = zoom_disabled_dates(db)
                db.execute("DELETE FROM kv WHERE key LIKE 'zoom_day:%'")
                db.commit()
                reply(chat_id, '✅ Все исключения по датам удалены. Глобальная настройка не изменилась.')
                if zoom_enabled(db):
                    for changed_date in changed_dates:
                        notify_all(db, zoom_change_announcement(db, changed_date))
                continue
            if len(parts) == 3 and arg in ('on', 'off', 'вкл', 'выкл'):
                try:
                    target_date = datetime.strptime(parts[2], '%d.%m.%Y').date()
                except ValueError:
                    reply(chat_id, '❌ Неверная дата. Пример: /zoom off 16.10.2026')
                    continue
                enabled = arg in ('on', 'вкл')
                iso_date = target_date.isoformat()
                before = zoom_enabled_for_date(db, iso_date)
                set_zoom_date(db, iso_date, enabled)
                after = zoom_enabled_for_date(db, iso_date)
                reply(chat_id, f"📅 {target_date:%d.%m.%Y}: Zoom-ссылки " +
                      ('добавлены ✅' if enabled else 'убраны ❌') +
                      ('\n⚠️ Глобально Zoom выключен, поэтому ссылки пока скрыты везде.'
                       if enabled and not zoom_enabled(db) else ''))
                if before != after:
                    notify_all(db, zoom_change_announcement(db, iso_date))
                continue
            if len(parts) > 2:
                reply(chat_id, 'Используй /zoom off 16.10.2026 или /zoom on 16.10.2026.')
                continue
            if arg in ('on', 'вкл', '1'):
                enabled = True
            elif arg in ('off', 'выкл', '0'):
                enabled = False
            elif not arg:
                enabled = not zoom_enabled(db)
            else:
                reply(chat_id, 'Команды: /zoom on, /zoom off, /zoom off ДД.ММ.ГГГГ, '
                      '/zoom on ДД.ММ.ГГГГ, /zoom list, /zoom clear')
                continue
            before = zoom_enabled(db)
            set_zoom_enabled(db, enabled)
            reply(chat_id, '🔗 Zoom глобально: ' +
                  ('включён ✅ (исключения по датам сохраняются)' if enabled else 'выключен ❌'))
            if before != enabled:
                notify_all(db, zoom_change_announcement(db))
            continue
        now = datetime.now(TZ)
        today = now.date()
        if cmd == '/today':
            reply(chat_id, show_day(items, today, db))
        elif cmd == '/tomorrow':
            reply(chat_id, show_day(items, today + timedelta(days=1), db))
        elif cmd == '/week':
            reply(chat_id, show_week(items, today, db))
        elif cmd == '/nextweek':
            reply(chat_id, show_week(items, today + timedelta(days=7), db))
        elif cmd == '/next':
            reply(chat_id, show_next(items, now, db))
        elif cmd == '/now':
            reply(chat_id, show_now(items, now, db))
        elif cmd in ('/start', '/help'):
            reply(chat_id, '🤖 Расписание КН-26-1\n/today — сегодня\n/tomorrow — завтра\n/week — неделя\n/nextweek — следующая неделя\n/next — следующая пара\n/now — текущая пара\n/help — помощь' + ('\n/unsubscribe — отключить уведомления в ЛС' if is_private else ''))


WEEKDAYS_RU = ('понедельник', 'вторник', 'среда', 'четверг', 'пятница', 'суббота', 'воскресенье')


def date_label(iso_date):
    d = date.fromisoformat(iso_date)
    return f'{WEEKDAYS_RU[d.weekday()]}, {d:%d.%m.%Y}'


def diff_items(old, new, db=None):
    """Compare lessons, always showing the actual date for every change."""
    def indexed(rows):
        return {(x['date'], x['pair'], x['start']): x for x in rows}

    before, after = indexed(old), indexed(new)
    changes = []
    today = datetime.now(TZ).date()
    # Notify through Sunday of the following calendar week, not a rolling 7-day window.
    # Monday = 0, Sunday = 6; next week's Sunday is 13 - today.weekday() days away.
    last_day = today + timedelta(days=13 - today.weekday())
    for key in sorted(before.keys() | after.keys()):
        lesson_day = date.fromisoformat(key[0])
        # Keep the entire fetched timetable in storage even for dates outside this window.
        if not today <= lesson_day <= last_day:
            continue
        a, b = before.get(key), after.get(key)
        if a == b:
            continue
        heading = f'📅 <b>{html.escape(date_label(key[0]))}</b>\n'
        if a is None:
            changes.append(heading + '➕ Добавлена:\n' + pretty(b, db))
        elif b is None:
            changes.append(heading + '➖ Убрана/перенесена:\n' + pretty(a, db))
        else:
            changes.append(heading + '🔄 Изменена:\nБыло: ' + pretty(a, db) + '\nСтало: ' + pretty(b, db))
    return changes


def change_messages(changes):
    header = '📢 Изменения расписания КН-26-1\n\n'
    result = []
    current = header
    for change in changes:
        candidate = current + ('\n\n' if current != header else '') + change
        if len(candidate) > 3500 and current != header:
            result.append(current)
            current = header + change
        else:
            current = candidate
    if current != header:
        result.append(current)
    return result


def reminders(db, items):
    now = datetime.now(TZ)
    for item in items:
        when = datetime.fromisoformat(item['date'] + 'T' + item['start']).replace(tzinfo=TZ)
        delta = (when - now).total_seconds()
        # One-minute window accommodates polling jitter; missed reminders are not sent late.
        if REMINDER * 60 - INTERVAL - 10 <= delta <= REMINDER * 60:
            key = 'remind:' + hashlib.sha256(json.dumps(item, sort_keys=True, ensure_ascii=False).encode()).hexdigest()
            if claim(db, key):
                try:
                    notify_all(db, f'🔔 Через {REMINDER} минут пара!\n\n{pretty(item, db)}')
                except Exception:
                    unclaim(db, key)
                    raise


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--test', action='store_true', help='Fetch and save HTML, print parsed lessons; no Telegram messages')
    args = ap.parse_args()
    if not args.test and (not TOKEN or TOKEN == 'PASTE_YOUR_TOKEN_HERE'):
        raise SystemExit('Укажите TELEGRAM_BOT_TOKEN в .env')
    logging.basicConfig(level=logging.INFO, format='%(asctime)s %(levelname)s %(message)s',
                        handlers=[logging.FileHandler(Path(__file__).with_name('bot.log'), encoding='utf-8'),
                                  logging.StreamHandler()])
    with single_instance():
        run_bot(args)


def run_bot(args):
    db = db_connect()
    os.chdir(Path(__file__).resolve().parent)
    session = requests.Session()
    session.headers.update({'User-Agent': 'Mozilla/5.0 (compatible; KN26ScheduleBot/1.0)'})
    last_fetch = 0.0
    items = json.loads(kv_get(db, 'schedule') or '[]')
    while True:
        now = datetime.now(TZ)
        if args.test or time.monotonic() - last_fetch >= INTERVAL:
            last_fetch = time.monotonic()
            try:
                start = now.date() - timedelta(days=7)
                end = now.date() + timedelta(days=35)
                html = fetch_html(session, start, end)
                if args.test:
                    Path('debug_schedule.html').write_text(html, encoding='utf-8')
                fresh = parse_timetable(html)
                if not fresh:
                    raise ValueError('Таблица распознана, но не найдено ни одной пары; проверка HTML обязательна')
                if args.test:
                    print(f'Получено пар: {len(fresh)}')
                    print(json.dumps(fresh[:15], ensure_ascii=False, indent=2))
                    print('HTML сохранён: debug_schedule.html')
                    break
                previous = kv_get(db, 'schedule')
                if previous is not None:
                    changes = diff_items(items, fresh, db)
                    if changes:
                        # Save only after notification succeeds, so transient Telegram errors retry.
                        messages = change_messages(changes)
                        kv_set(db, 'last_change_messages', json.dumps(messages, ensure_ascii=False))
                        for message in messages:
                            notify_all(db, message)
                items = fresh
                kv_set(db, 'schedule', json.dumps(items, ensure_ascii=False))
                LOG.info('Расписание обновлено: %s пар', len(items))
            except Exception:
                LOG.exception('Ошибка получения/разбора расписания; старые данные сохранены')
                if args.test:
                    raise
        if not args.test:
            try:
                process_updates(db, items)
                reminders(db, items)
            except Exception:
                LOG.exception('Ошибка Telegram')
            time.sleep(5)


if __name__ == '__main__':
    main()
