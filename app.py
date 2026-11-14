
import os, threading, time, socket, struct, uuid, random, urllib3, logging, json
from datetime import datetime
from contextlib import asynccontextmanager
import httpx
from google_play_scraper import app as play_scraper
from Crypto.Cipher import AES
from Crypto.Util.Padding import pad
import thunderFF_pb2

from fastapi import FastAPI, HTTPException, Request
from fastapi.responses import JSONResponse, HTMLResponse
from pydantic import BaseModel
import uvicorn

try:
    from core.protocol import (
        openroom, spmroom, SEnd_InV, ExiT, GeT_Status, SPam_Room,
        Join_Room, GeneRaTePk, CrEaTe_ProTo, EnC_PacKeT, DecodE_HeX,
        DeCode_PackEt, EnC_AEs, xBunnEr, ArA_CoLor, EnC_Uid,
    )
except Exception as e:
    raise

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)
logging.basicConfig(
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    level=logging.INFO
)
logger = logging.getLogger(__name__)
API_HOST = os.getenv("API_HOST", "0.0.0.0")
API_PORT = int(os.getenv("API_PORT", "15127"))

# 🔐 كلمة المرور الثابتة
FIXED_PASSWORD = "xkris"

# المسارات العامة (بدون كلمة مرور)
PUBLIC_PATHS = {
    "/", "/docs", "/openapi.json", "/redoc", "/docs/oauth2-redirect",
    "/favicon.ico", "/health",
}

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
ACCOUNTS_FILE = os.path.join(BASE_DIR, 'accounts.txt')

# المدة الثابتة: 5 دقائق
USER_SPAM_TIME = 5 * 60
SOFT_RESTART_INTERVAL = 700

connected_clients, connected_clients_lock = {}, threading.Lock()
all_accounts, all_accounts_lock = {}, threading.Lock()
ACCOUNTS = []
spam_speed = 5.0
spam_running = False
state_lock = threading.Lock()

targets_list, targets_lock = [], threading.Lock()
targets_index = 0
targets_info_cache, targets_info_lock = {}, threading.Lock()
target_states, target_states_lock = {}, threading.Lock()
TARGET_DURATION_SECONDS = USER_SPAM_TIME
MAX_TARGETS = 100
target_expiry_times, target_timers_lock = {}, threading.Lock()

account_rotation_index = 0
account_rotation_lock = threading.Lock()
ACCOUNT_SWITCH_INTERVAL = 30
last_account_switch_time = time.time()
MAX_REQUESTS_PER_ROUND = 7

AES_KEY = b'Yg&tc%DEuh6%Zc^8'
AES_IV  = b'6oyZDr22E3ychjM%'
CF_DNS1, CF_DNS2 = "1.1.1.1", "1.0.0.1"
_DNS_CACHE, _DNS_CACHE_TTL = {}, 300.0
_HTTP_CLIENT = None

room_spam_announced, room_spam_announced_lock = set(), threading.Lock()

# ================== ORIGINAL HELPERS (بدون تغيير) ==================
def _cli():
    global _HTTP_CLIENT
    if _HTTP_CLIENT is None:
        _HTTP_CLIENT = httpx.Client(verify=False, timeout=15.0, limits=httpx.Limits(max_connections=200, max_keepalive_connections=100))
    return _HTTP_CLIENT

def _pb(n, v=None):
    def _varint(x):
        if x < 0: x = (1 << 64) + x
        o = bytearray()
        while True:
            b = x & 0x7F; x >>= 7
            if x: b |= 0x80
            o.append(b)
            if not x: break
        return bytes(o)
    if v is None: return _varint((n << 3) | 0)
    if isinstance(v, bool): v = int(v)
    if isinstance(v, int):  return _varint((n << 3) | 0) + _varint(v)
    if isinstance(v, str):  v = v.encode()
    if isinstance(v, (bytes, bytearray)):
        d = bytes(v)
        return _varint((n << 3) | 2) + _varint(len(d)) + d
    return b""

def _aes_encrypt(payload, key, iv):
    return AES.new(key, AES.MODE_CBC, iv).encrypt(pad(payload, AES.block_size))

def _parse_proto(parsed, want_key=None, default=None):
    out = {}
    for r in parsed:
        fd = {"wire_type": r.wire_type}
        if r.wire_type in ("varint", "string", "bytes"):
            fd["data"] = r.data
        elif r.wire_type == "length_delimited":
            if hasattr(r.data, "results"):
                fd["data"] = _parse_proto(r.data.results)
            elif isinstance(r.data, list):
                fd["data"] = _parse_proto(r.data)
            else:
                fd["data"] = str(r.data)
        out[str(r.field)] = fd
    if want_key is None: return out
    if not out or not isinstance(out, dict): return default
    for k in (want_key, str(want_key)):
        if k in out:
            v = out[k].get('data')
            if v is not None: return v
    return default

def resolve_host(hostname):
    if not hostname: return hostname
    p = hostname.split('.')
    if len(p) == 4 and all(x.isdigit() and 0 <= int(x) <= 255 for x in p): return hostname
    now = time.time()
    if hostname in _DNS_CACHE and now < _DNS_CACHE[hostname][1]: return _DNS_CACHE[hostname][0]
    def _q(srv):
        s = None
        try:
            tid = random.randint(1000, 65535)
            h = struct.pack(">HHHHHH", tid, 0x0100, 1, 0, 0, 0)
            qn = b"".join(bytes([len(x)]) + x.encode() for x in hostname.split('.')) + b"\x00"
            q = h + qn + struct.pack(">HH", 1, 1)
            s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM); s.settimeout(1.2)
            s.sendto(q, (srv, 53)); r, _ = s.recvfrom(1024)
            if len(r) >= 12 and struct.unpack(">H", r[6:8])[0] > 0:
                off = 12 + len(qn) + 4
                for _ in range(struct.unpack(">H", r[6:8])[0]):
                    if off >= len(r): break
                    if (r[off] & 0xC0) == 0xC0: off += 2
                    else:
                        while off < len(r) and r[off] != 0: off += 1 + r[off]
                        off += 1
                    if off + 10 > len(r): break
                    rt, _, _, rl = struct.unpack(">HHIH", r[off:off+10]); off += 10
                    if rt == 1 and rl == 4 and off + 4 <= len(r):
                        return socket.inet_ntoa(r[off:off+4])
                    off += rl
        except Exception: pass
        finally:
            if s:
                try: s.close()
                except Exception: pass
        return None
    ip = _q(CF_DNS1) or _q(CF_DNS2)
    if not ip:
        try: ip = socket.gethostbyname(hostname)
        except Exception: ip = hostname
    if ip: _DNS_CACHE[hostname] = (ip, now + _DNS_CACHE_TTL)
    return ip or hostname

def _version_config():
    try:
        v = play_scraper('com.dts.freefireth', lang='hi', country='id')
        av = v.get("version")
    except Exception:
        av = "1.132.8"
    url = ("https://version.ggwhitehawk.com/live/ver.php"
           f"?version={av}&lang=hi&device=android&channel=android"
           "&appstore=googleplay&region=ME"
           "&whitelist_version=1.3.0&whitelist_sp_version=1.0.0")
    try:
        r = _cli().get(url); r.raise_for_status(); d = r.json()
        su, rv, lrv = d.get("server_url"), d.get("remote_version"), d.get("latest_release_version")
        if su and rv and lrv: return lrv, rv, su
    except Exception: pass
    return None

def _oauth(uid, password):
    url = "https://100067.connect.garena.com/oauth/guest/token/grant"
    h = {"Host": "100067.connect.garena.com", "User-Agent": "Dalvik/2.1.0 (Linux; U; Android 12; SM-G998B Build/SP1A.210812.016)", "Content-Type": "application/x-www-form-urlencoded", "Accept-Encoding": "gzip, deflate, br", "Connection": "close"}
    d = {"uid": uid, "password": password, "response_type": "token", "client_type": "2", "client_secret": "2ee44819e9b4598845141067b281621874d0d5d7af9d8f7e00c1e54715b7d1e3", "client_id": "100067"}
    for _ in range(5):
        try:
            r = _cli().post(url, headers=h, data=d)
            if r.status_code == 200:
                j = r.json()
                oid, at, pl = j.get("open_id"), j.get("access_token"), j.get("platform", 4)
                if oid and at: return oid, at, pl
            if r.status_code == 429: time.sleep(1); continue
        except Exception: pass
        time.sleep(0.5)
    return None

def _build_majorlogin(open_id, access_token, platform, client_version):
    try:
        p = thunderFF_pb2.MajorLoginReq()
        p.event_time = str(datetime.now())[:-7]
        p.game_name = "free fire"; p.platform_id = 1
        p.client_version = str(client_version); p.client_version_code = "2019121229"
        p.system_software = "Android OS 15 / API-35 (AP3A.240905.015.A2/185014)"
        p.system_hardware = "Handheld"; p.device_type = "Handheld"
        p.screen_width = 1600; p.screen_height = 719; p.screen_dpi = "234"
        p.processor_details = "ARM64 FP ASIMD AES | 1820 | 8"
        p.memory = 2798; p.gpu_renderer = "Mali-G57"
        p.gpu_version = "OpenGL ES 3.2 v1.r49p1-04eac0.2848c17a2fd4e9340e06555168eaa3c9"
        p.unique_device_id = f"Google|{uuid.uuid4()}"
        p.client_ip = f"{random.randint(103,223)}.{random.randint(10,250)}.{random.randint(10,250)}.{random.randint(10,250)}"
        p.language = "pt-br"; p.open_id = str(open_id); p.open_id_type = "4"
        p.login_open_id_type = 4; p.access_token = str(access_token)
        p.login_by = 2; p.platform_sdk_id = 1
        p.origin_platform_type = "4"; p.primary_platform_type = "4"
        p.reg_avatar = 1; p.channel_type = 3
        p.telecom_operator = "TUNTEL"; p.network_operator_a = "TUNTEL"
        p.network_type = "WIFI"; p.network_type_a = "WIFI"
        p.cpu_type = 2; p.cpu_architecture = "64"; p.graphics_api = "OpenGLES2"
        p.supported_astc_bitset = 8191
        p.client_using_version = "7428b253defc164018c604a1ebbfebdf"
        p.loading_time = 15078; p.release_channel = "android"
        p.extra_info = "KqsHTx3+QOmBRR1WKvaWewlcpqJBfjki+PPHQoQG8+0yV+Uos7gUFFjHMQ/e7u6han6Fl77r7c3vMN3p8UbKgN+nfycQCgwBmWgBzomx2gj84c+p"
        p.android_engine_init_flag = 111207; p.if_push = 1; p.is_vpn = 0
        ma = p.memory_available; ma.version = 55; ma.hidden_value = 81
        p.external_storage_total = 49973; p.external_storage_available = 11338
        p.internal_storage_total = 854; p.internal_storage_available = 11466
        p.game_disk_storage_total = 49973; p.game_disk_storage_available = 11466
        p.external_sdcard_total_storage = 49973; p.external_sdcard_avail_storage = 11466
        p.library_path = "/data/app/~~lHFxTCCbupG2QVJmsURtZw==/com.dts.freefireth-N3aCHpHNXpdxjD80uIIbww==/lib/arm64"
        p.library_token = "b8e0cd5e295eee42f5860d3c86e483dd|/data/app/~~lHFxTCCbupG2QVJmsURtZw==/com.dts.freefireth-N3aCHpHNXpdxjD80uIIbww==/base.apk"
        base = p.SerializeToString()
        ex = (_pb(96, '{"cur_rate":[90,60,120],"support_etc2":false}')
              + _pb(97, 1) + _pb(99, "4") + _pb(100, "4")
              + _pb(102, b"\x17]ENWU\x0eR5") + _pb(104, 52882)
              + _pb(105, 1)
              + _pb(106, "https://dl.ak.freefiremobile.com/live/ABHotUpdates/|https://core-ak.freefiremobile.com/live/ABHotUpdates/|6b2078db9d22dd98f8e9386a39af8462")
              + _pb(107, "c8e41b7a93f02d56e1a94c7b8203f5d1"))
        return _aes_encrypt(base + ex, AES_KEY, AES_IV)
    except Exception:
        return None

def _post_proto(path, data, release_version, base_url, token=None, decode_major=False):
    try:
        url = f"{base_url.rstrip('/')}/{path}"
        h = {'User-Agent': 'UnityPlayer/2018.4.12f1 (UnityWebRequest/1.0, libcurl/8.5.0-DEV)', 'Connection': 'Keep-Alive', 'Accept-Encoding': 'gzip', 'Content-Type': 'application/x-www-form-urlencoded', 'X-Unity-Version': '2018.4.12f1', 'X-GA-SV': '1789535859', 'X-GA': 'v1 1', 'ReleaseVersion': str(release_version)}
        if token: h['Authorization'] = f"Bearer {token}"
        r = _cli().post(url, headers=h, data=data)
        if r.status_code != 200: return None
        content = r.content
        if decode_major and len(content) < 40: return None
        rp = thunderFF_pb2.MajorLoginRes() if decode_major else thunderFF_pb2.GetLoginDataRes()
        try: rp.ParseFromString(content)
        except Exception: pass
        if decode_major:
            dr = {}
            try:
                from protobuf_decoder.protobuf_decoder import Parser
                dr = _parse_proto(Parser().parse(content.hex()))
            except Exception: pass
            kv  = _parse_proto(dr, 22) or rp.aes_ak
            ivv = _parse_proto(dr, 23) or rp.iv_i
            if isinstance(kv, str):
                try: kv = bytes.fromhex(kv)
                except Exception: pass
            if isinstance(ivv, str):
                try: ivv = bytes.fromhex(ivv)
                except Exception: pass
            if not kv or not ivv:
                for off in range(min(128, len(content))):
                    try:
                        c = thunderFF_pb2.MajorLoginRes(); c.ParseFromString(content[off:])
                        if c.region and c.token: rp = c; break
                    except Exception: pass
            if kv:
                try: rp.aes_ak = kv
                except Exception: pass
            if ivv:
                try: rp.iv_i = ivv
                except Exception: pass
            return rp
        def _rv(buf, p):
            res, sh = 0, 0
            while p < len(buf):
                b = buf[p]; p += 1; res |= (b & 0x7F) << sh
                if not (b & 0x80): break
                sh += 7
            return res, p
        def _ex(raw, fn_):
            try:
                pos, n = 0, len(raw); fields = {}
                while pos < n:
                    try: key, pos = _rv(raw, pos)
                    except Exception: break
                    fn, wt = key >> 3, key & 7
                    try:
                        if wt == 0: val, pos = _rv(raw, pos)
                        elif wt == 2:
                            ln, pos = _rv(raw, pos); val = raw[pos:pos+ln]; pos += ln
                        elif wt == 5: val = raw[pos:pos+4]; pos += 4
                        elif wt == 1: val = raw[pos:pos+8]; pos += 8
                        else: break
                    except Exception: break
                    fields.setdefault(fn, []).append(val)
                if fn_ in fields:
                    v = fields[fn_][0]
                    return v.decode('utf-8','ignore') if isinstance(v, bytes) else str(v)
            except Exception: return None
        try:
            for off in range(0, min(80, len(content))):
                fa = _ex(content[off:], 14); ia = _ex(content[off:], 32)
                if fa and ":" in fa and ia and ":" in ia:
                    rp.functional_addrs = fa; rp.informational_addrs = ia; break
        except Exception: pass
        return rp
    except Exception:
        return None

def _new_login_flow(uid, password):
    vc = _version_config()
    if vc is None: return None
    release_version, client_version, server_url = vc
    tg = _oauth(uid, password)
    if tg is None: return None
    open_id, access_token, platform = tg
    payload = _build_majorlogin(open_id, access_token, platform, client_version)
    if payload is None: return None
    ml = _post_proto("MajorLogin", payload, release_version, server_url, decode_major=True)
    if ml is None: return None
    gl = _post_proto("GetLoginData", payload, release_version, ml.url, token=ml.token)
    if gl is None: return None
    acc_id = str(ml.account_id)
    if not acc_id or acc_id in ("0", "None"): return None
    fa, ia = gl.functional_addrs, gl.informational_addrs
    if not isinstance(fa, str) or ":" not in fa: fa = None
    if not isinstance(ia, str) or ":" not in ia: ia = None
    kv, ivv = ml.aes_ak, ml.iv_i
    if not isinstance(kv, (bytes, bytearray)) or len(kv) < 16: kv = AES_KEY
    if not isinstance(ivv, (bytes, bytearray)) or len(ivv) < 16: ivv = AES_IV
    return {"account_id": acc_id, "token": ml.token, "server_time": ml.server_time, "aes_ak": kv, "iv_i": ivv, "functional_addrs": fa, "informational_addrs": ia, "release_version": release_version, "server_url": ml.url}

def _build_auth(mode, account_uid, token, ts, key, iv):
    ct = AES.new(key, AES.MODE_CBC, iv).encrypt(pad(token.encode("utf-8"), 16))
    uid_b = int(account_uid).to_bytes(8, "big")
    ts_b  = int(ts).to_bytes(4, "big")
    if mode == "online": return (bytes.fromhex("830c") + uid_b + ts_b + len(ct).to_bytes(8, "big") + ct).hex()
    if mode == "chat": return (bytes.fromhex("6d19") + uid_b + ts_b + len(ct).to_bytes(4, "big") + ct).hex()
    raise ValueError(f"unknown auth mode: {mode}")

# ================== إدارة الأهداف ==================
def _targets_snapshot():
    with targets_lock:  return targets_list.copy()

def _target_is_running(uid):
    with target_states_lock: return target_states.get(str(uid).strip(), True)

def _target_time_left(uid):
    with target_timers_lock:
        exp = target_expiry_times.get(str(uid))
    if exp is None: return None
    return max(0, int(exp - time.time()))

def _target_purge(uid):
    uid = str(uid).strip()
    with target_timers_lock:   target_expiry_times.pop(uid, None)
    with target_states_lock:   target_states.pop(uid, None)
    with targets_info_lock:    targets_info_cache.pop(uid, None)
    with room_spam_announced_lock: room_spam_announced.discard(uid)

def _targets_add(uid):
    """يضيف هدف بمدة 5 دقائق ثابتة"""
    uid = str(uid).strip()
    if not uid.isdigit(): return False
    removed = None
    with targets_lock:
        if uid in targets_list: return False
        if len(targets_list) >= MAX_TARGETS:
            removed = targets_list.pop(0)
        targets_list.append(uid)
    if removed is not None: _target_purge(removed)
    with target_timers_lock:
        target_expiry_times[uid] = time.time() + TARGET_DURATION_SECONDS
    with target_states_lock:
        target_states[uid] = True
    return True

def _targets_remove(uid):
    uid = str(uid).strip()
    with targets_lock:
        if uid not in targets_list: return False
        targets_list.remove(uid)
    _target_purge(uid)
    return True

def _target_expiry_worker():
    while True:
        now = time.time()
        with target_timers_lock:
            expired = [u for u, e in list(target_expiry_times.items()) if e <= now]
        for u in expired:
            _targets_remove(u)
            logger.info(f"[EXPIRY] target {u} finished 5 minutes — removed automatically")
        time.sleep(1)

# ================== SOFT RESTART ==================
def force_restart_accounts():
    try:
        print("[RESTART] Starting soft restart...")
        with connected_clients_lock:
            clients_to_kill = list(connected_clients.values())
            connected_clients.clear()
        for c in clients_to_kill:
            try:
                c.running = False
                if c.CliEnts: c.CliEnts.close()
                if c.CliEnts2: c.CliEnts2.close()
            except Exception: pass
        time.sleep(2)
        for acc in ACCOUNTS:
            def _start(a=acc):
                try: FF_CLient(a['id'], a['password'])
                except Exception as e: print(f"[RESTART] Failed {a['id']}: {e}")
            threading.Thread(target=_start, daemon=True).start()
            time.sleep(0.1)
        print(f"[RESTART] Restarted {len(ACCOUNTS)} accounts (targets & spam intact)")
    except Exception as e:
        print(f"[RESTART] Error: {e}")

def soft_restart_worker():
    print(f"[RESTART] Soft restart worker — every {SOFT_RESTART_INTERVAL}s")
    time.sleep(30)
    while True:
        try:
            time.sleep(SOFT_RESTART_INTERVAL)
            force_restart_accounts()
        except Exception as e:
            print(f"[RESTART-WORKER] Error: {e}")
            time.sleep(60)

# ================== FF CLIENT (بدون تغيير) ==================
class FF_CLient:
    def __init__(self, id, password):
        self.id = id
        self.password = password
        self.key = None
        self.iv = None
        self.CliEnts = None
        self.CliEnts2 = None
        self.running = True
        self.room_opened = False
        self.spam_thread_started = False
        self.send_lock = threading.Lock()
        self.account_uid = None
        self.JwT_ToKen = None
        self.chat_auth_hex = None
        self.online_auth_hex = None
        self.request_count = 0
        self.last_send_time = 0
        threading.Thread(target=self.start_client, daemon=True).start()

    def _set_status(self, status):
        with all_accounts_lock:
            if self.id in all_accounts: all_accounts[self.id]['status'] = status

    def start_client(self):
        while self.running:
            self._set_status('connecting')
            try:
                self.get_tok(); return
            except Exception:
                self._set_status('offline'); time.sleep(2)

    def get_tok(self):
        while self.running:
            try:
                result = _new_login_flow(self.id, self.password)
                if not result:
                    self._set_status('connecting'); time.sleep(2); continue
                self.JwT_ToKen   = result["token"]
                self.account_uid = result["account_id"]
                self.AccounT_Uid = self.account_uid
                self.key, self.iv = result["aes_ak"], result["iv_i"]
                fa, ia = result["functional_addrs"], result["informational_addrs"]
                if not fa or ":" not in fa or not ia or ":" not in ia:
                    time.sleep(2); continue
                ip, port   = fa.rsplit(":", 1)
                ip2, port2 = ia.rsplit(":", 1)
                self.online_auth_hex = _build_auth("online", int(self.AccounT_Uid), self.JwT_ToKen, int(result["server_time"]), self.key, self.iv)
                self.chat_auth_hex = _build_auth("chat", int(self.AccounT_Uid), self.JwT_ToKen, int(result["server_time"]), self.key, self.iv)
                threading.Thread(target=self.Chat_TCP_Loop, args=(ip2, port2), daemon=True).start()
                time.sleep(2)
                t = threading.Thread(target=self.Online_TCP_Loop, args=(ip, port), daemon=True)
                t.start(); t.join(timeout=30)
                return
            except Exception:
                self._set_status('connecting'); time.sleep(2)

    def _keepalive_loop(self, sock_attr):
        while self.running and getattr(self, sock_attr):
            time.sleep(20)
            try:
                s = getattr(self, sock_attr)
                if s: s.send(bytes.fromhex("0219"))
            except Exception: break

    def Chat_TCP_Loop(self, ip, port):
        while self.running:
            try:
                self.CliEnts = socket.create_connection((resolve_host(ip), int(port)))
                self.CliEnts.settimeout(30)
                self.CliEnts.send(bytes.fromhex(self.chat_auth_hex))
                threading.Thread(target=self._keepalive_loop, args=("CliEnts",), daemon=True).start()
                while self.running:
                    try:
                        data = self.CliEnts.recv(9999)
                        if not data: break
                        hx = data.hex()
                        if hx.startswith(("0200", "0300")):
                            try: self.CliEnts.send(bytes.fromhex("0219"))
                            except Exception: pass
                    except socket.timeout: continue
                    except Exception: break
                try: self.CliEnts.close()
                except Exception: pass
                self.CliEnts = None
            except Exception:
                self.CliEnts = None
            if self.running: time.sleep(3)

    def Online_TCP_Loop(self, ip, port):
        while self.running:
            try:
                self.CliEnts2 = socket.create_connection((resolve_host(ip), int(port)))
                self.CliEnts2.settimeout(30)
                self.CliEnts2.send(bytes.fromhex(self.online_auth_hex))
                if not self.room_opened:
                    try:
                        self.CliEnts2.send(openroom(self.key, self.iv))
                        self.room_opened = True
                    except Exception: pass
                with connected_clients_lock:
                    connected_clients[self.id] = self
                self._set_status('online')
                print(f"{self.id} CONNECTED SUCCESFULLY [SPAM ROOM]")
                self.start_continuous_spam()
                threading.Thread(target=self._keepalive_loop, args=("CliEnts2",), daemon=True).start()
                while self.running:
                    try:
                        data = self.CliEnts2.recv(99999)
                        if not data: break
                        hx = data.hex()
                        if hx.startswith(("0200", "0300")):
                            try: self.CliEnts2.send(bytes.fromhex("0219"))
                            except Exception: pass
                    except socket.timeout: continue
                    except Exception: break
                try: self.CliEnts2.close()
                except Exception: pass
                self.CliEnts2 = None
                self.room_opened = False
                with connected_clients_lock:
                    connected_clients.pop(self.id, None)
                self._set_status('connecting')
            except Exception:
                with connected_clients_lock:
                    connected_clients.pop(self.id, None)
                self._set_status('connecting')
            if self.running: time.sleep(2)

    def start_continuous_spam(self):
        if self.spam_thread_started: return
        self.spam_thread_started = True

        def spam_loop():
            global targets_index, account_rotation_index, last_account_switch_time
            while self.running:
                try:
                    with state_lock:
                        if not spam_running:
                            time.sleep(0.5); continue
                    now = time.time()
                    if now - last_account_switch_time >= ACCOUNT_SWITCH_INTERVAL:
                        with account_rotation_lock:
                            account_rotation_index = 0
                            last_account_switch_time = now
                            with connected_clients_lock:
                                for c in connected_clients.values():
                                    c.request_count = 0
                    with targets_lock:
                        if not targets_list:
                            time.sleep(1); continue
                        target = targets_list[targets_index % len(targets_list)]
                        targets_index += 1
                    if not _target_is_running(target):
                        time.sleep(0.05); continue
                    try:
                        with connected_clients_lock:
                            online_clients = list(connected_clients.values())
                        if not online_clients:
                            time.sleep(1); continue
                        with account_rotation_lock:
                            start = account_rotation_index
                            found = False
                            for attempts in range(len(online_clients)):
                                idx = (start + attempts) % len(online_clients)
                                cand = online_clients[idx]
                                if cand.request_count < MAX_REQUESTS_PER_ROUND:
                                    active = cand
                                    account_rotation_index = (idx + 1) % len(online_clients)
                                    found = True
                                    break
                            if not found:
                                with connected_clients_lock:
                                    for c in connected_clients.values():
                                        c.request_count = 0
                                time.sleep(1); continue
                        if active == self:
                            elapsed = now - self.last_send_time
                            if elapsed < spam_speed:
                                time.sleep(spam_speed - elapsed)
                            with self.send_lock:
                                if self.CliEnts2 and self.key and self.iv:
                                    self.CliEnts2.send(spmroom(self.key, self.iv, int(target)))
                                    self.CliEnts2.send(SEnd_InV(1, int(target), self.key, self.iv))
                                    self.request_count += 1
                                    self.last_send_time = time.time()
                                    with room_spam_announced_lock:
                                        if target not in room_spam_announced:
                                            room_spam_announced.add(target)
                                            print(f"🚀 SPAM ROOM STARTED SUCCESSFULLY TO ID => {target}")
                                else:
                                    time.sleep(1); continue
                        else:
                            time.sleep(0.1); continue
                    except Exception:
                        time.sleep(1); continue
                    time.sleep(0.2)
                except Exception:
                    time.sleep(1)
        threading.Thread(target=spam_loop, daemon=True).start()

# ================== START ACCOUNTS ==================
def start_accounts():
    global ACCOUNTS
    threading.Thread(target=_target_expiry_worker, daemon=True).start()
    time.sleep(1)
    accs = []
    try:
        if os.path.exists(ACCOUNTS_FILE):
            with open(ACCOUNTS_FILE, "r", encoding="utf-8") as f:
                for raw in f:
                    line = raw.strip()
                    if not line or line.startswith('#') or ':' not in line: continue
                    uid, pwd = line.split(':', 1)
                    uid, pwd = uid.strip(), pwd.strip()
                    if uid.isdigit() and pwd: accs.append({'id': uid, 'password': pwd})
    except Exception: pass
    ACCOUNTS = accs
    if not ACCOUNTS:
        print("No accounts"); return
    print(f"LOADED {len(ACCOUNTS)} from accounts.txt [SPAM ROOM MODE]")
    with all_accounts_lock:
        for a in ACCOUNTS:
            all_accounts[a['id']] = {'id': a['id'], 'password': a['password'], 'status': 'offline'}
    for acc in ACCOUNTS:
        def _start(acc=acc):
            try: FF_CLient(acc['id'], acc['password'])
            except Exception:
                with all_accounts_lock:
                    if acc['id'] in all_accounts: all_accounts[acc['id']]['status'] = 'offline'
                time.sleep(1)
        threading.Thread(target=_start, daemon=True).start()
        time.sleep(0.05)

# ================== FastAPI ==================
@asynccontextmanager
async def lifespan(app: FastAPI):
    threading.Thread(target=start_accounts, daemon=True).start()
    threading.Thread(target=soft_restart_worker, daemon=True).start()
    logger.info(f"🚀 API STARTED on http://{API_HOST}:{API_PORT}")
    logger.info(f"📖 Docs: http://{API_HOST}:{API_PORT}/docs")
    logger.info(f"🔐 Password: {FIXED_PASSWORD}")
    logger.info(f"⏱️  Fixed duration: {TARGET_DURATION_SECONDS}s (5 min auto-stop)")
    yield
    logger.info("🛑 API STOPPING")

app = FastAPI(
    title="FreeFire Room Spam API",
    description="سبام روم فقط — 5 دقائق ثابت لكل هدف (إيقاف تلقائي) — محمي بكلمة مرور",
    version="3.1.0",
    lifespan=lifespan,
)

# 🔐 Middleware للتحقق من كلمة المرور
@app.middleware("http")
async def auth_middleware(request: Request, call_next):
    path = request.url.path.rstrip("/") or "/"
    if path in PUBLIC_PATHS or path.startswith("/docs") or path.startswith("/redoc"):
        return await call_next(request)
    password = request.headers.get("X-Password") or request.query_params.get("password")
    if password != FIXED_PASSWORD:
        return JSONResponse(
            status_code=401,
            content={
                "detail": "Unauthorized — wrong or missing password",
                "how_to": "Pass X-Password header or ?password= query",
            }
        )
    return await call_next(request)

# ---- Models ----
class RoomReq(BaseModel):
    uid: str

# ---- HTML Helper ----
def _html_page(title, message, color="#00c853"):
    return f"""<!DOCTYPE html>
<html dir="rtl" lang="ar"><head><meta charset="utf-8">
<title>{title}</title>
<style>
body {{ font-family: Arial, sans-serif; background: #0d0d0d; color: #fff;
        display: flex; align-items: center; justify-content: center;
        min-height: 100vh; margin: 0; padding: 20px; }}
.box {{ background: #1a1a1a; padding: 40px 50px; border-radius: 18px;
        border: 3px solid {color}; text-align: center; max-width: 520px;
        box-shadow: 0 0 40px {color}33; }}
h1 {{ color: {color}; margin: 0 0 20px; font-size: 28px; }}
p {{ font-size: 18px; line-height: 1.8; margin: 10px 0; }}
.small {{ color: #666; font-size: 13px; margin-top: 25px;
          padding-top: 15px; border-top: 1px solid #333; }}
</style></head>
<body><div class="box">
<h1>{title}</h1>
<p>{message}</p>
<div class="small">FreeFire Room Spam API • 5 min auto-stop</div>
</div></body></html>"""

# ---- Endpoints ----
@app.get("/")
def root():
    return {
        "name": "FreeFire Room Spam API",
        "status": "online",
        "docs": "/docs",
        "duration_seconds": TARGET_DURATION_SECONDS,
        "auth": "X-Password header or ?password= query",
        "quick_start": "/start?uid=UID&password=xkris",
    }

@app.get("/health")
def health():
    return {"status": "ok", "time": time.time()}

@app.get("/api/status")
def api_status():
    with all_accounts_lock:
        online = sum(1 for a in all_accounts.values() if a.get('status') == 'online')
        total = len(all_accounts)
    return {
        "accounts_online": online,
        "accounts_total": total,
        "room_targets_count": len(_targets_snapshot()),
        "spam_running": spam_running,
        "fixed_duration_seconds": TARGET_DURATION_SECONDS,
    }

@app.get("/api/list")
def api_list():
    tgs = _targets_snapshot()
    rooms = []
    for t in tgs:
        rooms.append({
            "uid": t,
            "time_left_seconds": _target_time_left(t),
        })
    return {
        "room_targets": rooms,
        "count": len(rooms),
        "duration_seconds": TARGET_DURATION_SECONDS,
    }

@app.post("/api/room")
def api_room(req: RoomReq):
    global spam_running
    uid = str(req.uid).strip()
    if not uid.isdigit():
        raise HTTPException(400, "uid must be numeric")
    if uid in _targets_snapshot():
        raise HTTPException(409, "target already running")
    if _targets_add(uid):
        with state_lock:
            spam_running = True
        logger.info(f"[ROOM] started for {uid} — will auto-stop in 5 min")
        return {
            "success": True,
            "uid": uid,
            "duration_seconds": TARGET_DURATION_SECONDS,
            "expires_in_minutes": TARGET_DURATION_SECONDS // 60,
            "auto_stop": True,
        }
    raise HTTPException(500, "failed to add target")

@app.post("/api/xroom")
def api_xroom(req: RoomReq):
    global spam_running
    uid = str(req.uid).strip()
    if _targets_remove(uid):
        with state_lock:
            if not _targets_snapshot():
                spam_running = False
        logger.info(f"[ROOM] stopped for {uid}")
        return {"success": True, "uid": uid}
    raise HTTPException(404, "target not found")

@app.post("/api/stopall")
def api_stopall():
    global spam_running
    with targets_lock:
        targets_list.clear()
    with target_timers_lock:
        target_expiry_times.clear()
    with target_states_lock:
        target_states.clear()
    with targets_info_lock:
        targets_info_cache.clear()
    with room_spam_announced_lock:
        room_spam_announced.clear()
    with state_lock:
        spam_running = False
    logger.info("[ROOM] stopall executed")
    return {"success": True, "message": "all room spam stopped"}

# ================== 🆕 GET Endpoints (روابط مباشرة) ==================

@app.get("/start", response_class=HTMLResponse)
def api_start_get(uid: str = ""):
    """🆕 بدء السبام من رابط مباشر — مثال: /start?uid=123456&password=xkris"""
    global spam_running
    uid = str(uid).strip()
    if not uid:
        return _html_page("⚠️ ناقص UID", "أضف <b>?uid=YOUR_ID</b> للرابط<br>مثال: <code>/start?uid=123456789&password=xkris</code>", "#ff9800")
    if not uid.isdigit():
        return _html_page("❌ UID غير صحيح", "الـ UID لازم يكون أرقام فقط<br>المدخل: <b>" + uid + "</b>", "#e63946")
    if uid in _targets_snapshot():
        left = _target_time_left(uid) or 0
        return _html_page("⚠️ موجود بالفعل", f"الهدف <b>{uid}</b> شغال بالفعل<br>متبقي: <b>{left}</b> ثانية<br>سيوقف تلقائياً", "#ff9800")
    if _targets_add(uid):
        with state_lock:
            spam_running = True
        logger.info(f"[ROOM-GET] started for {uid}")
        return _html_page(
            "✅ تم بدء السبام",
            f"الهدف: <b>{uid}</b><br>المدة: <b>5 دقائق</b><br>سيوقف تلقائياً بعد انتهاء المدة",
            "#00c853"
        )
    return _html_page("❌ فشل", "تعذر إضافة الهدف — حاول مرة أخرى", "#e63946")

@app.get("/stop", response_class=HTMLResponse)
def api_stop_get(uid: str = ""):
    """🆕 إيقاف السبام من رابط مباشر — مثال: /stop?uid=123456&password=xkris"""
    global spam_running
    uid = str(uid).strip()
    if not uid:
        return _html_page("⚠️ ناقص UID", "أضف <b>?uid=YOUR_ID</b> للرابط", "#ff9800")
    if _targets_remove(uid):
        with state_lock:
            if not _targets_snapshot():
                spam_running = False
        logger.info(f"[ROOM-GET] stopped for {uid}")
        return _html_page("🛑 تم الإيقاف", f"تم إيقاف السبام على <b>{uid}</b>", "#ff9800")
    return _html_page("⚠️ غير موجود", f"الهدف <b>{uid}</b> غير موجود في القائمة", "#ff9800")

@app.get("/stopall", response_class=HTMLResponse)
def api_stopall_get():
    """🆕 إيقاف كل الأهداف من رابط مباشر — /stopall?password=xkris"""
    global spam_running
    with targets_lock: targets_list.clear()
    with target_timers_lock: target_expiry_times.clear()
    with target_states_lock: target_states.clear()
    with targets_info_lock: targets_info_cache.clear()
    with room_spam_announced_lock: room_spam_announced.clear()
    with state_lock: spam_running = False
    logger.info("[ROOM-GET] stopall")
    return _html_page("🛑 تم إيقاف الكل", "تم حذف جميع الأهداف بنجاح", "#ff9800")

@app.get("/list", response_class=HTMLResponse)
def list_get():
    """🆕 عرض الأهداف في صفحة HTML جميلة"""
    tgs = _targets_snapshot()
    if not tgs:
        return _html_page("📋 لا توجد أهداف", "القائمة فارغة — أضف هدف عبر <b>/start?uid=...</b>", "#888")
    rows = ""
    for t in tgs:
        left = _target_time_left(t) or 0
        rows += f'<tr><td style="padding:10px;border-bottom:1px solid #333">{t}</td><td style="padding:10px;border-bottom:1px solid #333;color:#00c853"><b>{left}s</b></td></tr>'
    return f"""<!DOCTYPE html><html dir="rtl"><head><meta charset="utf-8"><title>الأهداف</title>
<style>body{{font-family:Arial;background:#0d0d0d;color:#fff;padding:40px;display:flex;justify-content:center}}
.box{{background:#1a1a1a;padding:30px 40px;border-radius:18px;border:2px solid #00c853;max-width:600px;width:100%}}
h1{{color:#00c853;text-align:center}}table{{width:100%;border-collapse:collapse;margin-top:20px}}
th{{background:#222;padding:12px;text-align:right;color:#00c853}}td{{padding:10px}}</style></head>
<body><div class="box"><h1>📋 الأهداف النشطة ({len(tgs)})</h1>
<table><tr><th>UID</th><th>الوقت المتبقي</th></tr>{rows}</table>
<p style="text-align:center;color:#666;margin-top:20px">تحديث تلقائي كل 5 ثواني <a href="/list?password=xkris" style="color:#00c853">⟳</a></p>
<script>setTimeout(()=>location.reload(),5000)</script>
</div></body></html>"""

# ================== RUN ==================
if __name__ == "__main__":
    uvicorn.run(app, host=API_HOST, port=API_PORT, log_level="info")