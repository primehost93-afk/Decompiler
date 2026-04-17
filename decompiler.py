import discord
from discord.ext import commands
import os
import subprocess
import tempfile
import struct
import hashlib
import socket
import datetime
import io
import json
import time
from collections import defaultdict

# ============================================
# إعدادات البوت والسيرفر (من متغيرات البيئة)
# ============================================

BOT_TOKEN = os.getenv("BOT_TOKEN")
UNLUAC_PATH = os.getenv("UNLUAC_PATH", "unluac_20201218.jar")
COMMAND_PREFIX = "!"
SERVER_NAME = "JustScripts"
OWNER_NAME = "Dragon"
UNLIMITED_ROLE_ID = 1475007094997389392

# التحقق من وجود التوكن
if not BOT_TOKEN:
    raise ValueError("BOT_TOKEN not found! Please set it in environment variables.")
# إعدادات الاستخدام
DAILY_LIMIT = 3  # عدد المحاولات اليومية للعضو العادي
COOLDOWN_SECONDS = 10  # فترة الانتظار بين كل عملية والثانية (للرول الخاص)
MAX_FILES_PER_MESSAGE = 2  # الحد الأقصى للملفات في رسالة واحدة

# تخزين بيانات الاستخدام (في الذاكرة - سيتم مسحها عند إعادة تشغيل البوت)
user_usage = defaultdict(lambda: {"count": 0, "last_reset": time.time(), "last_used": 0})
cooldown_users = {}  # تتبع المستخدمين في فترة cooldown

# ============================================
# استخراج الفئات من xteam.py الأصلي
# ============================================

class sha1:
    @staticmethod
    def sha1(data):
        return hashlib.sha1(data).hexdigest().upper()

class Script:
    class ScriptException(Exception):
        pass

    class RSAKey:
        def __init__(self, key):
            if len(key) <= 8:
                raise ValueError("Modulus missing")
            self.raw = key
            self.bitsize = (len(key) - 8) << 2
            self.exp = int.from_bytes(bytearray.fromhex(key[:8]), byteorder='little')
            self.mod = int.from_bytes(bytearray.fromhex(key[8:]), byteorder='little')

        @property
        def bytesize(self):
            return self.bitsize >> 3

        def decrypt_block_int(self, block):
            if self.bytesize < len(block):
                raise ValueError("Block is too large")
            intblock = int.from_bytes(block, byteorder='little')
            return pow(intblock, self.exp, self.mod)

        def decrypt_block_bytes(self, block):
            return self.decrypt_block_int(block).to_bytes(self.bytesize, 'little')

        def __str__(self):
            return "(e:%d, n:%s)" % (self.exp, self.raw[8:])

    RSA_OBFKEY = RSAKey("0100010005B20A3E491EDB02B85E1073E4B3BA6EEA2AF02A361F32A6FA56A89FE7B773B11732F9394E8BF6A6D71F34A68B55AF4266A41AEC82363E8E3F37499818DBE0C9")
    RSA_SIGNKEYS = [
        RSAKey("01000100998C1C031E148F2DDD9783E6F78542B862E7034983CBB9FD78F6836F1F5F82510270C964E1C538CBCA435BE0A6D3EF3174BA0EADB8B26AF89D8E31E0CF4A644C"),
        RSAKey("0100010097E565431323A6FC9557970DFDE25346E00D633B3B51550E9EA374B3B7ED40E4F5707A382B7E70B5FD2349CE3EFB42161FBA68C17580C559F600908932BEA1B3"),
        RSAKey("0100010045FAE258F357B981F2EE0DEB9EAE7C67B85FF1AE1A13BE6CCAE0F3625F7141E8F42728019978B4F8481E7F704E392B794CE5ED5F19BFEBA1E7D33AF00BF6C599")
    ]

    MAGIC = 0xF14A55B7

    def __init__(self, raw, ignore_invalid_magic=False, ignore_invalid_header_offset=False, 
                 ignore_invalid_checksum=False, ignore_invalid_signature=False):
        if not isinstance(raw, bytes):
            if isinstance(raw, str):
                raw = raw.encode("ascii")
            else:
                raise ValueError("The input should be either 'bytes' or 'str'")

        self.raw = raw
        if len(raw) < 157:
            raise self.ScriptException("The input is too small.")

        raw_signature = self.raw[-64:]
        raw_body = self.raw[:-64]
        raw_header = raw_body[-93:]
        raw_scriptcontent = raw_body[:-93]

        const0_1 = struct.unpack("<I", raw_header[0:4])[0]
        const0_2 = struct.unpack("<I", raw_header[4:8])[0]

        self.magic = struct.unpack("<I", raw_header[81:85])[0]
        if not ignore_invalid_magic and self.magic != self.MAGIC:
            raise self.ScriptException("Incorrect magic. Probably not a signed .luac file for MTA:SA.")

        self.header_offset = struct.unpack("<I", raw_header[85:89])[0]
        if not ignore_invalid_header_offset and self.header_offset != len(self.raw) - 157:
            raise self.ScriptException("Incorrect header offset. The script is probably corrupted.")

        self.checksum = struct.unpack("<I", raw_header[89:93])[0]
        self.checksum_calculated = sum(raw_body[:-5])
        if not ignore_invalid_checksum and self.checksum != self.checksum_calculated:
            raise self.ScriptException("Incorrect checksum. The script is probably corrupted.")

        header = bytearray(raw_header)
        for i in range(73):
            header[i + 8] = header[i + 8] ^ (i % 0xC * (i % 0xC) ^ 0x5D ^ (1 << (i & 7)))
        
        compiled_at_ = struct.unpack("BBBBBB", header[8:14])
        self.compiled_at = datetime.datetime(
            2000+compiled_at_[0], compiled_at_[1], compiled_at_[2],
            compiled_at_[3], compiled_at_[4], compiled_at_[5]
        )

        gap1 = header[14:18]
        self.uploaders_ip = socket.inet_ntoa(header[18:22])
        self.min_server_host_version = header[22:35].decode("ascii")
        self.min_server_run_version = header[35:48].decode("ascii")
        self.min_client_run_version = header[48:61].decode("ascii")

        obfuscation_levels_ = {
            "0.0.0-0.00000": 0, "1.3.4-0.00000": 1,
            "1.5.2-9.07903": 2, "1.5.6-9.18728": 3
        }
        self.obfuscation_level = (-1) if self.min_server_run_version not in obfuscation_levels_ else obfuscation_levels_[self.min_server_run_version]

        self.is_lua_bytecode_encrypted = struct.unpack("<I", header[61:65])[0] == 1
        gap2 = header[65:81]

        if self.is_lua_bytecode_encrypted:
            self.lua_bytecode = b""
            encrypted_content_ = raw_scriptcontent[5:-4]
            encrypted_content_length_ = struct.unpack("<I", raw_scriptcontent[-4:])[0]
            if encrypted_content_length_ > len(encrypted_content_):
                raise self.ScriptException("The size of the encrypted data is being funny.")

            for i in range(0, len(encrypted_content_), 64):
                self.lua_bytecode += self.RSA_OBFKEY.decrypt_block_bytes(encrypted_content_[i:i+64])[:min(63, encrypted_content_length_-len(self.lua_bytecode))]
        else:
            self.lua_bytecode = raw_scriptcontent

        self.signature_hash_calculated = sha1.sha1(raw_body)
        self.signature_hash = None
        self.signature_key = None

        for key in self.RSA_SIGNKEYS:
            signature_hash_ = key.decrypt_block_int(raw_signature)
            if signature_hash_.bit_length() > 160:
                continue
            self.signature_hash = "%040x" % (int.from_bytes((signature_hash_).to_bytes(20, byteorder='little'), byteorder='big'))
            if self.signature_hash == self.signature_hash_calculated:
                self.signature_key = key
                break

        if not ignore_invalid_signature and self.signature_key == None:
            raise self.ScriptException("Invalid signature.")

    @property
    def lua_bytecode_without_bom(self):
        return self.lua_bytecode[3:] if self.lua_bytecode.startswith(b"\xef\xbb\xbf") else self.lua_bytecode

    @property
    def is_magic_ok(self):
        return self.magic == self.MAGIC

    @property
    def is_checksum_ok(self):
        return self.checksum == self.checksum_calculated

    @property
    def is_header_offset_ok(self):
        return self.header_offset == len(self.raw)-157

    @property
    def is_signature_ok(self):
        return self.signature_hash_calculated == self.signature_hash


class LuaDeobfuscator:
    class LuaDeobfuscatorException(Exception):
        pass
    
    OP_MOVE = 0x0
    OP_LOADK = 0x1
    OP_LOADBOOL = 0x2
    OP_LOADNIL = 0x3
    OP_GETUPVAL = 0x4
    OP_GETGLOBAL = 0x5
    OP_GETTABLE = 0x6
    OP_SETGLOBAL = 0x7
    OP_SETUPVAL = 0x8
    OP_SETTABLE = 0x9
    OP_NEWTABLE = 0xA
    OP_SELF = 0xB
    OP_ADD = 0xC
    OP_SUB = 0xD
    OP_MUL = 0xE
    OP_DIV = 0xF
    OP_MOD = 0x10
    OP_POW = 0x11
    OP_UNM = 0x12
    OP_NOT = 0x13
    OP_LEN = 0x14
    OP_CONCAT = 0x15
    OP_JMP = 0x16
    OP_EQ = 0x17
    OP_LT = 0x18
    OP_LE = 0x19
    OP_TEST = 0x1A
    OP_TESTSET = 0x1B
    OP_CALL = 0x1C
    OP_TAILCALL = 0x1D
    OP_RETURN = 0x1E
    OP_FORLOOP = 0x1F
    OP_FORPREP = 0x20
    OP_TFORLOOP = 0x21
    OP_SETLIST = 0x22
    OP_CLOSE = 0x23
    OP_CLOSURE = 0x24
    OP_VARARG = 0x25
    OP_MTA_NOP = 0x26
    OP_MTA_XOR = 0x27
    OP_MTA_FAIL = 0x28

    CRYPTTABLE = [
        0x8E, 0x79, 0x64, 0xBB, 0x77, 0xEA, 0x60, 0xD2, 0xCA, 0x3C, 0x1A, 0x1A, 0xC4, 0xC1, 0x98, 0x1E,
        0x1E, 0x61, 0x99, 0xFD, 0xEB, 0x26, 0xAD, 0xC2, 0x3E, 0x87, 0xDC, 0x4B, 0x63, 0x0A, 0x9B, 0xDA,
        0xBC, 0x9D, 0xA8, 0x90, 0x27, 0xD2, 0xBA, 0xAB, 0xE0, 0x49, 0xC0, 0xE7, 0xE3, 0x1D, 0xB9, 0x48,
        0x70, 0x64, 0x4B, 0x6B, 0x69, 0x96, 0xD4, 0xFF, 0x61, 0xDD, 0x37, 0x85, 0x64, 0xD6, 0x10, 0x43,
        0xBA, 0x85, 0xE0, 0x24, 0x0B, 0xFB, 0x1F, 0xC8, 0x24, 0x14, 0x8F, 0x1B, 0x8F, 0x66, 0xF3, 0x20,
        0xDF, 0xBA, 0xEF, 0x36, 0x10, 0x71, 0xE0, 0xFB, 0x0D, 0x1D, 0x99, 0x80, 0x10, 0x51, 0x9B, 0x19,
        0xDB, 0xAB, 0x1D, 0x7E, 0x13, 0xC3, 0xC1, 0xCB, 0x4C, 0xBB, 0xFE, 0x2C, 0x69, 0x94, 0xE7, 0x56,
        0xD5, 0x88, 0x63, 0x16, 0xD5, 0xFB, 0xA1, 0xC4, 0x55, 0x91, 0x5D, 0x6D, 0x51, 0xD7, 0x19, 0x3C,
        0x95, 0x43, 0x66, 0x36, 0x7B, 0xAF, 0xD7, 0x99, 0x75, 0xE5, 0x32, 0xA7, 0x13, 0xA7, 0x5E, 0xF8,
        0x39, 0xAB, 0x57, 0x45, 0x87, 0xDC, 0x8B, 0xA1, 0x09, 0x21, 0x0D, 0xB3, 0xBB, 0xE1, 0x57, 0xEE,
        0xDD, 0x62, 0xC7, 0x23, 0xFC, 0x3F, 0x91, 0xBD, 0x7B, 0xA5, 0xAF, 0x3D, 0xEA, 0x7E, 0x75, 0x49,
        0xC1, 0xB2, 0x0D, 0x4D, 0x65, 0xA9, 0x21, 0x9A, 0xF1, 0x05, 0xA7, 0x63, 0x78, 0x6D, 0x83, 0xF9,
        0xC6, 0x5C, 0xF7, 0xF6, 0xCD, 0xCA, 0x76, 0x7A, 0x7A, 0x2D, 0xE7, 0x84, 0x67, 0xDD, 0x65, 0x99,
        0x26, 0x02, 0xCF, 0x95, 0xA1, 0xC0, 0x32, 0x88, 0xC5, 0x04, 0x92, 0x77, 0xB4, 0xB9, 0x7B, 0x4A,
        0x31, 0x42, 0x5D, 0x18, 0x0C, 0x2C, 0xFA, 0x46, 0x34, 0x76, 0xD9, 0xC2, 0xA7, 0xA4, 0xAC, 0x69,
        0xF0, 0xE1, 0x74, 0x79, 0x28, 0xB0, 0x64, 0xEA, 0x6D, 0x84, 0x86, 0xE6, 0x79, 0xEF, 0xB6, 0xB7
    ]

    @staticmethod
    def lua_mask1(n, p): 
        return ((~((~0)<<n))<<p)
        
    @staticmethod
    def lua_mask0(n, p): 
        return (~LuaDeobfuscator.lua_mask1(n,p))
    
    @staticmethod
    def lua_inst_get(i, i_p, i_s): 
        return (i >> i_p) & LuaDeobfuscator.lua_mask1(i_s, 0)
        
    @staticmethod
    def lua_inst_set(i, o, i_p, i_s): 
        return (i & LuaDeobfuscator.lua_mask0(i_s, i_p)) | ((o << i_p) & LuaDeobfuscator.lua_mask1(i_s, i_p))

    @staticmethod
    def lua_get_opcode(i): 
        return LuaDeobfuscator.lua_inst_get(i, 0, 6)
        
    @staticmethod
    def lua_set_opcode(i, o): 
        return LuaDeobfuscator.lua_inst_set(i, o, 0, 6)

    @staticmethod
    def lua_get_arg_a(i): 
        return LuaDeobfuscator.lua_inst_get(i, 6, 8)
        
    @staticmethod
    def lua_set_arg_a(i, o): 
        return LuaDeobfuscator.lua_inst_set(i, o, 6, 8)

    @staticmethod
    def lua_get_arg_c(i): 
        return LuaDeobfuscator.lua_inst_get(i, 14, 9)
        
    @staticmethod
    def lua_set_arg_c(i, o): 
        return LuaDeobfuscator.lua_inst_set(i, o, 14, 9)

    @staticmethod
    def lua_get_arg_b(i): 
        return LuaDeobfuscator.lua_inst_get(i, 23, 9)
        
    @staticmethod
    def lua_set_arg_b(i, o): 
        return LuaDeobfuscator.lua_inst_set(i, o, 23, 9)

    @staticmethod
    def lua_get_arg_bx(i): 
        return LuaDeobfuscator.lua_inst_get(i, 14, 18)
        
    @staticmethod
    def lua_set_arg_bx(i, o): 
        return LuaDeobfuscator.lua_inst_set(i, o, 14, 18)
    
    @staticmethod
    def lua_get_arg_sbx(i): 
        return LuaDeobfuscator.lua_get_arg_bx(i) - (((1<<18)-1)>>1)
        
    @staticmethod
    def lua_set_arg_sbx(i, o): 
        return LuaDeobfuscator.lua_set_arg_bx(i, o + (((1<<18)-1)>>1))

    def __init__(self, data):
        if not isinstance(data, bytes):
            if isinstance(data, str):
                data = data.encode("ascii")
            else:
                raise ValueError("The input should be either 'bytes' or 'str'")

        self.data = bytearray(data)
        self.n = 0
        self.header = self.parse_header()
        if self.header["signature"] != b"\033Lua":
            raise self.LuaDeobfuscatorException("Not a Lua script. (%s)", self.header["signature"])
        if self.header["version"] != 0x51:
            ver = self.header["version"]
            raise self.LuaDeobfuscatorException("Incompatible Lua version (%X.%X)." % ((ver >> 4 & 0xf), ver & 0xf))
        self.body = self.parse_function()

        if self.n != len(self.data):
            print(f"[WARNING] Extra data found in buffer (size: {len(self.data) - self.n} bytes), ignoring it.")

    def get_data(self):
        return bytes(self.data)

    def parse_data(self, n):
        ret = self.data[self.n:self.n+n]
        self.n += n
        return ret

    @staticmethod
    def bytes_to_int(b): return struct.unpack("<I", b)[0]
    @staticmethod
    def int_to_bytes(b): return struct.pack("<I", b)

    def parse_int(self): return struct.unpack("<I", self.parse_data(4))[0]
    def parse_short(self): return struct.unpack("<H", self.parse_data(2))[0]
    def parse_char(self): return struct.unpack("B", self.parse_data(1))[0]
    def parse_num(self): return struct.unpack("d", self.parse_data(8))[0]
    def parse_vector(self, n, s): return [self.parse_data(s) for i in range(n)]
    def parse_vector_of(self, n, f): return [f() for i in range(n)]
    def parse_int_at(self, i): return self.bytes_to_int(self.data[i:i+4])
    def put_int_at(self, i, n):
        l_ = self.int_to_bytes(n)
        for j in range(4):
            self.data[i+j] = l_[j]

    def parse_string(self):
        size = self.parse_int()
        if size == 0:
            return None
        cryptkey = size >> 24
        size &= 0xffffff
        self.data[self.n-1] = 0
        if cryptkey != 0:
            for i in range(size):
                self.data[self.n+i] ^= self.CRYPTTABLE[cryptkey]
                cryptkey = 0 if cryptkey == len(self.CRYPTTABLE)-1 else cryptkey + 1
        string = self.data[self.n:self.n + size-1]
        self.n += size
        return string

    def parse_header(self):
        header = {}
        header["signature"] = self.parse_data(4)
        header["version"] = self.parse_char()
        header["format"] = self.parse_char()
        header["endianness"] = self.parse_char()
        header["sizeof_int"] = self.parse_char()
        header["sizeof_size_t"] = self.parse_char()
        header["sizeof_instruction"] = self.parse_char()
        header["sizeof_lua_number"] = self.parse_char()
        header["is_lua_number_integral"] = self.parse_char()
        return header

    def parse_code(self):
        size = self.parse_int()
        if size * 4 > len(self.data) - self.n:
            print(f"[WARNING] Code size ({size}) exceeds remaining data, adjusting size.")
            size = (len(self.data) - self.n) // 4
        if size > 0:
            first_inst = self.parse_int_at(self.n)
            if self.lua_get_opcode(first_inst) == 0x27:
                crypt_key = self.lua_get_arg_a(first_inst)
                crypt_size = self.lua_get_arg_bx(first_inst) * 4
                if crypt_size > len(self.data) - self.n:
                    print(f"[WARNING] Encrypted code size ({crypt_size}) exceeds remaining data, adjusting.")
                    crypt_size = len(self.data) - self.n
                back_ptr = crypt_size - 1
                for i in range(crypt_size - 4):
                    self.data[self.n + back_ptr] ^= (i ^ crypt_key ^ (5 * i)) % 256
                    back_ptr -= 1
                if self.parse_int_at(self.n + crypt_size - 4) != 0x80001e:
                    print("[WARNING] Code section does not terminate with a return, proceeding anyway.")
                size -= 1
                self.put_int_at(self.n - 4, size)
                self.data = self.data[:self.n] + self.data[self.n + 4:]
        j = 0
        while j < size:
            i = self.parse_int_at(self.n + 4 * j)
            op = self.lua_get_opcode(i)
            if op == self.OP_MTA_NOP:
                size -= 1
                self.put_int_at(self.n - 4, size)
                self.data = self.data[:self.n + 4 * j] + self.data[self.n + 4 * j + 4:]
            if op in [self.OP_JMP, self.OP_FORLOOP, self.OP_FORPREP]:
                loc = self.lua_get_arg_sbx(i)
                if loc > 60000:
                    loc = 120000 - loc
                self.put_int_at(self.n + 4 * j, self.lua_set_arg_sbx(i, loc))
            j += 1
        return self.parse_vector_of(size, self.parse_int)

    def parse_constants(self):
        constant = {}
        constant["sizek"] = self.parse_int()
        constant["k"] = []
        for i in range(constant["sizek"]):
            val = None
            t = self.parse_char()
            if t == 0:
                val = None
            elif t == 1:
                val = self.parse_char() != 0
            elif t == 3:
                val = self.parse_num()
            elif t == 4:
                val = self.parse_string()
            else:
                print(f"[WARNING] Bad constant type ({t}), skipping.")
                constant["k"].append(None)
                continue
            constant["k"].append(val)
        constant["sizep"] = self.parse_int()
        constant["p"] = self.parse_vector_of(constant["sizep"], self.parse_function)
        return constant

    def parse_debug(self, fun):
        debug = {}
        code_len = len(fun["code"])
        debug["sizelineinfo"] = self.parse_int()
        if debug["sizelineinfo"] != code_len:
            self.put_int_at(self.n - 4, code_len)
            self.data = self.data[:self.n] + self.data[self.n + 4:]
            debug["sizelineinfo"] -= 1
        debug["lineinfo"] = self.parse_vector(debug["sizelineinfo"], 4)
        debug["sizelocvars"] = self.parse_int()
        debug["locvars"] = []
        for i in range(debug["sizelocvars"]):
            lv = {}
            lv["varname"] = self.parse_string()
            lv["startpc"] = self.parse_int()
            lv["endpc"] = self.parse_int()
            debug["locvars"].append(lv)
        debug["sizeupvalues"] = self.parse_int()
        debug["upvalues"] = self.parse_vector_of(debug["sizeupvalues"], self.parse_string)
        return debug

    def parse_function(self):
        fun = {}
        fun["source"] = self.parse_string()
        fun["linedefined"] = self.parse_int()
        fun["lastlinedefined"] = self.parse_int()
        fun["nups"] = self.parse_char()
        fun["numparams"] = self.parse_char()
        fun["is_vararg"] = self.parse_char()
        fun["maxstacksize"] = self.parse_char()
        fun["code"] = self.parse_code()
        fun["constants"] = self.parse_constants()
        fun["debug"] = self.parse_debug(fun)
        return fun


# ============================================
# دوال مساعدة
# ============================================

def check_user_limit(user_id: int, has_unlimited_role: bool) -> tuple:
    """
    التحقق من حدود المستخدم
    Returns: (can_use: bool, message: str, remaining: int)
    """
    current_time = time.time()
    
    # التحقق من مرور 24 ساعة على آخر إعادة تعيين
    if current_time - user_usage[user_id]["last_reset"] >= 86400:
        user_usage[user_id] = {"count": 0, "last_reset": current_time, "last_used": 0}
    
    # إذا كان لديه رول غير محدود
    if has_unlimited_role:
        # التحقق من cooldown
        if user_id in cooldown_users:
            remaining_cooldown = COOLDOWN_SECONDS - (current_time - cooldown_users[user_id])
            if remaining_cooldown > 0:
                return False, f"⏳ Please wait `{remaining_cooldown:.1f}` seconds before next decompilation.", 0
        return True, "", -1  # -1 يعني غير محدود
    
    # للمستخدمين العاديين
    if user_usage[user_id]["count"] >= DAILY_LIMIT:
        # حساب الوقت المتبقي لإعادة التعيين
        time_until_reset = 86400 - (current_time - user_usage[user_id]["last_reset"])
        hours = int(time_until_reset // 3600)
        minutes = int((time_until_reset % 3600) // 60)
        return False, f"❌ You have reached your daily limit (`{DAILY_LIMIT}` decompilations).\n🔄 Reset in: `{hours}h {minutes}m`", 0
    
    remaining = DAILY_LIMIT - user_usage[user_id]["count"]
    return True, "", remaining

def update_user_usage(user_id: int, has_unlimited_role: bool):
    """تحديث استخدام المستخدم"""
    if has_unlimited_role:
        cooldown_users[user_id] = time.time()
    else:
        user_usage[user_id]["count"] += 1
        user_usage[user_id]["last_used"] = time.time()

def analyze_lua_code(lua_source: str) -> dict:
    """
    تحليل الكود المفكك وإرجاع إحصائيات
    """
    lines = lua_source.split('\n')
    non_empty_lines = [l for l in lines if l.strip()]
    
    # عدد الدوال
    function_count = lua_source.count('function')
    
    # عدد المتغيرات المحلية (تقريبي)
    local_vars = lua_source.count('local ')
    
    # عدد الأسطر الفعلية (غير الفارغة)
    code_lines = len(non_empty_lines)
    
    # حجم الكود
    code_size = len(lua_source)
    
    # البحث عن أنماط معينة
    has_loops = 'for ' in lua_source or 'while ' in lua_source or 'repeat ' in lua_source
    has_conditions = 'if ' in lua_source
    has_tables = '{' in lua_source and '}' in lua_source
    
    return {
        "total_lines": len(lines),
        "code_lines": code_lines,
        "empty_lines": len(lines) - code_lines,
        "functions": function_count,
        "local_vars": local_vars,
        "size_bytes": code_size,
        "has_loops": has_loops,
        "has_conditions": has_conditions,
        "has_tables": has_tables
    }

def get_file_info(script: Script) -> dict:
    """
    استخراج معلومات الملف من Script object
    """
    return {
        "compiled_at": script.compiled_at.strftime("%Y-%m-%d %H:%M:%S"),
        "uploaders_ip": script.uploaders_ip,
        "min_server_version": script.min_server_run_version,
        "obfuscation_level": script.obfuscation_level,
        "is_encrypted": script.is_lua_bytecode_encrypted,
        "magic_ok": script.is_magic_ok,
        "checksum_ok": script.is_checksum_ok,
        "signature_ok": script.is_signature_ok
    }

async def process_luac_file(file_data: bytes, filename: str) -> tuple:
    """
    معالجة ملف .luac وإرجاع الكود المفكك مع المعلومات
    """
    try:
        # الخطوة 1: فك تشفير Script (MTA:SA)
        script = Script(
            file_data,
            ignore_invalid_header_offset=True,
            ignore_invalid_checksum=True,
            ignore_invalid_signature=True
        )
        
        file_info = get_file_info(script)
        
        # الخطوة 2: إزالة التشويش باستخدام LuaDeobfuscator
        deobfuscator = LuaDeobfuscator(script.lua_bytecode_without_bom)
        bytecode = deobfuscator.get_data()
        
        # الخطوة 3: استخدام unluac لفك التجميع النهائي
        with tempfile.TemporaryDirectory() as temp_dir:
            temp_luac = os.path.join(temp_dir, "temp.luac")
            
            with open(temp_luac, "wb") as f:
                f.write(bytecode)
            
            try:
                result = subprocess.run(
                    ['java', '-jar', UNLUAC_PATH, temp_luac],
                    capture_output=True,
                    text=True,
                    timeout=30,
                    check=True
                )
                lua_source = result.stdout
                
                if not lua_source or len(lua_source) < 10:
                    return None, None, "Decompiled output is empty or too short"
                
                # تحليل الكود
                code_stats = analyze_lua_code(lua_source)
                
                return lua_source, file_info, code_stats, None
                
            except subprocess.TimeoutExpired:
                return None, None, None, "Decompilation timed out (30s limit)"
            except subprocess.CalledProcessError as e:
                return None, None, None, "Decompilation failed"
            except FileNotFoundError:
                return None, None, None, "Java or unluac not found"
                
    except Script.ScriptException as e:
        return None, None, None, "Invalid or corrupted .luac file"
    except LuaDeobfuscator.LuaDeobfuscatorException as e:
        return None, None, None, "Deobfuscation failed"
    except Exception as e:
        return None, None, None, "Processing failed"

# ============================================
# إعدادات البوت
# ============================================

intents = discord.Intents.default()
intents.message_content = True

bot = commands.Bot(
    command_prefix=COMMAND_PREFIX, 
    intents=intents,
    help_command=None
)

# ============================================
# أحداث البوت
# ============================================

@bot.event
async def on_ready():
    print(f"✅ {SERVER_NAME} Decompiler Bot is ready!")
    print(f"🤖 Logged in as: {bot.user.name}")
    print(f"👑 Owner: {OWNER_NAME}")
    print(f"📊 Connected to {len(bot.guilds)} guilds")
    print(f"⌨️  Command Prefix: {COMMAND_PREFIX}")

@bot.event
async def on_command_error(ctx, error):
    if isinstance(error, commands.CommandNotFound):
        return
    elif isinstance(error, commands.MissingRequiredArgument):
        await ctx.send(f"❌ **Missing Argument**: Use `{COMMAND_PREFIX}bothelp` for usage info.")
    else:
        await ctx.send(f"❌ **Error**: Something went wrong. Please try again later.")

# ============================================
# الأوامر
# ============================================

@bot.command(name="decompile", aliases=["dc", "unluac"])
async def decompile_command(ctx, *, filename: str = None):
    """
    فك تجميع ملف .luac مرفق
    """
    # التحقق من عدد الملفات المرفقة
    if not ctx.message.attachments:
        embed = discord.Embed(
            title="❌ No File Attached",
            description=f"Please attach a `.luac` file!\n\n**Usage:** `{COMMAND_PREFIX}decompile` (with attachment)",
            color=discord.Color.red()
        )
        await ctx.send(embed=embed)
        return
    
    if len(ctx.message.attachments) > MAX_FILES_PER_MESSAGE:
        await ctx.send(f"❌ **Too many files!** Maximum `{MAX_FILES_PER_MESSAGE}` files per message.", delete_after=10)
        return
    
    attachment = ctx.message.attachments[0]
    
    # التحقق من امتداد الملف
    if not attachment.filename.endswith('.luac'):
        await ctx.send("❌ **Invalid file type!** Please upload `.luac` files only.", delete_after=10)
        return
    
    # التحقق من حجم الملف
    if attachment.size > 25 * 1024 * 1024:
        await ctx.send("❌ **File too large!** Maximum size is 25MB.", delete_after=10)
        return
    
    # التحقق من صلاحيات المستخدم (الرول الخاص)
    has_unlimited_role = any(role.id == UNLIMITED_ROLE_ID for role in ctx.author.roles)
    
    # التحقق من الحدود
    can_use, limit_message, remaining = check_user_limit(ctx.author.id, has_unlimited_role)
    if not can_use:
        await ctx.send(limit_message)
        return
    
    # إرسال رسالة المعالجة
    processing_embed = discord.Embed(
        title="🔍 Processing...",
        description=f"Decompiling `{attachment.filename}`...",
        color=discord.Color.blue()
    )
    if not has_unlimited_role and remaining > 0:
        processing_embed.set_footer(text=f"Remaining today: {remaining-1}/{DAILY_LIMIT}")
    
    processing_msg = await ctx.send(embed=processing_embed)
    
    try:
        # قراءة ومعالجة الملف
        file_data = await attachment.read()
        
        lua_source, file_info, code_stats, error = await process_luac_file(file_data, attachment.filename)
        
        if error:
            # رسالة فشل بسيطة بدون تفاصيل تقنية
            fail_embed = discord.Embed(
                title="❌ Decompilation Failed",
                description="Sorry, I couldn't decompile this file. It might be corrupted or use an unsupported format.",
                color=discord.Color.red()
            )
            await processing_msg.edit(embed=fail_embed)
            return
        
        # تحديث استخدام المستخدم
        update_user_usage(ctx.author.id, has_unlimited_role)
        
        # إعداد اسم الملف الناتج مع الترويسة
        base_name = attachment.filename[:-5]
        output_filename = f"[{SERVER_NAME}_{OWNER_NAME}]_{base_name}.lua"
        
        # إضافة الترويسة للكود
        header = f"--[[\n  Decompiled by {OWNER_NAME}\n  Server: {SERVER_NAME}\n  Original: {attachment.filename}\n  Date: {datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n--]]\n\n"
        final_code = header + lua_source
        
        # إعداد معلومات الملف
        info_embed = discord.Embed(
            title="📊 File Information",
            color=discord.Color.blue()
        )
        info_embed.add_field(name="📅 Compiled", value=f"`{file_info['compiled_at']}`", inline=True)
        info_embed.add_field(name="🔒 Encrypted", value="Yes" if file_info['is_encrypted'] else "No", inline=True)
        info_embed.add_field(name="🛡️ Obfuscation", value=f"Level `{file_info['obfuscation_level']}`", inline=True)
        info_embed.add_field(name="📏 Total Lines", value=f"`{code_stats['total_lines']}`", inline=True)
        info_embed.add_field(name="💻 Code Lines", value=f"`{code_stats['code_lines']}`", inline=True)
        info_embed.add_field(name="⚡ Functions", value=f"`{code_stats['functions']}`", inline=True)
        
        # إرسال النتيجة
        if len(final_code) > 1900:
            # إرسال كملف
            file_obj = discord.File(
                io.BytesIO(final_code.encode('utf-8')),
                filename=output_filename
            )
            
            success_embed = discord.Embed(
                title="✅ Decompilation Successful",
                description=f"File was too large, sent as attachment.",
                color=discord.Color.green()
            )
            success_embed.add_field(name="📁 Original", value=f"`{attachment.filename}`", inline=True)
            success_embed.add_field(name="📤 Output", value=f"`{output_filename}`", inline=True)
            
            if not has_unlimited_role:
                success_embed.set_footer(text=f"Remaining today: {remaining-1}/{DAILY_LIMIT}")
            
            await processing_msg.edit(embed=success_embed)
            await ctx.send(embed=info_embed)
            await ctx.send(file=file_obj)
        else:
            # عرض في كود بلوك
            success_embed = discord.Embed(
                title="✅ Decompilation Successful",
                color=discord.Color.green()
            )
            success_embed.add_field(name="📁 File", value=f"`{attachment.filename}`", inline=True)
            success_embed.add_field(name="📊 Size", value=f"`{code_stats['code_lines']}` lines", inline=True)
            
            if not has_unlimited_role:
                success_embed.set_footer(text=f"Remaining today: {remaining-1}/{DAILY_LIMIT}")
            
            code_block = f"```lua\n{final_code}\n```"
            
            await processing_msg.edit(content=None, embed=success_embed)
            await ctx.send(embed=info_embed)
            await ctx.send(code_block)
            
    except Exception as e:
        # رسالة خطأ عامة بدون تفاصيل
        error_embed = discord.Embed(
            title="❌ Error",
            description="An unexpected error occurred. Please try again later.",
            color=discord.Color.red()
        )
        await processing_msg.edit(embed=error_embed)

@bot.command(name="ping")
async def ping_command(ctx):
    """
    فحص حالة البوت
    """
    latency = round(bot.latency * 1000)
    embed = discord.Embed(
        title="🏓 Pong!",
        description=f"Latency: `{latency}ms`",
        color=discord.Color.green()
    )
    embed.set_footer(text=f"{SERVER_NAME} | by {OWNER_NAME}")
    await ctx.send(embed=embed)

@bot.command(name="bothelp", aliases=["help", "cmds"])
async def bothelp_command(ctx):
    """
    عرض معلومات عن البوت والأوامر
    """
    embed = discord.Embed(
        title=f"🔧 {SERVER_NAME} Luac Decompiler",
        description=f"Advanced MTA:SA .luac decompiler by **{OWNER_NAME}**",
        color=discord.Color.dark_red()
    )
    
    embed.add_field(
        name="📌 Commands",
        value=f"""
`{COMMAND_PREFIX}decompile` - Decompile a .luac file (attach file)
`{COMMAND_PREFIX}ping` - Check bot latency
`{COMMAND_PREFIX}setup` - Bot information
`{COMMAND_PREFIX}bothelp` - Show this message
        """,
        inline=False
    )
    
    embed.add_field(
        name="⚙️ Usage Limits",
        value=f"""
• **Normal users**: `{DAILY_LIMIT}` decompilations per day
• **Special role**: Unlimited (with `{COOLDOWN_SECONDS}s` cooldown)
• **Max files**: `{MAX_FILES_PER_MESSAGE}` per message
        """,
        inline=False
    )
    
    embed.add_field(
        name="📝 How to use",
        value=f"1. Attach your `.luac` file\n2. Type `{COMMAND_PREFIX}decompile`\n3. Get your decompiled Lua code!",
        inline=False
    )
    
    embed.set_footer(text=f"{SERVER_NAME} | Created by {OWNER_NAME}")
    await ctx.send(embed=embed)

@bot.command(name="setup")
async def setup_command(ctx):
    """
    معلومات عن البوت والإعدادات
    """
    embed = discord.Embed(
        title=f"⚙️ {SERVER_NAME} Decompiler Bot",
        description="Professional MTA:SA Lua Decompiler",
        color=discord.Color.dark_blue()
    )
    
    embed.add_field(
        name="👑 Owner",
        value=f"**{OWNER_NAME}**",
        inline=True
    )
    
    embed.add_field(
        name="🏢 Server",
        value=f"**{SERVER_NAME}**",
        inline=True
    )
    
    embed.add_field(
        name="🔧 Features",
        value="""
• MTA:SA Script decryption
• Lua 5.1 bytecode deobfuscation
• File analysis & statistics
• Daily usage limits
• Cooldown system for VIP
        """,
        inline=False
    )
    
    embed.add_field(
        name="📊 Current Settings",
        value=f"""
• Daily Limit: `{DAILY_LIMIT}`
• Cooldown: `{COOLDOWN_SECONDS}s`
• Max Files: `{MAX_FILES_PER_MESSAGE}`
        """,
        inline=False
    )
    
    embed.add_field(
        name="💎 VIP Role",
        value=f"Role ID: `{UNLIMITED_ROLE_ID}`\nGet unlimited decompilations!",
        inline=False
    )
    
    embed.set_footer(text=f"{SERVER_NAME} | Developed by {OWNER_NAME}")
    await ctx.send(embed=embed)

# ============================================
# تشغيل البوت
# ============================================

if __name__ == "__main__":
    if BOT_TOKEN == "YOUR_BOT_TOKEN_HERE" or not BOT_TOKEN:
        print("❌ Error: Please set your bot token!")
        exit(1)
    
    if not os.path.exists(UNLUAC_PATH):
        print(f"⚠️  Warning: unluac not found at '{UNLUAC_PATH}'")
    
    print(f"🚀 Starting {SERVER_NAME} Decompiler Bot...")
    print(f"👑 Owner: {OWNER_NAME}")
    

    bot.run(BOT_TOKEN)
