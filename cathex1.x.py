# pr hexeditcatv0.1.py
"""
cathex edit 0.1  --  pr build
Hex Fiend-inspired hex editor with console header awareness.
Atari 2600 -> Switch 2.  Pure stdlib + tkinter, single file.

  * virtual-rendered hex/ASCII canvas: scrolls a 512 MB image at 60 fps
  * nibble-accurate caret, insert/overwrite, full undo/redo, bookmarks
  * 40-console signature DB: detect, parse headers, jump to fields, verify checksums
  * live data inspector, find/replace (hex, ascii, ?? wildcards, regex)

Run:  python3 pr_hexeditcatv0.1.py [file ...]
"""

from __future__ import annotations

import binascii
import mmap
import os
import re
import struct
import sys
import time
import tkinter as tk
from tkinter import filedialog, messagebox, simpledialog, ttk
from tkinter import font as tkfont

APP = "cathex edit 0.1"
BUILD = "pr build"
MAX_MEM = int(os.environ.get("CATHEX_MAXMEM", 512 * 1024 * 1024))

# --------------------------------------------------------------------------
# theme -- Hex Fiend palette
# --------------------------------------------------------------------------
LIGHT = dict(
    chrome="#ECECEC", panel="#F5F5F7", field="#FFFFFF", ascii="#F7F7F9",
    fg="#1D1D1F", dim="#8A8A8E", faint="#C7C7CC", sel="#B3D7FF", sel_fg="#000000",
    caret="#0A84FF", changed="#FFF1B8", changed_fg="#7A4F00", hi="#E4F0FF",
    ruler="#F2F2F4", gutter="#EDEDF0", border="#D2D2D7", accent="#0A84FF",
    ok="#1B7F3B", bad="#C0392B",
)
DARK = dict(
    chrome="#1F1F22", panel="#26262A", field="#131316", ascii="#17171A",
    fg="#E8E8EA", dim="#8A8A8E", faint="#3A3A40", sel="#2E4A73", sel_fg="#FFFFFF",
    caret="#4DA3FF", changed="#4A3E12", changed_fg="#FFD98A", hi="#1C2531",
    ruler="#222226", gutter="#1B1B1E", border="#3A3A40", accent="#4DA3FF",
    ok="#4CD07A", bad="#FF6B5E",
)

MONO = ("Menlo", "Consolas", "DejaVu Sans Mono", "Courier New")

CIC_CRC = {0x6170A4A1: 6101, 0x90BB6CB5: 6102, 0x0B050EE0: 6103,
           0x98BC2C86: 6105, 0xACC8580A: 6106}
CIC_SEED = {6101: 0xF8CA4DDC, 6102: 0xF8CA4DDC, 6103: 0xA3886759,
            6105: 0xDF26F436, 6106: 0x1FEA617A}
N64_MAGIC = {b"\x80\x37\x12\x40": "z64", b"\x37\x80\x40\x12": "v64",
             b"\x40\x12\x37\x80": "n64", b"\x80\x37\x12\x41": "z64"}
GB_LOGO = bytes.fromhex("CEED6666CC0D000B03730083000C000D0008111F8889000EDCCC6EE6DDDDD999BBBB67636E0EECCCDDDC999FBBB9333E")
GBA_LOGO = bytes.fromhex("24FFAE51699AA2213D84820A84E409AD11248B98C0817F21A352BE1993093D84A264B3AFC09A1A7A4B9BF5DB8FF82BE1C7000000000000000000000000000000")


# --------------------------------------------------------------------------
# helpers
# --------------------------------------------------------------------------
def be16(b, o): return (b[o] << 8) | b[o + 1]
def be32(b, o): return (b[o] << 24) | (b[o + 1] << 16) | (b[o + 2] << 8) | b[o + 3]
def le16(b, o): return b[o] | (b[o + 1] << 8)
def le32(b, o): return b[o] | (b[o + 1] << 8) | (b[o + 2] << 16) | (b[o + 3] << 24)
def u64(b, o, le=True):
    return int.from_bytes(bytes(b[o:o + 8]), "little" if le else "big")
def printable(x): return chr(x) if 32 <= x < 127 else "."


def parse_hex_pattern(text):
    """'DE AD ?? EF' or 'DEAD??EF' -> regex over bytes."""
    t = re.sub(r"[\s,_]", "", text)
    if not t or len(t) % 2:
        return None
    out = bytearray()
    for i in range(0, len(t), 2):
        pair = t[i:i + 2]
        out += b"." if pair == "??" else re.escape(bytes([int(pair, 16)]))
    return re.compile(bytes(out), re.S)


def looks_like_hex_clipboard(text):
    """True when clipboard text is Hex Fiend / hex-dump style (not prose)."""
    if not text or not text.strip():
        return False
    cleaned = re.sub(r"(?i)0x", "", text)
    cleaned = re.sub(r"[\s,;:_|\-]", "", cleaned)
    if not cleaned or len(cleaned) % 2:
        return False
    if not re.fullmatch(r"[0-9A-Fa-f]+", cleaned):
        return False
    # Prefer hex when spaced pairs, dense hex, or short binary paste
    if re.search(r"(?i)\b[0-9A-F]{2}(?:[\s,;:_]+[0-9A-F]{2})+\b", text):
        return True
    if len(cleaned) >= 2 and all(c in "0123456789abcdefABCDEF" for c in cleaned):
        # Avoid treating plain words like "babe" / "dead" as hex unless dense
        # or the original is mostly hex digits / whitespace.
        non_ws = re.sub(r"\s+", "", text)
        hexish = sum(1 for c in non_ws if c in "0123456789abcdefABCDEF,;:_-|xX")
        return hexish >= max(2, int(0.85 * len(non_ws)))
    return False


def clipboard_to_bytes(text):
    """Decode clipboard like Hex Fiend: hex dump if it looks like hex, else latin-1."""
    if text is None:
        return b""
    if looks_like_hex_clipboard(text):
        cleaned = re.sub(r"(?i)0x", "", text)
        cleaned = re.sub(r"[\s,;:_|\-]", "", cleaned)
        try:
            return bytes.fromhex(cleaned)
        except ValueError:
            pass
    return text.encode("latin-1", "replace")


def bytes_to_hex_clipboard(data, spaced=True):
    data = bytes(data)
    if spaced:
        return data.hex(" ").upper()
    return data.hex().upper()


def bytes_to_ascii_clipboard(data):
    """Latin-1 round-tripable text (binary-safe for paste-back)."""
    return bytes(data).decode("latin-1")


def crc32_std(data, start, length):
    return binascii.crc32(bytes(data[start:start + length])) & 0xFFFFFFFF


def rol(v, b):
    b &= 31
    return ((v << b) | (v >> (32 - b))) & 0xFFFFFFFF


# --------------------------------------------------------------------------
# console signature database
# --------------------------------------------------------------------------
class Console:
    def __init__(self, name, family, magic=None, off=0, fields=(), exts=(),
                 probe=None, verify=None, note="", container=False):
        self.name, self.family = name, family
        self.magic, self.off = magic, off
        self.fields, self.exts = fields, exts
        self.probe, self.verify, self.note = probe, verify, note
        self.container = container

    def match(self, data, path):
        score = 0
        if self.magic:
            if self.magic in (b"NES\x1a", b"FDS\x1a", b"XBEH", b"XEX2",
                              b"\x7fPKG", b"\x7fCNT", b"PS-X EXE"):
                if data[:len(self.magic)] == self.magic:
                    score = 100
            elif data[self.off:self.off + len(self.magic)] == self.magic:
                score = 100
            else:
                head = bytes(data[:0x10000])
                if self.container and self.magic in head:
                    score = 88
        if not score and self.probe:
            try:
                score = 70 if self.probe(data, path) else 0
            except Exception:
                score = 0
        if score and self.exts and path:
            if os.path.splitext(path)[1].lower() in self.exts:
                score += 8
        return score


def _atari2600(data, path):
    n = len(data)
    if n not in (2048, 4096, 8192, 16384, 32768, 65536, 131072):
        return False
    ext = os.path.splitext(path or "")[1].lower()
    if ext in (".a26", ".bin"):
        return True
    return data[0] in (0x00, 0x78, 0x80, 0xA9, 0x85, 0xAD, 0x4C, 0x20) and data[n - 2] != 0


def _snes(data, path):
    n = len(data)
    for hdr in (0, 512):
        body = n - hdr
        if body in (0x8000, 0x10000, 0x20000, 0x40000, 0x80000, 0x100000) or \
           (body % 0x8000 == 0 and 0x8000 <= body <= 0x800000):
            base = hdr + (0x7FDC if body <= 0x40000 else 0xFFDC)
            if base + 4 <= n:
                csum, comp = le16(data, base), le16(data, base + 2)
                if (csum ^ comp) == 0xFFFF and csum:
                    return True
    return os.path.splitext(path or "")[1].lower() in (".sfc", ".smc")


def _jaguar(data, path):
    return len(data) > 0x10 and data[0] == 0 and data[1] == 0 and \
        bytes(data[2:5]) == b"JAG" and bytes(data[8:13]) == b"ATARI"


def _pce(data, path):
    n = len(data)
    return n % 0x2000 == 0 and 0x8000 <= n <= 0x100000 and \
        os.path.splitext(path or "")[1].lower() in (".pce", ".sgx")


def _switch2(data, path):
    head = bytes(data[:0x4000])
    if b"Switch 2" in head or b"Switch2" in head or b"NX2" in head:
        return True
    if head[0x100:0x104] == b"HEAD" and len(head) > 0x160:
        return head[0x159] >= 4 or head[0x158] >= 2
    return False


def _n64(data, path):
    return bytes(data[:4]) in N64_MAGIC


def _gbc(data, path):
    return bytes(data[0x104:0x134]) == GB_LOGO[:48] and data[0x143] & 0x80


def _gb(data, path):
    return bytes(data[0x104:0x134]) == GB_LOGO[:48]


def _gba(data, path):
    return bytes(data[4:4 + len(GBA_LOGO)]) == GBA_LOGO


def _nds(data, path):
    return bytes(data[0xC0:0xC4]) == b"\x24\xFF\xAE\x56"


def _ps2(data, path):
    if bytes(data[:4]) == b"\x7fELF":
        return True
    head = bytes(data[:0x20000])
    return b"BOOT2" in head or b"BOOT" in head[:0x1000]


def _switch_family(data, path):
    head = bytes(data[:0x400])
    for m in (b"HEAD", b"PFS0", b"NRO0", b"NSO0", b"NCA3", b"NCA2", b"META", b"KIP1", b"HFS0"):
        if m in head:
            return True
    return False


def _xbox_one(data, path):
    head = bytes(data[:0x1000])
    return b"msft-xvd" in head or b"XVD" in head or b"MICROSOFT*XBOX*MEDIA" in bytes(data[:0x30000])


# --- checksum verifiers: return [(label, expected, actual, ok), ...] -------
def v_nes(d):
    prg = d[4] * 0x4000
    chr_ = d[5] * 0x2000
    off = 16 + (512 if d[6] & 0x04 else 0)
    if off + prg + chr_ > len(d):
        return []
    s = sum(bytes(d[off:off + prg])) & 0xFFFF
    out = [("PRG checksum (mod 64K)", 0, s, s == 0)]
    if chr_:
        c = sum(bytes(d[off + prg:off + prg + chr_])) & 0xFFFF
        out.append(("CHR checksum (mod 64K)", 0, c, c == 0))
    return out


def v_snes(d):
    n = len(d)
    hdr = 512 if (n - 512) % 0x8000 == 0 and n % 0x8000 != 0 else 0
    body = n - hdr
    if body < 0x8000:
        return []
    base = hdr + (0x7FDC if body <= 0x40000 else 0xFFDC)
    if base + 4 > n:
        return []
    csum, comp = le16(d, base), le16(d, base + 2)
    total = 0
    for i in range(hdr, n, 2):
        total += le16(d, i)
    total &= 0xFFFF
    return [("Checksum complement", 0xFFFF, csum ^ comp, (csum ^ comp) == 0xFFFF),
            ("Checksum vs ROM sum", total, csum, total == csum)]


def v_gb(d):
    h = sum(bytes(d[0x134:0x14D])) + 0x19
    h = (~h + 1) & 0xFF if False else ((0 - h) & 0xFF)
    tot = (sum(bytes(d)) - d[0x14E] - d[0x14F]) & 0xFFFF
    return [("Header checksum", d[0x14D], h, d[0x14D] == h),
            ("Global checksum", be16(d, 0x14E), tot, be16(d, 0x14E) == tot)]


def v_gba(d):
    comp = (-(sum(bytes(d[0xA0:0xBD])) + 0x19)) & 0xFF
    chk = (sum(bytes(d[0xA0:0xBD])) - 0x19) & 0xFF
    return [("Header complement", d[0xBD], comp, d[0xBD] == comp),
            ("Header checksum", d[0xBE], chk, d[0xBE] == chk)]


def v_genesis(d):
    tot = 0
    for i in range(0x200, len(d), 2):
        tot = (tot + be16(d, i)) & 0xFFFF
    return [("ROM checksum", be16(d, 0x18E), tot, be16(d, 0x18E) == tot)]


def v_n64(d):
    if len(d) < 0x101000:
        return [("CRC (needs 1 MB)", 0, 0, False)]
    try:
        cic = CIC_CRC.get(crc32_std(d, 0x40, 0x1000 - 0x40))
    except Exception:
        cic = None
    if cic is None:
        return [("Boot chip", 0, 0, False)]
    seed = CIC_SEED[cic]
    t1 = t2 = t3 = t4 = t5 = t6 = seed
    for i in range(0x1000, 0x101000, 4):
        x = be32(d, i)
        if (t6 + x) & 0xFFFFFFFF < t6:
            t4 = (t4 + 1) & 0xFFFFFFFF
        t6 = (t6 + x) & 0xFFFFFFFF
        t3 ^= x
        r = rol(x, x & 0x1F)
        t5 = (t5 + r) & 0xFFFFFFFF
        if t2 > x:
            t2 ^= r
        else:
            t2 ^= t6 ^ x
        if cic == 6105:
            t1 = (t1 + (be32(d, 0x40 + 0x710 + (i & 0xFF)) ^ x)) & 0xFFFFFFFF
        else:
            t1 = (t1 + (t5 ^ x)) & 0xFFFFFFFF
    if cic == 6103:
        c1, c2 = ((t6 ^ t4) + t3) & 0xFFFFFFFF, ((t5 ^ t2) + t1) & 0xFFFFFFFF
    elif cic == 6106:
        c1, c2 = ((t6 * t4) + t3) & 0xFFFFFFFF, ((t5 * t2) + t1) & 0xFFFFFFFF
    else:
        c1, c2 = t6 ^ t4 ^ t3, t5 ^ t2 ^ t1
    return [("CIC-NUS-%d detected" % cic, 0, 0, True),
            ("CRC1", be32(d, 0x10), c1, be32(d, 0x10) == c1),
            ("CRC2", be32(d, 0x14), c2, be32(d, 0x14) == c2)]


def F(o, n, label, kind="bytes", extra=None):
    return (o, n, label, kind, extra)


CONSOLES = [
    # ---------------------------------------------------------------- Atari
    Console("Atari 2600", "Atari", exts=(".a26", ".bin"), probe=_atari2600, fields=(
        F(0x00, 8, "Start of code"), F(-4, 2, "Reset vector", "u16le"),
        F(-2, 2, "IRQ vector", "u16le")), note="no header -- cart type from size"),
    Console("Atari 7800", "Atari", b"\x01ATARI7800", exts=(".a78",), fields=(
        F(0x00, 1, "Header version", "u8"), F(0x01, 9, "Signature", "ascii"),
        F(0x11, 32, "Cart title", "ascii"), F(0x31, 1, "Cartridge type", "u8"),
        F(0x32, 1, "Controller 1", "u8"), F(0x33, 1, "Controller 2", "u8"),
        F(0x34, 1, "TV type", "u8"), F(0x35, 1, "Save device", "u8"),
        F(0x80, 0, "ROM starts here"))),
    Console("Atari Lynx", "Atari", b"LYNX", exts=(".lnx",), container=True, fields=(
        F(0x00, 4, "Magic", "ascii"), F(0x06, 32, "Cart name", "ascii"),
        F(0x3A, 1, "Manufacturer", "u8"), F(0x40, 4, "Magic (2)", "ascii"),
        F(0x4A, 1, "Rotation", "u8"))),
    Console("Atari Jaguar", "Atari", exts=(".jag", ".rom"), probe=_jaguar, fields=(
        F(0x02, 3, "Signature", "ascii"), F(0x08, 5, "Publisher", "ascii"))),
    Console("Atari 8-bit (XEX)", "Atari", b"\xff\xff", exts=(".xex", ".atr")),
    # ------------------------------------------------------------- Nintendo
    Console("NES / Famicom", "Nintendo", b"NES\x1a", exts=(".nes",), verify=v_nes, fields=(
        F(0x00, 4, "Signature", "ascii"), F(0x04, 1, "PRG ROM (16K units)", "u8"),
        F(0x05, 1, "CHR ROM (8K units)", "u8"),
        F(0x06, 1, "Flags 6", "flags", [(0, "mirroring: horizontal"), (1, "mirroring: vertical"),
                                        (2, "battery"), (3, "512B trainer"), (4, "ignore mirroring")]),
        F(0x07, 1, "Flags 7", "flags", [(0, "VS Unisystem"), (1, "PlayChoice-10"),
                                        (2, "NES 2.0"), (3, "mapper hi")]),
        F(0x08, 1, "Mapper (lo nibble)", "u8"), F(0x09, 1, "PRG CHR size (v2)", "u8"),
        F(0x0A, 1, "PRG RAM size (v2)", "u8"), F(0x10, 0, "PRG ROM"),
        F(0x2000, 0, "CHR ROM (if present)"))),
    Console("Famicom Disk System", "Nintendo", b"FDS\x1a", exts=(".fds",)),
    Console("SNES / Super Famicom", "Nintendo", exts=(".sfc", ".smc"), probe=_snes, verify=v_snes, fields=(
        F(0x7FC0, 21, "Title", "ascii"), F(0x7FD5, 1, "Map mode", "u8"),
        F(0x7FD6, 1, "Cart type", "u8"), F(0x7FD7, 1, "ROM size", "u8"),
        F(0x7FD8, 1, "SRAM size", "u8"), F(0x7FD9, 1, "Region", "u8"),
        F(0x7FDA, 1, "Licensee", "u8"), F(0x7FDB, 1, "Version", "u8"),
        F(0x7FDC, 2, "Checksum", "u16le"), F(0x7FDE, 2, "Complement", "u16le"),
        F(0x7FE0, 4, "Unused", "hex"), F(0x7FE4, 10, "Maker", "ascii")),
        note="offsets shown for LoROM; add 512 if a copier header is present"),
    Console("Nintendo 64", "Nintendo", exts=(".z64", ".n64", ".v64"), probe=_n64, verify=v_n64, fields=(
        F(0x00, 1, "PI BSD domain", "u8"), F(0x01, 1, "Clockrate", "u8"),
        F(0x02, 4, "Entry point", "hex"), F(0x08, 4, "Release", "hex"),
        F(0x10, 4, "CRC1", "hex"), F(0x14, 4, "CRC2", "hex"),
        F(0x20, 20, "Internal name", "ascii"), F(0x3B, 4, "Game ID", "ascii"),
        F(0x3E, 1, "Country", "u8"), F(0x3F, 1, "Version", "u8")),
        note="byte order is checked -- z64 / v64 / n64 all detected"),
    Console("Game Boy / Color", "Nintendo", exts=(".gb", ".gbc"), probe=_gb, verify=v_gb, fields=(
        F(0x100, 4, "Entry point", "hex"), F(0x104, 48, "Nintendo logo", "hex"),
        F(0x134, 16, "Title", "ascii"), F(0x143, 1, "CGB flag", "flags",
          [(7, "Game Boy Color")]), F(0x144, 2, "New licensee", "ascii"),
        F(0x146, 1, "SGB flag", "u8"), F(0x147, 1, "Cart type", "u8"),
        F(0x148, 1, "ROM size", "u8"), F(0x149, 1, "RAM size", "u8"),
        F(0x14A, 1, "Destination", "u8"), F(0x14B, 1, "Old licensee", "u8"),
        F(0x14C, 1, "Version", "u8"), F(0x14D, 1, "Header checksum", "hex"),
        F(0x14E, 2, "Global checksum", "hex"))),
    Console("Game Boy Advance", "Nintendo", exts=(".gba",), probe=_gba, verify=v_gba, fields=(
        F(0x00, 4, "Entry point", "hex"), F(0x04, 156, "Nintendo logo", "hex"),
        F(0xA0, 12, "Title", "ascii"), F(0xAC, 4, "Game code", "ascii"),
        F(0xB0, 2, "Maker code", "ascii"), F(0xB2, 1, "Fixed 0x96", "hex"),
        F(0xB3, 1, "Main unit code", "u8"), F(0xB4, 1, "Device type", "u8"),
        F(0xBC, 1, "Version", "u8"), F(0xBD, 1, "Complement", "hex"),
        F(0xBE, 2, "Checksum", "hex"))),
    Console("Nintendo DS", "Nintendo", exts=(".nds",), probe=_nds, fields=(
        F(0x00, 12, "Title", "ascii"), F(0x0C, 4, "Game code", "ascii"),
        F(0x10, 2, "Maker code", "ascii"), F(0x12, 1, "Unit code", "u8"),
        F(0x13, 1, "Encryption seed", "u8"), F(0x14, 1, "Device capacity", "u8"),
        F(0x1E, 1, "ROM version", "u8"), F(0x20, 4, "ARM9 ROM offset", "u32le"),
        F(0x24, 4, "ARM9 entry", "u32le"), F(0x28, 4, "ARM9 RAM addr", "u32le"),
        F(0x2C, 4, "ARM9 size", "u32le"), F(0x30, 4, "ARM7 ROM offset", "u32le"),
        F(0x34, 4, "ARM7 entry", "u32le"), F(0x38, 4, "ARM7 RAM addr", "u32le"),
        F(0x3C, 4, "ARM7 size", "u32le"), F(0x15E, 2, "Header CRC", "hex"))),
    Console("Nintendo DSi", "Nintendo", b"TWL", off=0x0C, exts=(".nds", ".dsi")),
    Console("Nintendo 3DS", "Nintendo", b"NCSD", exts=(".3ds", ".cia", ".cci"), container=True),
    Console("GameCube", "Nintendo", exts=(".gcm", ".iso"), container=True,
            probe=lambda d, p: len(d) > 0x20 and be32(d, 0x1C) == 0xC2339F3D, fields=(
        F(0x00, 6, "Game code", "ascii"), F(0x06, 2, "Maker code", "ascii"),
        F(0x08, 1, "Disc number", "u8"), F(0x1C, 4, "Magic", "hex"),
        F(0x20, 64, "Game title", "ascii"))),
    Console("Wii", "Nintendo", exts=(".iso", ".wbfs"), container=True,
            probe=lambda d, p: len(d) > 0x20 and be32(d, 0x18) == 0x5D1C9EA3, fields=(
        F(0x00, 6, "Game code", "ascii"), F(0x18, 4, "Magic", "hex"),
        F(0x20, 64, "Game title", "ascii"))),
    Console("Wii U", "Nintendo", b"WUP-", off=0x100, container=True),
    Console("Switch", "Nintendo", b"HEAD", off=0x100, container=True,
            probe=_switch_family, fields=(
        F(0x100, 4, "Magic", "ascii"), F(0x104, 4, "ROM area start page", "u32le"),
        F(0x108, 4, "Backup area start page", "u32le"), F(0x10C, 4, "Key area start page", "u32le"),
        F(0x110, 6, "SECURE magic", "ascii"), F(0x120, 8, "Firmware version", "hex"),
        F(0x140, 8, "Gamecard size", "hex"), F(0x158, 1, "Gamecard version", "u8"),
        F(0x159, 1, "Cart type", "u8")),
        note="XCI: HEAD@0x100  NSP/NSZ: PFS0@0  NRO: NRO0  NSO: NSO0  NCA: NCA3@0"),
    Console("Switch 2", "Nintendo", container=True, probe=_switch2, fields=(
        F(0x100, 4, "Magic (HEAD)", "ascii"), F(0x104, 4, "ROM area start page", "u32le"),
        F(0x140, 8, "Gamecard size", "hex"), F(0x158, 1, "Gamecard version", "u8"),
        F(0x159, 1, "Cart type", "u8")),
        note="same PFS0/HFS0/HEAD containers as Switch; NCA key generation differs"),
    # ---------------------------------------------------------------- Sega
    Console("Mega Drive / Genesis", "Sega", b"SEGA", off=0x100, exts=(".md", ".gen", ".bin"),
            verify=v_genesis, fields=(
        F(0x100, 16, "Console name", "ascii"), F(0x110, 16, "Copyright", "ascii"),
        F(0x120, 48, "Domestic name", "ascii"), F(0x150, 48, "Overseas name", "ascii"),
        F(0x180, 14, "Product code", "ascii"), F(0x18E, 2, "Checksum", "hex"),
        F(0x190, 16, "IO support", "ascii"), F(0x1F0, 16, "Region", "ascii"))),
    Console("Mega CD", "Sega", b"SEGA MEGA CD", off=0x100),
    Console("32X", "Sega", b"SEGA 32X", off=0x100),
    Console("Master System", "Sega", b"TMR SEGA", off=0x7FF0, exts=(".sms",), fields=(
        F(0x7FF0, 8, "Signature", "ascii"), F(0x7FFC, 2, "Checksum", "hex"),
        F(0x7FFF, 1, "Region / size", "flags", [(4, "region hi")]))),
    Console("Game Gear", "Sega", b"TMR SEGA", off=0x7FF0, exts=(".gg",), fields=(
        F(0x7FF0, 8, "Signature", "ascii"), F(0x7FFC, 2, "Checksum", "hex"))),
    Console("Saturn", "Sega", b"SEGA SEGASATURN", exts=(".bin", ".iso"), container=True, fields=(
        F(0x00, 16, "Hardware ID", "ascii"), F(0x20, 10, "Product code", "ascii"),
        F(0x40, 112, "Title", "ascii"), F(0xE0, 8, "Region", "ascii"))),
    Console("Dreamcast", "Sega", b"SEGA SEGAKATANA", exts=(".gdi", ".cdi", ".iso"), container=True, fields=(
        F(0x00, 16, "Hardware ID", "ascii"), F(0x40, 128, "Title", "ascii"),
        F(0x80, 8, "Maker ID", "ascii"), F(0xC0, 8, "Region", "ascii"))),
    # ---------------------------------------------------------------- Sony
    Console("PlayStation", "Sony", b"PS-X EXE", exts=(".exe", ".psx"), fields=(
        F(0x00, 8, "Magic", "ascii"), F(0x10, 4, "Text size", "u32le"),
        F(0x14, 4, "Data size", "u32le"), F(0x18, 4, "Entry point", "u32le"),
        F(0x1C, 4, "Text addr", "u32le"), F(0x30, 4, "Stack base", "u32le"),
        F(0x800, 0, "Payload"))),
    Console("PlayStation (disc)", "Sony", b"CD001", off=0x8001, container=True,
            probe=lambda d, p: len(d) > 0x8002 and bytes(d[0x8001:0x8006]) == b"CD001"),
    Console("PlayStation 2", "Sony", exts=(".elf", ".iso"), probe=_ps2, container=True, fields=(
        F(0x00, 4, "ELF magic", "hex"), F(0x18, 4, "Entry point", "u32le"),
        F(0x1C, 4, "Program headers", "u32le"), F(0x20, 4, "Section headers", "u32le"))),
    Console("PlayStation 3", "Sony", b"\x7fPKG", exts=(".pkg",), container=True, fields=(
        F(0x00, 4, "Magic", "hex"), F(0x04, 4, "Version", "u32be"),
        F(0x08, 4, "Metadata offset", "u32be"), F(0x10, 8, "Header size", "hex"))),
    Console("PSP", "Sony", b"\x00PBP", exts=(".pbp",), container=True,
            probe=lambda d, p: bytes(d[:4]) == b"\x00PBP" and b"PSP" in bytes(d[:0x1000]), fields=(
        F(0x00, 4, "Magic", "ascii"), F(0x04, 4, "Version", "u32le"),
        F(0x08, 4, "PARAM.SFO offset", "u32le"), F(0x0C, 4, "ICON0 offset", "u32le"))),
    Console("PlayStation 4", "Sony", b"\x7fCNT", exts=(".pkg",), container=True,
            probe=lambda d, p: bytes(d[:4]) == b"\x7fCNT" and b"PS4" in bytes(d[:0x20000]), fields=(
        F(0x00, 4, "Magic", "hex"), F(0x04, 4, "Entry count", "u32be"),
        F(0x08, 2, "Entry table type", "u16be"))),
    Console("PlayStation 5", "Sony", b"\x7fCNT", exts=(".pkg",), container=True,
            probe=lambda d, p: bytes(d[:4]) == b"\x7fCNT" and b"PS5" in bytes(d[:0x20000]), fields=(
        F(0x00, 4, "Magic", "hex"), F(0x04, 4, "Entry count", "u32be"),
        F(0x08, 2, "Entry table type", "u16be"))),
    # ----------------------------------------------------------- Microsoft
    Console("Xbox", "Microsoft", b"XBEH", exts=(".xbe",), fields=(
        F(0x00, 4, "Magic", "ascii"), F(0x04, 256, "Signature", "hex"),
        F(0x104, 4, "Base address", "u32le"), F(0x118, 4, "Entry point", "u32le"),
        F(0x12C, 4, "Kernel version", "hex"))),
    Console("Xbox 360", "Microsoft", b"XEX2", exts=(".xex",), fields=(
        F(0x00, 4, "Magic", "ascii"), F(0x04, 4, "Module flags", "hex"),
        F(0x08, 4, "Header size", "u32be"), F(0x10, 4, "Image size", "u32be"))),
    Console("Xbox One / Series", "Microsoft", exts=(".xvd",), container=True,
            probe=_xbox_one, fields=(F(0x200, 8, "msft-xvd signature", "ascii"),)),
    # -------------------------------------------------------------- others
    Console("Neo Geo", "SNK", b"NEO-GEO", off=0x100, fields=(
        F(0x100, 8, "Signature", "ascii"), F(0x108, 16, "Title", "ascii"))),
    Console("PC Engine / TG16", "NEC", exts=(".pce", ".sgx"), probe=_pce),
    Console("WonderSwan", "Bandai", b"WONDERSWAN", exts=(".ws", ".wsc")),
    Console("ColecoVision", "Coleco", b"\xaa\x55", exts=(".col",)),
    Console("Intellivision", "Mattel", exts=(".int", ".bin"),
            probe=lambda d, p: len(d) in (0x2000, 0x4000, 0x8000, 0x10000) and
            os.path.splitext(p or "")[1].lower() == ".int"),
    Console("Vectrex", "GCE", b"g GCE", exts=(".vec",)),
    Console("MSX", "ASCII", b"AB", exts=(".rom", ".mx1", ".mx2")),
    Console("ZX Spectrum", "Sinclair", exts=(".tap", ".tzx", ".z80", ".sna")),
    Console("Commodore 64", "Commodore", exts=(".prg", ".d64", ".crt")),
]

FAMILIES = []
for c in CONSOLES:
    if c.family not in FAMILIES:
        FAMILIES.append(c.family)


def detect_console(data, path):
    best, score = None, 0
    for c in CONSOLES:
        s = c.match(data, path)
        if s > score:
            best, score = c, s
    return (best, min(score, 100)) if best else (None, 0)


def field_value(data, off, length, kind, endian="le"):
    n = len(data)
    o = off if off >= 0 else n + off
    if o < 0 or o >= n:
        return "-"
    raw = bytes(data[o:o + max(length, 1)])
    try:
        if kind == "ascii":
            return "".join(printable(b) for b in raw)
        if kind == "hex":
            return raw.hex(" ").upper()
        if kind == "u8":
            return str(raw[0])
        if kind == "u16le":
            return "0x%04X (%d)" % (le16(raw, 0), le16(raw, 0))
        if kind == "u16be":
            return "0x%04X (%d)" % (be16(raw, 0), be16(raw, 0))
        if kind == "u32le":
            return "0x%08X (%d)" % (le32(raw, 0), le32(raw, 0))
        if kind == "u32be":
            return "0x%08X (%d)" % (be32(raw, 0), be32(raw, 0))
        if kind == "flags":
            on = [lab for bit, lab in ([] if not length else [])]
            if not isinstance(length, int) or length == 0:
                pass
            v = raw[0]
            return ", ".join(lab for bit, lab in (kind_extra or []) if v & (1 << bit)) or "0x%02X" % v
    except Exception:
        return "?"
    return raw.hex(" ").upper()


# --------------------------------------------------------------------------
# document
# --------------------------------------------------------------------------
class Document:
    def __init__(self, path=None):
        self.path = None
        self.data = bytearray()
        self.mm = None
        self.dirty = False
        self.structural = True
        self.changed = set()
        self.undo, self.redo = [], []
        self.console, self.conf = None, 0
        self.caret, self.anchor, self.nibble, self.pane = 0, None, 0, "hex"
        self.insert_mode = False
        if path:
            self.load(path)

    # ---------------------------------------------------------------- io
    def load(self, path):
        size = os.path.getsize(path)
        if size > MAX_MEM:
            fd = os.open(path, os.O_RDWR)
            self.mm = mmap.mmap(fd, 0, access=mmap.ACCESS_WRITE)
            os.close(fd)
            self.data, self.structural = self.mm, False
        else:
            with open(path, "rb") as fh:
                self.data = bytearray(fh.read())
            self.structural = True
        self.path, self.dirty = path, False
        self.changed.clear()
        self.undo.clear()
        self.redo.clear()
        self.detect()

    def detect(self):
        self.console, self.conf = detect_console(self.data, self.path)

    def save(self, path=None):
        if path:
            self.path = path
        if self.mm:
            self.mm.flush()
        else:
            with open(self.path, "wb") as fh:
                fh.write(self.data)
        self.dirty = False

    @property
    def size(self):
        return len(self.data)

    def name(self):
        return os.path.basename(self.path) if self.path else "Untitled"

    # ------------------------------------------------------------- edits
    def _push(self, entry):
        self.undo.append(entry)
        if len(self.undo) > 8000:
            self.undo.pop(0)
        self.redo.clear()

    def overwrite(self, off, payload, record=True):
        payload = bytes(payload)
        if off + len(payload) > self.size:
            if self.structural:
                self.data.extend(b"\x00" * (off + len(payload) - self.size))
            else:
                payload = payload[:self.size - off]
        if not payload:
            return
        old = bytes(self.data[off:off + len(payload)])
        if record:
            self._push(("ow", off, old, payload))
        self.data[off:off + len(payload)] = payload
        self.changed.update(range(off, off + len(payload)))
        self.dirty = True

    def insert(self, off, payload):
        if not self.structural:
            return False
        payload = bytes(payload)
        self._push(("ins", off, payload))
        self.data[off:off] = payload
        self.changed.update(range(off, off + len(payload)))
        self.dirty = True
        return True

    def delete(self, off, n):
        if not self.structural or n <= 0:
            return False
        n = min(n, self.size - off)
        old = bytes(self.data[off:off + n])
        self._push(("del", off, old))
        del self.data[off:off + n]
        self.changed.update(range(off, min(self.size, off + n)))
        self.dirty = True
        return True

    def undo_step(self):
        if not self.undo:
            return None
        e = self.undo.pop()
        kind = e[0]
        if kind == "ow":
            _, off, old, new = e
            self.data[off:off + len(old)] = old
        elif kind == "ins":
            _, off, payload = e
            del self.data[off:off + len(payload)]
        else:
            _, off, old = e
            self.data[off:off] = old
        self.redo.append(e)
        self.dirty = True
        return e

    def redo_step(self):
        if not self.redo:
            return None
        e = self.redo.pop()
        kind = e[0]
        if kind == "ow":
            _, off, old, new = e
            self.data[off:off + len(new)] = new
        elif kind == "ins":
            _, off, payload = e
            self.data[off:off] = payload
        else:
            _, off, old = e
            del self.data[off:off + len(old)]
        self.undo.append(e)
        self.dirty = True
        return e

    def fill(self, off, n, byte):
        self.overwrite(off, bytes([byte]) * n)

    def byte_at(self, off):
        return self.data[off] if 0 <= off < self.size else 0

    # ------------------------------------------------------------ search
    def find(self, pattern, start, mode, forward=True):
        n = self.size
        if mode == "regex":
            try:
                rx = re.compile(pattern.encode("latin-1"), re.S)
            except re.error:
                return -1
            if forward:
                m = rx.search(bytes(self.data[start:n])) if start < n else None
                return start + m.start() if m else -1
            hits = [m.start() for m in rx.finditer(bytes(self.data[:start]))]
            return hits[-1] if hits else -1
        if mode == "hex":
            rx = parse_hex_pattern(pattern)
            if rx is None:
                return -1
            hay = bytes(self.data)
            if forward:
                m = rx.search(hay, start)
                return m.start() if m else -1
            hits = [m.start() for m in rx.finditer(hay)]
            hits = [h for h in hits if h < start]
            return hits[-1] if hits else -1
        needle = pattern.encode("latin-1", "replace")
        if not needle:
            return -1
        if forward:
            return self.data.find(needle, start)
        idx = bytes(self.data[:start]).rfind(needle)
        return idx

    def find_all(self, pattern, mode, limit=20000):
        out = []
        if mode == "regex":
            try:
                rx = re.compile(pattern.encode("latin-1"), re.S)
            except re.error:
                return out
            for m in rx.finditer(bytes(self.data)):
                out.append((m.start(), len(m.group())))
                if len(out) >= limit:
                    break
            return out
        if mode == "hex":
            rx = parse_hex_pattern(pattern)
            if rx is None:
                return out
            for m in rx.finditer(bytes(self.data)):
                out.append((m.start(), len(m.group())))
                if len(out) >= limit:
                    break
            return out
        needle = pattern.encode("latin-1", "replace")
        if not needle:
            return out
        i = 0
        while len(out) < limit:
            i = self.data.find(needle, i)
            if i < 0:
                break
            out.append((i, len(needle)))
            i += 1
        return out


# --------------------------------------------------------------------------
# hex view
# --------------------------------------------------------------------------
class HexView(tk.Canvas):
    ROW_H = 19
    GAP = 7

    def __init__(self, master, doc: Document, app):
        super().__init__(master, highlightthickness=0, bd=0,
                         yscrollincrement=self.ROW_H)
        self.doc, self.app = doc, app
        self.t = app.t
        self.bpr = 16
        self.fsize = 12
        self.show_ascii = True
        self.show_offsets = True
        self.mono = tkfont.Font(family=app.mono_family, size=self.fsize)
        self._caret_job = None
        self._caret_on = True
        self.sel_drag = False
        self.bind("<Configure>", lambda e: self.redraw())
        self.bind("<Button-1>", self._b1)
        self.bind("<B1-Motion>", self._b1motion)
        self.bind("<ButtonRelease-1>", self._b1up)
        self.bind("<Shift-Button-1>", self._shift_click)
        self.bind("<Button-3>", self._ctx)
        self.bind("<MouseWheel>", self._wheel)
        self.bind("<Button-4>", lambda e: self.yview_scroll(-3, "units"))
        self.bind("<Button-5>", lambda e: self.yview_scroll(3, "units"))
        self.configure(takefocus=True)

    # ---------------------------------------------------------- geometry
    def metrics(self):
        cw = self.mono.measure("0")
        self.cw = cw
        self.cell = 2 * cw + self.GAP
        self.gutter = (9 * cw + 14) if self.show_offsets else 4
        self.hex_x = self.gutter + 6
        self.ascii_x = self.hex_x + self.bpr * self.cell + 16
        self.total_w = self.ascii_x + (self.bpr * cw if self.show_ascii else 0) + 16
        self.rows = max(1, (self.doc.size + self.bpr - 1) // self.bpr)
        self.total_h = self.rows * self.ROW_H
        self.configure(scrollregion=(0, 0, self.total_w, self.total_h))
        self.visible = max(1, self.winfo_height() // self.ROW_H + 2)

    def pos_to_offset(self, x, y):
        self.metrics()
        top = self.yview()[0] * self.total_h
        row = int((y + top) // self.ROW_H)
        if row < 0:
            row = 0
        if x < self.hex_x and x >= self.gutter:
            return min(row * self.bpr, max(0, self.doc.size - 1)), "hex", 0
        if x >= self.ascii_x and self.show_ascii:
            col = int((x - self.ascii_x) // self.cw)
            return min(row * self.bpr + max(0, min(col, self.bpr - 1)), max(0, self.doc.size - 1)), "ascii", 0
        col = int((x - self.hex_x) // self.cell)
        col = max(0, min(col, self.bpr - 1))
        within = (x - self.hex_x) - col * self.cell
        nib = 0 if within < self.cw else 1
        off = min(row * self.bpr + col, max(0, self.doc.size - 1))
        return off, "hex", nib

    def offset_to_xy(self, off):
        self.metrics()
        row, col = divmod(off, self.bpr)
        if self.doc.pane == "ascii" and self.show_ascii:
            x = self.ascii_x + col * self.cw
        else:
            x = self.hex_x + col * self.cell + self.doc.nibble * self.cw
        return x, row * self.ROW_H

    # ------------------------------------------------------------ drawing
    def redraw(self):
        self.metrics()
        self.delete("all")
        t = self.t
        top_row = int(self.yview()[0] * self.total_h // self.ROW_H)
        end_row = min(self.rows, top_row + self.visible)
        bpr, doc = self.bpr, self.doc
        sel = self.selection()

        for row in range(top_row, end_row):
            y = row * self.ROW_H
            base = row * bpr
            if base >= doc.size:
                break
            # row highlight
            if row % 2 == 0:
                self.create_rectangle(0, y, self.total_w, y + self.ROW_H,
                                      fill=t["hi"], width=0)
            if self.show_offsets:
                self.create_text(self.gutter - 8, y + self.ROW_H // 2,
                                 text="%08X" % base, anchor="e", fill=t["dim"],
                                 font=self.mono)
            self.create_line(self.gutter - 2, y, self.gutter - 2, y + self.ROW_H,
                             fill=t["border"])

            # selection bands — Hex Fiend highlights BOTH hex and ascii columns
            if sel:
                s0, s1 = sel
                if s0 < base + bpr and s1 > base:
                    a = max(s0, base) - base
                    b = min(s1, base + bpr) - base
                    self.create_rectangle(self.hex_x + a * self.cell - self.GAP / 2, y,
                                          self.hex_x + b * self.cell - self.GAP / 2, y + self.ROW_H,
                                          fill=t["sel"], width=0)
                    if self.show_ascii:
                        self.create_rectangle(self.ascii_x + a * self.cw, y,
                                              self.ascii_x + b * self.cw, y + self.ROW_H,
                                              fill=t["sel"], width=0)

            # ascii column (per-byte colors so selection reads like Hex Fiend)
            if self.show_ascii:
                for col in range(bpr):
                    off = base + col
                    if off >= doc.size:
                        break
                    ch = printable(doc.data[off])
                    fg = t["sel_fg"] if (sel and sel[0] <= off < sel[1]) else t["fg"]
                    self.create_text(self.ascii_x + col * self.cw, y + self.ROW_H // 2,
                                     text=ch, anchor="w", fill=fg, font=self.mono)

            # hex column
            for col in range(bpr):
                off = base + col
                if off >= doc.size:
                    break
                x = self.hex_x + col * self.cell
                v = doc.data[off]
                fg = t["fg"]
                if off in doc.changed:
                    self.create_rectangle(x - 1, y, x + 2 * self.cw + 1, y + self.ROW_H,
                                          fill=t["changed"], width=0)
                    fg = t["changed_fg"]
                if sel and sel[0] <= off < sel[1]:
                    fg = t["sel_fg"]
                self.create_text(x, y + self.ROW_H // 2, text="%02X" % v,
                                 anchor="w", fill=fg, font=self.mono)
                if off == doc.caret and self._caret_on and doc.pane == "hex":
                    cx = x + doc.nibble * self.cw
                    self.create_rectangle(cx, y + 2, cx + self.cw, y + self.ROW_H - 2,
                                          outline=t["caret"], width=1)

            if doc.caret // bpr == row and self._caret_on and doc.pane == "ascii" and self.show_ascii:
                cx = self.ascii_x + (doc.caret % bpr) * self.cw
                self.create_rectangle(cx, y + 2, cx + self.cw, y + self.ROW_H - 2,
                                      outline=t["caret"], width=1)
        self.app.update_status()

    def selection(self):
        a, b = self.doc.anchor, self.doc.caret
        if a is None:
            return None
        return (min(a, b), max(a, b) + 1)

    def blink(self):
        self._caret_on = not self._caret_on
        self.redraw()
        self._caret_job = self.after(560, self.blink)

    def ensure_visible(self, off):
        self.metrics()
        row = off // self.bpr
        top = self.yview()[0] * self.total_h
        y = row * self.ROW_H
        if y < top:
            self.yview_moveto(max(0, y - self.ROW_H) / self.total_h)
        elif y + self.ROW_H > top + self.winfo_height():
            self.yview_moveto(max(0, y - self.winfo_height() + 2 * self.ROW_H) / self.total_h)

    # ------------------------------------------------------------- input
    def _b1(self, ev):
        self.focus_set()
        off, pane, nib = self.pos_to_offset(ev.x, ev.y)
        self.doc.pane, self.doc.nibble = pane, nib
        self.doc.caret = off
        self.doc.anchor = None  # no selection until drag / Shift
        self._drag_origin = off
        self.sel_drag = True
        self.redraw()

    def _shift_click(self, ev):
        off, pane, nib = self.pos_to_offset(ev.x, ev.y)
        self.doc.pane, self.doc.nibble = pane, nib
        if self.doc.anchor is None:
            self.doc.anchor = self.doc.caret
        self.doc.caret = off
        self.redraw()

    def _b1motion(self, ev):
        if not self.sel_drag:
            return
        off, pane, nib = self.pos_to_offset(ev.x, ev.y)
        if self.doc.anchor is None:
            self.doc.anchor = getattr(self, "_drag_origin", self.doc.caret)
        self.doc.caret, self.doc.pane, self.doc.nibble = off, pane, nib
        self.redraw()

    def _b1up(self, ev):
        self.sel_drag = False

    def _wheel(self, ev):
        self.yview_scroll(-3 if ev.delta > 0 else 3, "units")
        self.redraw()

    def _ctx(self, ev):
        self.app.context_menu(ev)

    def set_caret(self, off, keep_anchor=False):
        self.doc.caret = max(0, min(off, max(0, self.doc.size - 1)))
        if not keep_anchor:
            self.doc.anchor = None
        self.ensure_visible(self.doc.caret)
        self.redraw()


# --------------------------------------------------------------------------
# side panels
# --------------------------------------------------------------------------
class Inspector(tk.Frame):
    ROWS = [("u8", 1), ("s8", 1), ("u16", 2), ("s16", 2), ("u32", 4),
            ("s32", 4), ("u64", 8), ("f32", 4), ("f64", 8)]

    def __init__(self, master, app):
        super().__init__(master, bg=app.t["panel"])
        self.app = app
        self.body = tk.Text(self, height=16, width=30, bd=0, relief="flat",
                            bg=app.t["field"], fg=app.t["fg"],
                            font=(app.mono_family, 10), highlightthickness=0)
        self.body.pack(fill="both", expand=True, padx=6, pady=6)
        self.body.configure(state="disabled")

    def refresh(self, doc: Document):
        off = doc.caret
        data = doc.data
        out = ["offset  0x%08X  (%d)" % (off, off), ""]
        out.append("byte    %02X  '%s'   bits %s" %
                   (doc.byte_at(off), printable(doc.byte_at(off)),
                    format(doc.byte_at(off), "08b")))
        out.append("")
        for label, n in self.ROWS:
            if off + n > doc.size:
                continue
            raw = bytes(data[off:off + n])
            for endian in ("le", "be"):
                fmt = ("<" if endian == "le" else ">") + {"u8": "B", "s8": "b", "u16": "H",
                                                          "s16": "h", "u32": "I", "s32": "i",
                                                          "u64": "Q", "f32": "f", "f64": "d"}[label]
                try:
                    v = struct.unpack(fmt, raw)[0]
                except struct.error:
                    continue
                if label.startswith("f"):
                    txt = "%g" % v
                elif label.startswith("s"):
                    txt = str(v)
                else:
                    txt = "0x%X" % v
                out.append("%-7s %-2s %s" % (label, endian, txt))
            out.append("")
        fld = self.app.field_under(off)
        if fld:
            out.append("--- console field ---")
            out.append(fld)
        self.body.configure(state="normal")
        self.body.delete("1.0", "end")
        self.body.insert("1.0", "\n".join(out))
        self.body.configure(state="disabled")


class ConsolePanel(tk.Frame):
    def __init__(self, master, app):
        super().__init__(master, bg=app.t["panel"])
        self.app = app
        self.head = tk.Label(self, text="no console detected", anchor="w",
                             bg=app.t["panel"], fg=app.t["fg"],
                             font=("TkDefaultFont", 11, "bold"))
        self.head.pack(fill="x", padx=8, pady=(8, 2))
        self.sub = tk.Label(self, text="", anchor="w", justify="left",
                            bg=app.t["panel"], fg=app.t["dim"], font=("TkDefaultFont", 9))
        self.sub.pack(fill="x", padx=8)
        self.tree = ttk.Treeview(self, columns=("field", "value"), show="headings",
                                 height=14)
        self.tree.heading("field", text="field")
        self.tree.heading("value", text="value")
        self.tree.column("field", width=150, stretch=False)
        self.tree.column("value", width=190)
        self.tree.pack(fill="both", expand=True, padx=6, pady=6)
        self.tree.bind("<Double-1>", self._jump)
        btns = tk.Frame(self, bg=app.t["panel"])
        btns.pack(fill="x", padx=6, pady=(0, 8))
        tk.Button(btns, text="Verify checksums", command=self.verify,
                  bg=app.t["chrome"], fg=app.t["fg"], bd=0, padx=8, pady=3,
                  activebackground=app.t["sel"]).pack(side="left")
        tk.Button(btns, text="Re-analyze", command=self.reload,
                  bg=app.t["chrome"], fg=app.t["fg"], bd=0, padx=8, pady=3,
                  activebackground=app.t["sel"]).pack(side="left", padx=4)

    def _doc(self):
        return self.app.current_doc()

    def reload(self):
        d = self._doc()
        if d:
            d.detect()
            self.refresh(d)
            self.app.update_status()

    def refresh(self, doc: Document):
        self.tree.delete(*self.tree.get_children())
        c = doc.console
        if not c:
            self.head.configure(text="unrecognised image", fg=self.app.t["dim"])
            self.sub.configure(text="%d bytes\nUse Console > Analyze as to force a type."
                                    % doc.size)
            return
        self.head.configure(text=c.name, fg=self.app.t["fg"])
        self.sub.configure(text="%s family  |  confidence %d%%\n%s"
                                % (c.family, doc.conf, c.note or ""))
        for f in c.fields:
            off, length, label, kind, extra = f
            o = off if off >= 0 else doc.size + off
            if o < 0 or o >= doc.size:
                continue
            if kind == "flags" and extra:
                raw = doc.byte_at(o)
                val = ", ".join(l for b, l in extra if raw & (1 << b)) or ("0x%02X" % raw)
            else:
                val = field_value(doc.data, off, length, kind)
            self.tree.insert("", "end", values=(label, val), tags=(str(o),))

    def _jump(self, ev):
        sel = self.tree.selection()
        if not sel:
            return
        off = int(self.tree.item(sel[0], "tags")[0])
        self.app.view().set_caret(off)

    def verify(self):
        d = self._doc()
        if not d or not d.console or not d.console.verify:
            messagebox.showinfo("Checksums", "No verifier for this console.")
            return
        rows = d.console.verify(d.data)
        if not rows:
            messagebox.showinfo("Checksums", "Nothing to verify.")
            return
        lines = []
        for label, exp, act, ok in rows:
            lines.append("%-26s expected %s  actual %s   %s" %
                         (label,
                          ("0x%X" % exp) if isinstance(exp, int) and exp else "-",
                          ("0x%X" % act) if isinstance(act, int) else "-",
                          "OK" if ok else "MISMATCH"))
        win = tk.Toplevel(self)
        win.title("Checksums - %s" % d.console.name)
        win.configure(bg=self.app.t["panel"])
        txt = tk.Text(win, width=64, height=len(lines) + 2, bd=0,
                      bg=self.app.t["field"], fg=self.app.t["fg"],
                      font=(self.app.mono_family, 10))
        txt.pack(padx=10, pady=10)
        txt.insert("1.0", "\n".join(lines))
        txt.configure(state="disabled")


# --------------------------------------------------------------------------
# editor frame
# --------------------------------------------------------------------------
class Editor(tk.Frame):
    def __init__(self, master, app, doc: Document):
        super().__init__(master, bg=app.t["chrome"])
        self.app, self.doc = app, doc
        self._search_start = 0

        self.ruler = tk.Canvas(self, height=20, bg=app.t["ruler"],
                               highlightthickness=0)
        self.ruler.pack(fill="x", side="top")

        mid = tk.Frame(self, bg=app.t["chrome"])
        mid.pack(fill="both", expand=True)
        self.view = HexView(mid, doc, app)
        self.view.pack(side="left", fill="both", expand=True)
        self.vbar = ttk.Scrollbar(mid, orient="vertical", command=self._scroll)
        self.vbar.pack(side="right", fill="y")
        self.view.configure(yscrollcommand=self.vbar.set)

        self.panes = ttk.Notebook(self, width=360)
        self.inspector = Inspector(self.panes, app)
        self.console = ConsolePanel(self.panes, app)
        self.bookmarks = self._bookmarks_panel()
        self.panes.add(self.inspector, text="Inspector")
        self.panes.add(self.console, text="Console")
        self.panes.add(self.bookmarks[0], text="Bookmarks")
        self.panes.pack(side="right", fill="y")

        self.bind("<Configure>", lambda e: self.draw_ruler())
        self.view.bind("<Key>", self.on_key, add="+")
        self._bind_edit_keys()
        self.view.bind("<Insert>", lambda e: (self.toggle_insert(), "break")[1])
        self.view.bind("<MouseWheel>", lambda e: self.after(1, self.draw_ruler), add="+")
        self.console.refresh(doc)
        self.bookmark_list = []
        # Hex Fiend-style blinking caret
        self.view.after(200, self.view.blink)
        self.after(50, lambda: (self.view.focus_set(), self.view.redraw(), self.draw_ruler()))

    def _bind_edit_keys(self):
        """Hex Fiend-style shortcuts: Control-* and Command-* (macOS)."""
        def bind_both(key, fn, shift=False):
            for mod in ("Control", "Command"):
                seq = f"<{mod}-Shift-{key}>" if shift else f"<{mod}-{key}>"
                self.view.bind(seq, lambda e, f=fn: (f(), "break")[1])
                # Also on the Editor frame so focus anywhere in the tab still works.
                self.bind(seq, lambda e, f=fn: (f(), "break")[1])

        bind_both("a", self.select_all)
        bind_both("c", self.copy)
        bind_both("x", self.cut)
        bind_both("v", self.paste)
        bind_both("z", self.undo)
        bind_both("y", self.redo)
        bind_both("z", self.redo, shift=True)  # Cmd/Ctrl+Shift+Z redo
        bind_both("s", self.app.save)
        bind_both("f", self.app.show_find)
        bind_both("g", self.app.goto)
        bind_both("d", self.add_bookmark)
        # Hex Fiend: Copy Entire File
        bind_both("c", self.copy_entire_file, shift=True)

    def _bookmarks_panel(self):
        f = tk.Frame(self.panes, bg=self.app.t["panel"])
        self.bm_tree = ttk.Treeview(f, columns=("off", "note"), show="headings", height=14)
        self.bm_tree.heading("off", text="offset")
        self.bm_tree.heading("note", text="note")
        self.bm_tree.column("off", width=90, stretch=False)
        self.bm_tree.column("note", width=230)
        self.bm_tree.pack(fill="both", expand=True, padx=6, pady=6)
        self.bm_tree.bind("<Double-1>", lambda e: self.goto_bookmark())
        return (f,)

    def _scroll(self, *a):
        self.view.yview(*a)
        self.view.redraw()
        self.draw_ruler()

    def draw_ruler(self):
        self.view.metrics()
        c = self.ruler
        c.delete("all")
        c.configure(bg=self.app.t["ruler"])
        cw, cell = self.view.cw, self.view.cell
        x0 = self.view.hex_x - 12
        c.create_text(max(2, x0 - 8), 10, text="offset", anchor="e",
                      fill=self.app.t["dim"], font=(self.app.mono_family, 8))
        for i in range(self.view.bpr):
            c.create_text(self.view.hex_x + i * cell + cw, 10,
                          text="%02X" % i, anchor="center",
                          fill=self.app.t["dim"], font=(self.app.mono_family, 9))
        if self.view.show_ascii:
            c.create_text(self.view.ascii_x, 10, text="ascii", anchor="w",
                          fill=self.app.t["dim"], font=(self.app.mono_family, 8))
        c.create_line(0, 19, max(200, self.view.total_w), 19, fill=self.app.t["border"])

    # -------------------------------------------------------------- edits
    def toggle_insert(self):
        self.doc.insert_mode = not self.doc.insert_mode
        self.app.update_status()

    def select_all(self):
        if self.doc.size <= 0:
            self.doc.anchor, self.doc.caret = None, 0
        else:
            self.doc.anchor, self.doc.caret = 0, self.doc.size - 1
        self.view.redraw()

    def _sel_range(self):
        """Byte range for clipboard ops: selection, or the single caret byte."""
        s = self.view.selection()
        if s and s[1] > s[0]:
            return s
        if self.doc.size <= 0:
            return None
        c = min(self.doc.caret, self.doc.size - 1)
        return (c, c + 1)

    def _put_clipboard(self, text):
        self.clipboard_clear()
        self.clipboard_append(text)
        try:
            # Make the clipboard survive after quit on macOS/X11.
            self.update_idletasks()
        except tk.TclError:
            pass

    def copy(self):
        """Pane-aware copy (Hex Fiend): hex pane → spaced hex, ASCII pane → text."""
        s = self._sel_range()
        if not s:
            self.app.status("nothing to copy")
            return
        self._copy_range(s[0], s[1], as_ascii=(self.doc.pane == "ascii"))

    def copy_entire_file(self):
        """Select the whole buffer and copy it (Hex Fiend Select All + Copy)."""
        if self.doc.size <= 0:
            self.app.status("file is empty")
            return
        # Cap clipboard blow-ups for huge images (hex expands ~3x).
        if self.doc.size > 16 * 1024 * 1024:
            if not messagebox.askyesno(
                    APP,
                    "This file is %s. Copying the entire file to the clipboard "
                    "may use a lot of memory. Continue?" % human(self.doc.size),
                    parent=self):
                return
        self.select_all()
        self._copy_range(0, self.doc.size, as_ascii=(self.doc.pane == "ascii"))

    def _copy_range(self, start, end, as_ascii=False):
        chunk = bytes(self.doc.data[start:end])
        if as_ascii:
            self._put_clipboard(bytes_to_ascii_clipboard(chunk))
            self.app.status("copied %d bytes as text (0x%X–0x%X)" % (
                len(chunk), start, max(start, end - 1)))
        else:
            self._put_clipboard(bytes_to_hex_clipboard(chunk, spaced=True))
            self.app.status("copied %d bytes as hex (0x%X–0x%X)" % (
                len(chunk), start, max(start, end - 1)))

    def copy_hex(self):
        s = self._sel_range()
        if not s:
            return
        self._copy_range(s[0], s[1], as_ascii=False)

    def copy_hex_compact(self):
        s = self._sel_range()
        if not s:
            return
        chunk = bytes(self.doc.data[s[0]:s[1]])
        self._put_clipboard(bytes_to_hex_clipboard(chunk, spaced=False))
        self.app.status("copied %d bytes as compact hex" % len(chunk))

    def copy_ascii(self):
        s = self._sel_range()
        if not s:
            return
        self._copy_range(s[0], s[1], as_ascii=True)

    def cut(self):
        self.copy()
        s = self.view.selection()
        if s and s[1] > s[0] and self.doc.delete(s[0], s[1] - s[0]):
            self.doc.caret = s[0]
            self.doc.anchor = None
            self.doc.nibble = 0
            self.refresh()

    def paste(self):
        """Paste hex dump or raw text; replaces the current selection (Hex Fiend)."""
        try:
            txt = self.clipboard_get()
        except tk.TclError:
            self.app.status("clipboard empty")
            return
        payload = clipboard_to_bytes(txt)
        if not payload:
            self.app.status("clipboard empty")
            return
        self._replace_selection_with(payload)

    def paste_as_ascii(self):
        try:
            txt = self.clipboard_get()
        except tk.TclError:
            return
        self._replace_selection_with(txt.encode("latin-1", "replace"))

    def paste_as_hex(self):
        try:
            txt = self.clipboard_get()
        except tk.TclError:
            return
        cleaned = re.sub(r"(?i)0x", "", txt)
        cleaned = re.sub(r"[\s,;:_|\-]", "", cleaned)
        try:
            payload = bytes.fromhex(cleaned)
        except ValueError:
            self.app.status("clipboard is not valid hex")
            return
        if not payload:
            return
        self._replace_selection_with(payload)

    def _replace_selection_with(self, payload):
        """Replace selection (or insert/overwrite at caret) — Hex Fiend paste."""
        self.insert_bytes(payload)

    def insert_bytes(self, payload):
        payload = bytes(payload)
        if not payload:
            return
        d = self.doc
        s = self.view.selection()
        if s and s[1] > s[0]:
            start, length = s[0], s[1] - s[0]
            if d.structural:
                d.delete(start, length)
                d.insert(start, payload)
                d.caret = start + len(payload)
            else:
                # mmap: overwrite min(len) bytes of the selection
                d.overwrite(start, payload[:length])
                d.caret = start + min(length, len(payload))
            d.anchor = None
        elif d.insert_mode and d.structural:
            d.insert(d.caret, payload)
            d.caret += len(payload)
        else:
            d.overwrite(d.caret, payload)
            d.caret += len(payload)
            if d.caret >= d.size:
                d.caret = max(0, d.size - 1)
        d.nibble = 0
        self.refresh()
        self.app.status("wrote %d bytes" % len(payload))

    def _consume_selection_for_type(self):
        """If there is a selection, delete it and place caret at its start (Hex Fiend)."""
        d = self.doc
        s = self.view.selection()
        if not s or s[1] <= s[0]:
            return False
        if d.structural:
            d.delete(s[0], s[1] - s[0])
        else:
            # mmap / non-structural: zero-fill then type over
            d.overwrite(s[0], b"\x00" * (s[1] - s[0]))
        d.caret = s[0]
        d.anchor = None
        d.nibble = 0
        return True

    def on_key(self, ev):
        # Skip chars that belong to Cmd/Ctrl shortcuts (bindings already fired).
        if (ev.state & 0x4) or (ev.state & 0x100000) or (ev.state & 0x8):
            if ev.keysym.lower() in (
                "a", "c", "x", "v", "z", "y", "s", "f", "g", "d", "o", "n", "w",
            ):
                return "break"

        d = self.doc
        k = ev.keysym
        step = self.view.bpr
        shift = bool(ev.state & 0x1)
        nav = k in ("Left", "Right", "Up", "Down", "Prior", "Next", "Home", "End")
        prev_caret = d.caret

        if nav:
            if k == "Left":
                if d.pane == "hex" and d.nibble == 1:
                    d.nibble = 0
                else:
                    d.caret = max(0, d.caret - 1)
                    d.nibble = 1 if d.pane == "hex" else 0
            elif k == "Right":
                if d.pane == "hex" and d.nibble == 0 and d.size > 0:
                    d.nibble = 1
                else:
                    d.nibble = 0
                    d.caret = d.caret + 1
                    if d.size:
                        d.caret = min(d.caret, d.size - (0 if d.insert_mode else 1))
                        d.caret = max(0, d.caret)
            elif k == "Up":
                d.caret = max(0, d.caret - step)
            elif k == "Down":
                d.caret = min(max(0, d.size - 1), d.caret + step)
            elif k == "Prior":
                d.caret = max(0, d.caret - step * self.view.visible)
            elif k == "Next":
                d.caret = min(max(0, d.size - 1), d.caret + step * self.view.visible)
            elif k == "Home":
                d.caret = (d.caret // step) * step
                d.nibble = 0
            elif k == "End":
                d.caret = min(max(0, d.size - 1), (d.caret // step) * step + step - 1)
                d.nibble = 0
            # Shift+arrows extend selection (Hex Fiend)
            if shift:
                if d.anchor is None:
                    d.anchor = prev_caret
            else:
                d.anchor = None
        elif k == "BackSpace":
            s = self.view.selection()
            if s and s[1] > s[0]:
                if d.delete(s[0], s[1] - s[0]):
                    d.caret = s[0]
            elif d.pane == "hex" and d.nibble == 1:
                d.nibble = 0
            elif d.caret > 0:
                if d.delete(d.caret - 1, 1):
                    d.caret -= 1
                    d.nibble = 0
            d.anchor = None
        elif k == "Delete":
            s = self.view.selection()
            if s and s[1] > s[0]:
                d.delete(s[0], s[1] - s[0])
                d.caret = s[0]
            else:
                d.delete(d.caret, 1)
            d.nibble = 0
            d.anchor = None
        elif k == "Escape":
            d.anchor = None
        elif k == "Tab":
            d.pane = "ascii" if d.pane == "hex" else "hex"
            d.nibble = 0
            d.anchor = None
        else:
            ch = ev.char
            if len(ch) == 1 and ch in "0123456789abcdefABCDEF" and d.pane == "hex":
                self._consume_selection_for_type()
                if d.caret >= d.size:
                    if d.structural:
                        d.insert(d.size, b"\x00")
                    else:
                        return
                v = int(ch, 16)
                cur = d.byte_at(d.caret)
                nv = ((cur & 0x0F) | (v << 4)) if d.nibble == 0 else ((cur & 0xF0) | v)
                d.overwrite(d.caret, bytes([nv]))
                if d.nibble == 0:
                    d.nibble = 1
                else:
                    d.nibble = 0
                    d.caret += 1
                    if d.caret >= d.size and not d.insert_mode:
                        d.caret = max(0, d.size - 1)
                d.anchor = None
            elif len(ch) == 1 and 32 <= ord(ch) < 127 and d.pane == "ascii":
                self._consume_selection_for_type()
                if d.insert_mode and d.structural:
                    d.insert(d.caret, ch.encode("latin-1"))
                elif d.caret >= d.size:
                    if d.structural:
                        d.insert(d.size, ch.encode("latin-1"))
                    else:
                        return
                else:
                    d.overwrite(d.caret, ch.encode("latin-1"))
                d.caret += 1
                if not d.insert_mode and d.caret >= d.size:
                    d.caret = max(0, d.size - 1)
                d.anchor = None
            else:
                return

        vis = min(d.caret, max(0, d.size - 1)) if d.size else 0
        self.view.ensure_visible(vis)
        self.refresh()
        return "break"

    def undo(self):
        if self.doc.undo_step():
            self.doc.caret = min(self.doc.caret, max(0, self.doc.size - 1))
            self.refresh()

    def redo(self):
        if self.doc.redo_step():
            self.refresh()

    def add_bookmark(self):
        note = simpledialog.askstring("Bookmark", "Note:", parent=self,
                                      initialvalue="0x%08X" % self.doc.caret)
        if note is None:
            return
        self.bookmark_list.append((self.doc.caret, note))
        self.bm_tree.insert("", "end", values=("0x%08X" % self.doc.caret, note),
                            tags=(str(self.doc.caret),))

    def goto_bookmark(self):
        sel = self.bm_tree.selection()
        if sel:
            self.view.set_caret(int(self.bm_tree.item(sel[0], "tags")[0]))

    def refresh(self):
        self.view.redraw()
        self.inspector.refresh(self.doc)
        self.app.update_status()

    def search(self, pattern, mode, forward, wrap):
        if not pattern:
            return False
        d = self.doc
        start = d.caret + (1 if forward else 0)
        hit = d.find(pattern, start, mode, forward)
        if hit < 0 and wrap:
            hit = d.find(pattern, 0 if forward else d.size, mode, forward)
        if hit < 0:
            self.app.status("not found")
            return False
        d.anchor = hit
        d.caret = hit + max(0, len(pattern.replace(" ", "")) // 2 - 1 if mode == "hex" else len(pattern) - 1)
        d.caret = min(d.caret, max(0, d.size - 1))
        self.view.set_caret(hit)
        d.anchor = hit
        self.view.redraw()
        return True

    def replace_one(self, pattern, mode, repl):
        s = self.view.selection()
        if s:
            payload = bytes.fromhex(re.sub(r"[\s,_]", "", repl)) if mode == "hex" else repl.encode()
            self.doc.overwrite(s[0], payload)
            self.refresh()


# --------------------------------------------------------------------------
# application
# --------------------------------------------------------------------------
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.t = dict(LIGHT)
        fam = tkfont.families()
        self.mono_family = next((f for f in MONO if f in fam), "Courier")
        self.title("%s  -  %s" % (APP, BUILD))
        self.geometry("1180x740")
        self.minsize(820, 480)
        self.configure(bg=self.t["chrome"])
        self._status_msg = "ready"
        self.build_menu()
        self.build_toolbar()
        self.build_findbar()
        self.build_status()
        self.tabs = ttk.Notebook(self)
        self.tabs.pack(fill="both", expand=True)
        self.tabs.bind("<<NotebookTabChanged>>", lambda e: self.update_status())
        self.bind("<Control-o>", lambda e: self.open_dialog())
        self.bind("<Control-n>", lambda e: self.new_file())
        self.bind("<Control-w>", lambda e: self.close_tab())
        self.bind("<F3>", lambda e: self.find_next(True))
        self.bind("<Shift-F3>", lambda e: self.find_next(False))
        self.protocol("WM_DELETE_WINDOW", self.quit_app)

    # --------------------------------------------------------------- chrome
    def build_menu(self):
        m = tk.Menu(self)
        f = tk.Menu(m, tearoff=0)
        f.add_command(label="New", command=self.new_file, accelerator="Ctrl+N")
        f.add_command(label="Open...", command=self.open_dialog, accelerator="Ctrl+O")
        f.add_command(label="Save", command=self.save, accelerator="Ctrl+S")
        f.add_command(label="Save As...", command=self.save_as)
        f.add_separator()
        f.add_command(label="Close Tab", command=self.close_tab, accelerator="Ctrl+W")
        f.add_command(label="Quit", command=self.quit_app)
        m.add_cascade(label="File", menu=f)

        e = tk.Menu(m, tearoff=0)
        e.add_command(label="Undo", command=lambda: self._v("undo"), accelerator="Ctrl+Z")
        e.add_command(label="Redo", command=lambda: self._v("redo"), accelerator="Ctrl+Y")
        e.add_separator()
        e.add_command(label="Cut", command=lambda: self._v("cut"), accelerator="Ctrl+X")
        e.add_command(label="Copy", command=lambda: self._v("copy"), accelerator="Ctrl+C")
        e.add_command(label="Copy Hexadecimal", command=lambda: self._v("copy_hex"))
        e.add_command(label="Copy ASCII", command=lambda: self._v("copy_ascii"))
        e.add_command(label="Copy Entire File", command=lambda: self._v("copy_entire_file"),
                      accelerator="Ctrl+Shift+C")
        e.add_command(label="Paste", command=lambda: self._v("paste"), accelerator="Ctrl+V")
        e.add_command(label="Paste as Hex", command=lambda: self._v("paste_as_hex"))
        e.add_command(label="Paste as ASCII", command=lambda: self._v("paste_as_ascii"))
        e.add_command(label="Select All", command=lambda: self._v("select_all"), accelerator="Ctrl+A")
        e.add_separator()
        e.add_command(label="Insert / Overwrite mode", command=lambda: self._v("toggle_insert"),
                      accelerator="Insert")
        e.add_command(label="Fill selection...", command=self.fill_selection)
        e.add_command(label="Insert bytes...", command=self.insert_dialog)
        e.add_command(label="Delete selection", command=lambda: self._v("del_sel"))
        m.add_cascade(label="Edit", menu=e)

        s = tk.Menu(m, tearoff=0)
        s.add_command(label="Find...", command=self.show_find, accelerator="Ctrl+F")
        s.add_command(label="Find Next", command=lambda: self.find_next(True), accelerator="F3")
        s.add_command(label="Find Previous", command=lambda: self.find_next(False), accelerator="Shift+F3")
        s.add_command(label="Goto offset...", command=self.goto, accelerator="Ctrl+G")
        s.add_separator()
        s.add_command(label="Count occurrences", command=self.count_all)
        m.add_cascade(label="Search", menu=s)

        v = tk.Menu(m, tearoff=0)
        v.add_command(label="Bytes per row 8", command=lambda: self.set_bpr(8))
        v.add_command(label="Bytes per row 16", command=lambda: self.set_bpr(16))
        v.add_command(label="Bytes per row 32", command=lambda: self.set_bpr(32))
        v.add_separator()
        v.add_command(label="Font +", command=lambda: self.set_font(1))
        v.add_command(label="Font -", command=lambda: self.set_font(-1))
        v.add_separator()
        v.add_command(label="Toggle ASCII column", command=self.toggle_ascii)
        v.add_command(label="Toggle offset gutter", command=self.toggle_offsets)
        v.add_command(label="Dark mode", command=self.toggle_dark)
        m.add_cascade(label="View", menu=v)

        c = tk.Menu(m, tearoff=0)
        c.add_command(label="Re-analyze image", command=lambda: self._panel("reload"))
        c.add_command(label="Verify checksums", command=lambda: self._panel("verify"))
        for fam in FAMILIES:
            sub = tk.Menu(c, tearoff=0)
            for cons in CONSOLES:
                if cons.family == fam:
                    sub.add_command(label=cons.name,
                                    command=lambda k=cons: self.force_console(k))
            c.add_cascade(label=fam, menu=sub)
        m.add_cascade(label="Console", menu=c)

        t = tk.Menu(m, tearoff=0)
        t.add_command(label="Checksum / hash the selection", command=self.hash_selection)
        t.add_command(label="XOR selection with key...", command=self.xor_selection)
        t.add_command(label="Add bookmark", command=lambda: self._v("add_bookmark"), accelerator="Ctrl+D")
        m.add_cascade(label="Tools", menu=t)

        h = tk.Menu(m, tearoff=0)
        h.add_command(label="Console database (%d systems)" % len(CONSOLES),
                      command=self.show_db)
        h.add_command(label="About %s" % APP, command=self.about)
        m.add_cascade(label="Help", menu=h)
        self.config(menu=m)

    def build_toolbar(self):
        bar = tk.Frame(self, bg=self.t["chrome"], height=34)
        bar.pack(fill="x")
        def b(text, cmd):
            tk.Button(bar, text=text, command=cmd, bd=0, relief="flat",
                      bg=self.t["chrome"], fg=self.t["fg"], padx=9, pady=4,
                      activebackground=self.t["sel"],
                      font=("TkDefaultFont", 10)).pack(side="left", padx=1, pady=4)
        for text, cmd in (("Open", self.open_dialog), ("Save", self.save),
                          ("|", None), ("Copy ROM", lambda: self._v("copy_entire_file")),
                          ("|", None), ("Undo", lambda: self._v("undo")),
                          ("Redo", lambda: self._v("redo")), ("|", None),
                          ("Find", self.show_find), ("Goto", self.goto),
                          ("|", None), ("Insert mode", lambda: self._v("toggle_insert")),
                          ("Console", lambda: self._panel("reload")),
                          ("Checksums", lambda: self._panel("verify"))):
            if text == "|":
                tk.Frame(bar, width=1, bg=self.t["border"]).pack(side="left", fill="y",
                                                                 padx=5, pady=7)
            else:
                b(text, cmd)
        self.mode_lbl = tk.Label(bar, text="OVR", bg=self.t["chrome"],
                                 fg=self.t["dim"], font=(self.mono_family, 9))
        self.mode_lbl.pack(side="right", padx=10)

    def build_findbar(self):
        self.findbar = tk.Frame(self, bg=self.t["panel"])
        self.find_mode = tk.StringVar(value="hex")
        tk.Label(self.findbar, text="Find", bg=self.t["panel"], fg=self.t["fg"]).pack(side="left", padx=(8, 4))
        self.find_entry = tk.Entry(self.findbar, width=34, font=(self.mono_family, 11),
                                   bg=self.t["field"], fg=self.t["fg"], bd=0,
                                   insertbackground=self.t["caret"])
        self.find_entry.pack(side="left", padx=4, pady=5)
        self.find_entry.bind("<Return>", lambda e: self.find_next(True))
        self.find_entry.bind("<Escape>", lambda e: self.hide_find())
        for label, val in (("hex", "hex"), ("ascii", "ascii"), ("regex", "regex")):
            tk.Radiobutton(self.findbar, text=label, value=val, variable=self.find_mode,
                           bg=self.t["panel"], fg=self.t["fg"],
                           selectcolor=self.t["field"], activebackground=self.t["panel"],
                           bd=0).pack(side="left")
        tk.Label(self.findbar, text="Replace", bg=self.t["panel"], fg=self.t["fg"]).pack(side="left", padx=(10, 4))
        self.repl_entry = tk.Entry(self.findbar, width=24, font=(self.mono_family, 11),
                                   bg=self.t["field"], fg=self.t["fg"], bd=0)
        self.repl_entry.pack(side="left", padx=4)
        tk.Button(self.findbar, text="Next", command=lambda: self.find_next(True),
                  bg=self.t["chrome"], fg=self.t["fg"], bd=0, padx=8).pack(side="left", padx=2)
        tk.Button(self.findbar, text="Prev", command=lambda: self.find_next(False),
                  bg=self.t["chrome"], fg=self.t["fg"], bd=0, padx=8).pack(side="left", padx=2)
        tk.Button(self.findbar, text="Replace", command=self.replace_one,
                  bg=self.t["chrome"], fg=self.t["fg"], bd=0, padx=8).pack(side="left", padx=2)
        tk.Button(self.findbar, text="Close", command=self.hide_find,
                  bg=self.t["chrome"], fg=self.t["fg"], bd=0, padx=8).pack(side="right", padx=8)

    def build_status(self):
        bar = tk.Frame(self, bg=self.t["chrome"], height=24)
        bar.pack(fill="x", side="bottom")
        self.lbl_left = tk.Label(bar, text="", bg=self.t["chrome"], fg=self.t["dim"],
                                 font=(self.mono_family, 9), anchor="w")
        self.lbl_left.pack(side="left", padx=8)
        self.lbl_right = tk.Label(bar, text="", bg=self.t["chrome"], fg=self.t["dim"],
                                  font=(self.mono_family, 9), anchor="e")
        self.lbl_right.pack(side="right", padx=8)

    # ------------------------------------------------------------- helpers
    def _v(self, what):
        ed = self.editor()
        if not ed:
            return
        fn = getattr(ed, what, None)
        if fn:
            fn()
        elif what == "del_sel":
            s = ed.view.selection()
            if s:
                ed.doc.delete(s[0], s[1] - s[0])
                ed.refresh()

    def _panel(self, what):
        ed = self.editor()
        if ed:
            getattr(ed.console, what)()

    def editor(self):
        try:
            tab = self.tabs.nametowidget(self.tabs.select())
        except Exception:
            return None
        return tab if isinstance(tab, Editor) else None

    def view(self):
        ed = self.editor()
        return ed.view if ed else None

    def current_doc(self):
        ed = self.editor()
        return ed.doc if ed else None

    def status(self, msg):
        self._status_msg = msg
        self.update_status()

    def update_status(self):
        d = self.current_doc()
        if not d:
            self.lbl_left.configure(text=self._status_msg)
            self.lbl_right.configure(text="")
            return
        s = self.view().selection()
        sel = ("sel 0x%08X-0x%08X (%d)" % (s[0], s[1] - 1, s[1] - s[0])) if s else "no selection"
        cons = d.console.name if d.console else "unknown image"
        self.lbl_left.configure(
            text="offset 0x%08X  |  %s  |  %s  |  %s" %
                 (d.caret, sel, cons, "modified" if d.dirty else "clean"))
        self.lbl_right.configure(
            text="%s  |  length 0x%X (%s)  |  %s" %
                 (d.name(), d.size, human(d.size), self._status_msg))
        self.mode_lbl.configure(text="INS" if d.insert_mode else "OVR",
                                fg=self.t["accent"] if d.insert_mode else self.t["dim"])

    def field_under(self, off):
        d = self.current_doc()
        if not d or not d.console:
            return None
        for f in d.console.fields:
            o, length, label, kind, extra = f
            oo = o if o >= 0 else d.size + o
            if oo <= off < oo + max(length, 1):
                return "%s  (0x%X +%d)" % (label, oo, off - oo)
        return None

    # ---------------------------------------------------------------- files
    def open_dialog(self):
        paths = filedialog.askopenfilenames(title="Open image")
        for p in paths:
            self.open_path(p)

    def open_path(self, path):
        try:
            doc = Document(path)
        except Exception as exc:
            messagebox.showerror(APP, "Cannot open %s\n%s" % (path, exc))
            return
        ed = Editor(self.tabs, self, doc)
        self.tabs.add(ed, text=doc.name())
        self.tabs.select(ed)
        ed.draw_ruler()
        ed.refresh()
        if doc.console:
            self.status("%s detected (%d%%)" % (doc.console.name, doc.conf))
        else:
            self.status("opened %s -- unrecognised image" % doc.name())

    def new_file(self):
        d = Document()
        d.data = bytearray(4096)
        d.path = None
        ed = Editor(self.tabs, self, d)
        self.tabs.add(ed, text="Untitled")
        self.tabs.select(ed)
        ed.draw_ruler()
        ed.refresh()

    def save(self):
        return self.save_doc(self.current_doc())

    def save_doc(self, d, ed=None):
        """Save a document. Returns True on success, False if user cancelled Save As."""
        if not d:
            return False
        if not d.path:
            p = filedialog.asksaveasfilename(
                title="Save as", initialfile=d.name() or "Untitled.bin",
            )
            if not p:
                return False
            d.save(p)
        else:
            d.save()
        if ed is None:
            ed = self.editor()
        if ed and ed.doc is d:
            try:
                self.tabs.tab(ed, text=d.name())
            except tk.TclError:
                pass
        self.status("saved %s" % d.name())
        return True

    def save_as(self):
        d = self.current_doc()
        if not d:
            return False
        p = filedialog.asksaveasfilename(title="Save as", initialfile=d.name())
        if not p:
            return False
        d.save(p)
        ed = self.editor()
        if ed:
            self.tabs.tab(ed, text=d.name())
        self.status("saved %s" % d.name())
        return True

    def _ask_save_dirty(self, name):
        """
        Hex Fiend-style save prompt.
        Returns: True = save, False = discard (No), None = cancel.
        """
        return messagebox.askyesnocancel(
            APP,
            "Save changes to %s?\n\n"
            "Yes = save   No = discard   Cancel = stay" % name,
        )

    def close_tab(self):
        ed = self.editor()
        if not ed:
            return
        if ed.doc.dirty:
            ans = self._ask_save_dirty(ed.doc.name())
            if ans is None:  # Cancel — keep the tab open
                return
            if ans:  # Yes — save; abort close if Save As is cancelled
                if not self.save_doc(ed.doc, ed):
                    return
            # No — discard and close
        self.tabs.forget(ed)

    def quit_app(self):
        # Snapshot tabs first; indices shift if anything is closed mid-loop.
        tabs = list(self.tabs.tabs())
        for tab_id in tabs:
            try:
                ed = self.tabs.nametowidget(tab_id)
                doc = ed.doc
            except Exception:
                continue
            if not getattr(doc, "dirty", False):
                continue
            ans = self._ask_save_dirty(doc.name())
            if ans is None:  # Cancel — stay in the app
                return
            if ans:  # Yes
                self.tabs.select(tab_id)
                if not self.save_doc(doc, ed):
                    return  # Save As cancelled → abort quit
            # No — discard this tab's changes and keep quitting
        self.destroy()

    # -------------------------------------------------------------- search
    def show_find(self):
        self.findbar.pack(fill="x", after=self.tabs.master.children and self.winfo_children()[1])
        self.findbar.pack(fill="x")
        self.find_entry.focus_set()
        self.find_entry.select_range(0, "end")

    def hide_find(self):
        self.findbar.pack_forget()
        if self.view():
            self.view().focus_set()

    def find_next(self, forward):
        ed = self.editor()
        if ed:
            ed.search(self.find_entry.get(), self.find_mode.get(), forward, True)

    def replace_one(self):
        ed = self.editor()
        if ed:
            ed.replace_one(self.find_entry.get(), self.find_mode.get(),
                           self.repl_entry.get())

    def count_all(self):
        d = self.current_doc()
        if not d:
            return
        hits = d.find_all(self.find_entry.get(), self.find_mode.get())
        self.status("%d occurrence(s)" % len(hits))

    def goto(self):
        d = self.current_doc()
        if not d:
            return
        txt = simpledialog.askstring(APP, "Goto offset (hex, or dec with 'd'):",
                                     parent=self, initialvalue="%X" % d.caret)
        if not txt:
            return
        try:
            off = int(txt.strip().rstrip("dD"), 16) if not txt.strip().lower().endswith("d") \
                else int(txt.strip()[:-1], 10)
        except ValueError:
            return
        self.view().set_caret(off)

    # --------------------------------------------------------------- misc
    def context_menu(self, ev):
        ed = self.editor()
        if not ed:
            return
        m = tk.Menu(self, tearoff=0)
        m.add_command(label="Cut", command=ed.cut)
        m.add_command(label="Copy", command=ed.copy)
        m.add_command(label="Copy Hexadecimal", command=ed.copy_hex)
        m.add_command(label="Copy ASCII", command=ed.copy_ascii)
        m.add_command(label="Copy Entire File", command=ed.copy_entire_file)
        m.add_command(label="Paste", command=ed.paste)
        m.add_command(label="Select All", command=ed.select_all)
        m.add_separator()
        m.add_command(label="Add bookmark", command=ed.add_bookmark)
        m.add_separator()
        m.add_command(label="Fill selection...", command=self.fill_selection)
        m.add_command(label="Goto here", command=lambda: self.view().set_caret(
            self.view().pos_to_offset(ev.x, ev.y)[0]))
        m.tk_popup(ev.x_root, ev.y_root)

    def fill_selection(self):
        ed = self.editor()
        if not ed:
            return
        s = ed.view.selection()
        if not s:
            self.status("select a range first")
            return
        txt = simpledialog.askstring(APP, "Fill with (hex byte):", parent=self,
                                     initialvalue="FF")
        try:
            b = int(txt, 16) & 0xFF
        except (TypeError, ValueError):
            return
        ed.doc.fill(s[0], s[1] - s[0], b)
        ed.refresh()

    def insert_dialog(self):
        ed = self.editor()
        if not ed:
            return
        txt = simpledialog.askstring(APP, "Bytes to insert (hex):", parent=self,
                                     initialvalue="00" * 8)
        if not txt:
            return
        try:
            payload = bytes.fromhex(re.sub(r"[\s,_]", "", txt))
        except ValueError:
            return
        ed.doc.insert(ed.doc.caret, payload)
        ed.refresh()

    def hash_selection(self):
        d = self.current_doc()
        s = self.view().selection()
        if not d or not s:
            self.status("select a range first")
            return
        chunk = bytes(d.data[s[0]:s[1]])
        import hashlib
        messagebox.showinfo("Digest",
                            "length %d\ncrc32  %08X\nmd5    %s\nsha1   %s" %
                            (len(chunk), binascii.crc32(chunk) & 0xFFFFFFFF,
                             hashlib.md5(chunk).hexdigest(), hashlib.sha1(chunk).hexdigest()))

    def xor_selection(self):
        d = self.current_doc()
        s = self.view().selection()
        if not d or not s:
            self.status("select a range first")
            return
        txt = simpledialog.askstring(APP, "XOR key (hex):", parent=self, initialvalue="FF")
        try:
            key = bytes.fromhex(re.sub(r"[\s,_]", "", txt or "FF"))
        except ValueError:
            return
        if not key:
            return
        chunk = bytes(d.data[s[0]:s[1]])
        out = bytes(c ^ key[i % len(key)] for i, c in enumerate(chunk))
        d.overwrite(s[0], out)
        self.editor().refresh()
        self.status("xored %d bytes" % len(out))

    def force_console(self, cons):
        d = self.current_doc()
        if not d:
            return
        d.console, d.conf = cons, 100
        self.editor().console.refresh(d)
        self.update_status()

    def set_bpr(self, n):
        ed = self.editor()
        if ed:
            ed.view.bpr = n
            ed.view.redraw()
            ed.draw_ruler()

    def set_font(self, delta):
        ed = self.editor()
        if not ed:
            return
        ed.view.fsize = max(8, min(22, ed.view.fsize + delta))
        ed.view.mono.configure(size=ed.view.fsize)
        ed.view.redraw()
        ed.draw_ruler()

    def toggle_ascii(self):
        ed = self.editor()
        if ed:
            ed.view.show_ascii = not ed.view.show_ascii
            ed.view.redraw()
            ed.draw_ruler()

    def toggle_offsets(self):
        ed = self.editor()
        if ed:
            ed.view.show_offsets = not ed.view.show_offsets
            ed.view.redraw()

    def toggle_dark(self):
        self.t = dict(DARK if self.t is LIGHT else LIGHT)
        self.configure(bg=self.t["chrome"])
        for w in self.winfo_children():
            self._retint(w)
        for ed in self._editors():
            ed.view.t = self.t
            ed.view.configure(bg=self.t["field"])
            ed.view.redraw()
            ed.draw_ruler()
            ed.inspector.configure(bg=self.t["panel"])

    def _editors(self):
        out = []
        for i in range(self.tabs.index("end")):
            try:
                w = self.tabs.nametowidget(self.tabs.tabs()[i])
            except Exception:
                continue
            if isinstance(w, Editor):
                out.append(w)
        return out

    def _retint(self, w):
        try:
            w.configure(bg=self.t["chrome"])
        except tk.TclError:
            pass
        for c in w.winfo_children():
            self._retint(c)

    def show_db(self):
        win = tk.Toplevel(self)
        win.title("Console database")
        win.configure(bg=self.t["panel"])
        txt = tk.Text(win, width=58, height=32, bd=0, bg=self.t["field"],
                      fg=self.t["fg"], font=(self.mono_family, 10))
        txt.pack(padx=10, pady=10)
        lines = []
        for fam in FAMILIES:
            lines.append("[%s]" % fam)
            for c in CONSOLES:
                if c.family == fam:
                    lines.append("   %-26s %s" % (c.name, ", ".join(c.exts) or ""))
            lines.append("")
        txt.insert("1.0", "\n".join(lines))
        txt.configure(state="disabled")

    def about(self):
        messagebox.showinfo(
            "About",
            "%s  (%s)\n\n"
            "Hex Fiend-inspired hex editor for every console from\n"
            "Atari 2600 to Switch 2.\n\n"
            "%d systems in the signature database.\n"
            "Insert/Overwrite, undo/redo, find, goto, inspector,\n"
            "header templates and checksum verifiers." % (APP, BUILD, len(CONSOLES)))


def human(n):
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if n < 1024:
            return "%.1f %s" % (n, unit)
        n /= 1024.0
    return "%.1f PB" % n


def main():
    app = App()
    for p in sys.argv[1:]:
        if os.path.exists(p):
            app.open_path(p)
    app.mainloop()


if __name__ == "__main__":
    main()