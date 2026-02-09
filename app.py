# -*- coding: utf-8 -*-
from __future__ import annotations
r"""
PDFページ欠落チェック（スキャンPDF向け） v1.2.11

v1.2.11 変更点
- FIXED_POPPLER 未定義エラーの修正（DEFAULT_POPPLERに統一）

v1.2.3 変更点
- 「画質プレビュー」機能を追加：指定ページの「原画像」と「前処理後（コントラスト/しきい値/反転）」を並べて確認可能
- 画質プレビュー上に ROI（左/右）枠を重ねて表示できる（開き方向/奇数偶数に応じた利用ROIも表示）
- v1.2.2で混入していた省略記号（...）等の不完全コードを排除し、ROIプレビュー等が確実に動作する版に整理

必要（Python）:
    pip install pillow pdf2image pytesseract
外部:
    Poppler（pdf2image用）と Tesseract（OCR本体）

ログ:
    %USERPROFILE%\.pdf_page_checker\app.log
"""


import os
import re
import sys
import json
import time
import queue
import shutil
import hashlib
import threading
import traceback
import unicodedata
from dataclasses import dataclass
from typing import Optional, Tuple, List, Dict, Any

import tkinter as tk
from tkinter import ttk, filedialog, messagebox, scrolledtext

# ---- Default external app paths (editable) ----
DEFAULT_TESSERACT = r"C:\Program Files\Tesseract-OCR\tesseract.exe"
DEFAULT_POPPLER   = r"C:\poppler\Library\bin"
DEFAULT_ROI_TEST_PAGE = 30

APP_NAME = "PDFページ欠落チェック"
APP_VERSION = "1.2.11"

APP_HOME = os.path.join(os.path.expanduser("~"), ".pdf_page_checker")
CONFIG_BASENAME = "pdf_page_checker_scan_config.json"
LEGACY_CONFIG_PATH = os.path.join(APP_HOME, "pdf_page_checker_config.json")
CONFIG_PATH = os.path.join(APP_HOME, CONFIG_BASENAME)
CACHE_ROOT = os.path.join(APP_HOME, "cache")
LOG_PATH = os.path.join(APP_HOME, "app.log")

# -----------------------------
# Preflight: optional imports (checked at startup)
# -----------------------------
PIL_IMPORT_ERROR = None
try:
    from PIL import Image, ImageTk, ImageOps, ImageEnhance, ImageDraw
except Exception as e:
    PIL_IMPORT_ERROR = e
    Image = None
    ImageTk = None
    ImageOps = None
    ImageEnhance = None
    ImageDraw = None

try:
    from pdf2image import convert_from_path, pdfinfo_from_path
except Exception:
    convert_from_path = None
    pdfinfo_from_path = None

try:
    import pytesseract
except Exception:
    pytesseract = None

# Pillow resampling compatibility
if Image is not None:
    try:
        RESAMPLE_LANCZOS = Image.Resampling.LANCZOS
        RESAMPLE_NEAREST = Image.Resampling.NEAREST
    except Exception:
        RESAMPLE_LANCZOS = getattr(Image, "LANCZOS", Image.BICUBIC)
        RESAMPLE_NEAREST = getattr(Image, "NEAREST", Image.BILINEAR)
else:
    RESAMPLE_LANCZOS = None
    RESAMPLE_NEAREST = None

DEFAULT_CONFIG: Dict[str, Any] = {
    "last_pdf_path": "",
    "poppler_path": DEFAULT_POPPLER,
    "tesseract_cmd": DEFAULT_TESSERACT,
    "dpi": 250,
    "opening": "left",  # "left"=左開き / "right"=右開き

    # ROI: x1,y1,x2,y2 in 0..1
    "roi_left":  [0.00, 0.00, 0.18, 0.12],
    "roi_right": [0.82, 0.00, 1.00, 0.12],

    "roi_padding_pct": 0.01,
    "contrast": 2.0,
    "threshold": 170,
    "invert": False,
    "try_rotate": True,
    "cache_enabled": True,
    "preview_preprocessed": True,
    "roman_enabled": True,
    "roi_test_page": DEFAULT_ROI_TEST_PAGE,

    # "auto"|"eng"|"jpn"|"eng+jpn"
    "tess_lang": "auto",
}

# -----------------------------
# Utilities
# -----------------------------
def ensure_dirs():
    os.makedirs(APP_HOME, exist_ok=True)
    os.makedirs(CACHE_ROOT, exist_ok=True)

def log_write(msg: str):
    try:
        ensure_dirs()
        with open(LOG_PATH, "a", encoding="utf-8") as f:
            f.write(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] {msg}\n")
    except Exception:
        pass

def load_config() -> Dict[str, Any]:
    ensure_dirs()
    # Config file name is unique to this app (to avoid collisions).
    # If the new config does not exist, try legacy config.json once.
    cfg_path = CONFIG_PATH if os.path.exists(CONFIG_PATH) else (LEGACY_CONFIG_PATH if os.path.exists(LEGACY_CONFIG_PATH) else None)
    cfg: Dict[str, Any] = {}
    if cfg_path:
        try:
            with open(cfg_path, "r", encoding="utf-8") as f:
                cfg = json.load(f) or {}
        except Exception as e:
            log_write("config load failed: " + repr(e))
            cfg = {}

    merged = dict(DEFAULT_CONFIG)
    merged.update(cfg)

    # ROI is per-session; do not load persisted ROI even if present in old config
    merged["roi_left"] = list(DEFAULT_CONFIG["roi_left"])
    merged["roi_right"] = list(DEFAULT_CONFIG["roi_right"])

    # normalize
    try:
        merged["dpi"] = int(merged.get("dpi", DEFAULT_CONFIG["dpi"]))
    except Exception:
        merged["dpi"] = DEFAULT_CONFIG["dpi"]

    if merged.get("opening") not in ("left", "right"):
        merged["opening"] = DEFAULT_CONFIG["opening"]

    try:
        merged["roi_test_page"] = int(merged.get("roi_test_page", DEFAULT_ROI_TEST_PAGE))
    except Exception:
        merged["roi_test_page"] = DEFAULT_ROI_TEST_PAGE

    if merged.get("tess_lang") not in ("auto", "eng", "jpn", "eng+jpn"):
        merged["tess_lang"] = "auto"

    # paths: keep defaults if empty
    if not merged.get("poppler_path"):
        merged["poppler_path"] = DEFAULT_POPPLER
    if not merged.get("tesseract_cmd"):
        merged["tesseract_cmd"] = DEFAULT_TESSERACT

    return merged

def save_config(cfg: Dict[str, Any]) -> None:
    """Save config *without* persisting ROI rectangles.
    ROI is treated as a per-session setting per user request.
    """
    ensure_dirs()
    cfg2 = dict(cfg)
    # Do NOT persist ROI across restarts
    cfg2.pop("roi_left", None)
    cfg2.pop("roi_right", None)
    try:
        with open(CONFIG_PATH, "w", encoding="utf-8") as f:
            json.dump(cfg2, f, ensure_ascii=False, indent=2)
    except Exception as e:
        log_write("config save failed: " + repr(e))


def compute_pdf_id(pdf_path: str) -> str:
    st = os.stat(pdf_path)
    s = f"{os.path.abspath(pdf_path)}|{st.st_size}|{int(st.st_mtime)}"
    return hashlib.md5(s.encode("utf-8")).hexdigest()

def get_cache_dir(pdf_id: str) -> str:
    return os.path.join(CACHE_ROOT, pdf_id)

def clamp01(x: float) -> float:
    return max(0.0, min(1.0, x))

def expand_roi(roi: Tuple[float, float, float, float], pad: float) -> Tuple[float, float, float, float]:
    x1, y1, x2, y2 = roi
    x1 = clamp01(x1 - pad)
    y1 = clamp01(y1 - pad)
    x2 = clamp01(x2 + pad)
    y2 = clamp01(y2 + pad)
    if x2 <= x1:
        x2 = min(1.0, x1 + 0.01)
    if y2 <= y1:
        y2 = min(1.0, y1 + 0.01)
    return x1, y1, x2, y2

def roi_to_px(roi: Tuple[float, float, float, float], w: int, h: int) -> Tuple[int, int, int, int]:
    x1, y1, x2, y2 = roi
    return (int(x1 * w), int(y1 * h), int(x2 * w), int(y2 * h))

# -----------------------------
# PDF -> image
# -----------------------------
def pdf_page_count(pdf_path: str, poppler_path: str) -> int:
    if pdfinfo_from_path is None:
        raise RuntimeError("pdf2image が必要です。pip install pdf2image")
    info = pdfinfo_from_path(pdf_path, poppler_path=poppler_path)
    return int(info.get("Pages", 0))

def load_page_image(
    pdf_path: str,
    page_num: int,
    dpi: int,
    cache_dir: Optional[str],
    poppler_path: str,
) -> "Image.Image":
    if cache_dir:
        os.makedirs(cache_dir, exist_ok=True)
        img_path = os.path.join(cache_dir, f"page_{page_num:05d}.png")
        if os.path.exists(img_path):
            return Image.open(img_path).convert("RGB")

    if convert_from_path is None:
        raise RuntimeError("pdf2image が必要です。pip install pdf2image")

    imgs = convert_from_path(
        pdf_path,
        dpi=dpi,
        first_page=page_num,
        last_page=page_num,
        poppler_path=poppler_path,
        fmt="png",
        thread_count=1,
    )
    if not imgs:
        raise RuntimeError(f"PDFのページ画像化に失敗: page={page_num}")
    img = imgs[0].convert("RGB")

    if cache_dir:
        try:
            img.save(os.path.join(cache_dir, f"page_{page_num:05d}.png"))
        except Exception as e:
            log_write("cache save failed: " + repr(e))
    return img

# -----------------------------
# Spinbox compatibility
# -----------------------------
def make_spinbox(parent, **kwargs):
    if hasattr(ttk, "Spinbox"):
        return ttk.Spinbox(parent, **kwargs)
    return tk.Spinbox(parent, **kwargs)

# -----------------------------
# Roman numerals
# -----------------------------
_ROMAN_MAP = {"I": 1, "V": 5, "X": 10, "L": 50, "C": 100, "D": 500, "M": 1000}

def int_to_roman(n: int) -> str:
    if not (0 < n < 4000):
        return ""
    vals = [
        (1000, "M"), (900, "CM"), (500, "D"), (400, "CD"),
        (100, "C"), (90, "XC"), (50, "L"), (40, "XL"),
        (10, "X"), (9, "IX"), (5, "V"), (4, "IV"), (1, "I"),
    ]
    out = []
    for v, sym in vals:
        while n >= v:
            out.append(sym)
            n -= v
    return "".join(out)

def roman_to_int(s: str) -> Optional[int]:
    s = s.strip().upper()
    if not s or not re.fullmatch(r"[IVXLCDM]+", s):
        return None
    total = 0
    prev = 0
    for ch in reversed(s):
        v = _ROMAN_MAP.get(ch, 0)
        if v < prev:
            total -= v
        else:
            total += v
            prev = v
    if int_to_roman(total) != s:
        return None
    return total

# -----------------------------
# OCR helpers
# -----------------------------
def preprocess_for_ocr(
    img: "Image.Image",
    contrast: float,
    threshold: Optional[int],
    invert: bool,
    scale: float = 3.0,
    binarize: bool = True,
) -> "Image.Image":
    g = img.convert("L")
    g = ImageOps.autocontrast(g)
    if contrast and abs(contrast - 1.0) > 1e-3:
        g = ImageEnhance.Contrast(g).enhance(float(contrast))
    if scale and scale != 1.0:
        nw = max(1, int(g.size[0] * scale))
        nh = max(1, int(g.size[1] * scale))
        g = g.resize((nw, nh), RESAMPLE_LANCZOS)
    if binarize and threshold is not None:
        t = int(max(0, min(255, int(threshold))))
        g = g.point(lambda p: 255 if p >= t else 0)
    if invert:
        g = ImageOps.invert(g)
    return g

def _to_ascii_digits(s: str) -> str:
    """Unicode数字を ASCII に寄せる（全角・丸数字など→0-9）。"""
    out = []
    for ch in s:
        try:
            d = unicodedata.digit(ch)
            out.append(str(d))
            continue
        except Exception:
            pass
        try:
            n = unicodedata.numeric(ch)
            if float(n).is_integer() and 0 <= int(n) <= 9:
                out.append(str(int(n)))
                continue
        except Exception:
            pass
        out.append(ch)
    return "".join(out)

_KANJI_DIGITS = {
    "〇": 0, "零": 0,
    "一": 1, "二": 2, "三": 3, "四": 4, "五": 5, "六": 6, "七": 7, "八": 8, "九": 9,
    "壱": 1, "弐": 2, "参": 3, "肆": 4, "伍": 5, "陸": 6, "漆": 7, "捌": 8, "玖": 9,
}
_KANJI_UNITS = {"十": 10, "拾": 10, "百": 100, "佰": 100, "千": 1000, "仟": 1000}
_KANJI_BIG = {"万": 10000, "萬": 10000}

def kanji_to_int(s: str) -> Optional[int]:
    """漢数字（例: 七, 十二, 二百三, 三一, 一〇二）を int に変換。"""
    if not s:
        return None
    s = s.strip()
    if not re.fullmatch(r"[〇零一二三四五六七八九壱弐参肆伍陸漆捌玖十拾百佰千仟万萬]+", s):
        return None

    def parse_small(part: str) -> Optional[int]:
        total = 0
        num = 0
        for ch in part:
            if ch in _KANJI_DIGITS:
                num = _KANJI_DIGITS[ch]
            elif ch in _KANJI_UNITS:
                unit = _KANJI_UNITS[ch]
                if num == 0:
                    num = 1
                total += num * unit
                num = 0
            else:
                return None
        total += num
        return total

    total = 0
    buf = ""
    for ch in s:
        if ch in _KANJI_BIG:
            big = _KANJI_BIG[ch]
            small = parse_small(buf) if buf else 1
            if small is None:
                return None
            total += small * big
            buf = ""
        else:
            buf += ch
    if buf:
        small = parse_small(buf)
        if small is None:
            return None
        total += small
    return total if total > 0 else None

def extract_int_from_text(s: str) -> Optional[int]:
    if not s:
        return None
    s = _to_ascii_digits(s)
    s = s.replace("—", "-").replace("–", "-")
    m = re.search(r"([0-9]{1,6})", s)
    if m:
        try:
            return int(m.group(1))
        except Exception:
            pass
    km = re.search(r"([〇零一二三四五六七八九壱弐参肆伍陸漆捌玖十拾百佰千仟万萬]{1,20})", s)
    if km:
        v = kanji_to_int(km.group(1))
        if v is not None:
            return v
    return None

def extract_roman_from_text(s: str) -> Tuple[Optional[int], str]:
    if not s:
        return (None, "")
    s = s.replace("—", "-").replace("–", "-")
    rm = re.search(r"\b([IVXLCDMivxlcdm]{1,12})\b", s)
    if not rm:
        return (None, "")
    val = roman_to_int(rm.group(1))
    return (val, rm.group(1))

def _set_tesseract_cmd(cmd: str):
    if pytesseract is None:
        return
    try:
        pytesseract.pytesseract.tesseract_cmd = cmd
    except Exception as e:
        log_write("set tesseract_cmd failed: " + repr(e))

def get_available_langs(tesseract_cmd: str) -> List[str]:
    if pytesseract is None:
        return []
    _set_tesseract_cmd(tesseract_cmd)
    try:
        langs = pytesseract.get_languages(config="")
        return [x.strip() for x in langs if x and x.strip()]
    except Exception as e:
        log_write("get_languages failed: " + repr(e))
        return []

def resolve_lang(lang_setting: str, available_langs: List[str]) -> str:
    """auto のとき、eng/jpn が両方あるなら eng+jpn。なければある方。"""
    if lang_setting in ("eng", "jpn", "eng+jpn"):
        return lang_setting
    if "eng" in available_langs and "jpn" in available_langs:
        return "eng+jpn"
    for cand in ("eng", "jpn"):
        if cand in available_langs:
            return cand
    return "eng"

def _ocr_tokens(proc_img: "Image.Image", lang: str, psm: int, whitelist: Optional[str]) -> List[Tuple[str, float]]:
    """
    image_to_data で token と confidence を取り、ノイズを除いた候補を返す。
    """
    if pytesseract is None:
        return []
    cfg = f"--oem 3 --psm {psm}"
    if whitelist:
        cfg += f' -c tessedit_char_whitelist="{whitelist}"'
    try:
        data = pytesseract.image_to_data(proc_img, lang=lang, config=cfg, output_type=pytesseract.Output.DICT)
    except Exception as e:
        return [(f"OCR error: {e}", 0.0)]
    toks: List[Tuple[str, float]] = []
    n = len(data.get("text", []))
    for i in range(n):
        txt = (data["text"][i] or "").strip()
        if not txt:
            continue
        try:
            conf = float(data.get("conf", [0])[i])
        except Exception:
            conf = 0.0
        if conf < 0:
            conf = 0.0
        toks.append((txt, conf))
    return toks

@dataclass
class OCRResult:
    value_type: str                 # "arabic" | "roman" | "none"
    value_int: Optional[int]
    value_str: str
    raw_text: str
    rotation_used: int
    ok: bool
    detail: str

def ocr_extract_value(
    roi_img: "Image.Image",
    tesseract_cmd: str,
    contrast: float,
    threshold: int,
    invert_user: bool,
    try_rotate: bool,
    roman_enabled: bool,
    lang: str,
) -> OCRResult:
    """ROI画像からページ番号を抽出。whitelist あり/なしを両方試す（漢数字・記号混在対策）。"""
    if pytesseract is None:
        return OCRResult("none", None, "", "pytesseract が未インストールです", 0, False, "no pytesseract")

    _set_tesseract_cmd(tesseract_cmd)

    rotations = [0, 180, 90, 270] if try_rotate else [0]
    invert_list = [bool(invert_user), (not bool(invert_user))]  # user / auto
    binarize_list = [True, False]
    thr0 = int(max(0, min(255, int(threshold))))
    thr_list = [thr0, max(0, thr0 - 20), min(255, thr0 + 20)]
    psm_list = [7, 6, 11]

    whitelist = "0123456789０１２３４５６７８９IVXLCDMivxlcdm()[]-–— "
    whitelist_list: List[Optional[str]] = [whitelist, None]  # None=whitelist無し

    best: Optional[OCRResult] = None

    def maybe_update(cand: OCRResult):
        nonlocal best
        if best is None:
            best = cand
            return
        if cand.ok and not best.ok:
            best = cand
            return
        if cand.ok == best.ok:
            rank = {"arabic": 3, "roman": 2, "none": 0}
            if rank.get(cand.value_type, 0) > rank.get(best.value_type, 0):
                best = cand

    for rot in rotations:
        img_rot = roi_img.rotate(rot, expand=True) if rot else roi_img

        for inv in invert_list:
            for binarize in binarize_list:
                for thr in thr_list:
                    thr_use = thr if binarize else None
                    proc = preprocess_for_ocr(
                        img_rot,
                        contrast=float(contrast),
                        threshold=thr_use,
                        invert=bool(inv),
                        scale=3.0,
                        binarize=bool(binarize),
                    )

                    # 1) token OCR
                    for psm in psm_list:
                        found_any = False
                        for wl in whitelist_list:
                            toks = _ocr_tokens(proc, lang=lang, psm=psm, whitelist=wl)
                            joined = ""
                            if toks:
                                toks_sorted = sorted(toks, key=lambda x: x[1], reverse=True)
                                joined = " ".join(t for t, c in toks_sorted[:10])

                            v = extract_int_from_text(joined)
                            if v is not None:
                                cand = OCRResult("arabic", v, str(v), joined, rot, True,
                                                 f"data psm={psm} thr={thr_use} inv={inv} bin={binarize} wl={'on' if wl else 'off'}")
                                maybe_update(cand)
                                found_any = True
                                break

                            if roman_enabled:
                                rv, rstr = extract_roman_from_text(joined)
                                if rv is not None:
                                    cand = OCRResult("roman", rv, rstr, joined, rot, True,
                                                     f"data psm={psm} thr={thr_use} inv={inv} bin={binarize} wl={'on' if wl else 'off'}")
                                    maybe_update(cand)
                                    found_any = True
                                    break

                            cand = OCRResult("none", None, "", joined, rot, False,
                                             f"data psm={psm} thr={thr_use} inv={inv} bin={binarize} wl={'on' if wl else 'off'}")
                            maybe_update(cand)

                        if found_any:
                            break

                    if best and best.ok and best.value_type == "arabic":
                        return best

                    # 2) string OCR fallback
                    for psm in psm_list:
                        for wl in whitelist_list:
                            cfg = f"--oem 3 --psm {psm}"
                            if wl:
                                cfg += f' -c tessedit_char_whitelist="{wl}"'
                            try:
                                raw = pytesseract.image_to_string(proc, lang=lang, config=cfg)
                            except Exception as e:
                                raw = f"OCR error: {e}"
                            raw_s = (raw or "").strip()

                            v2 = extract_int_from_text(raw_s)
                            if v2 is not None:
                                cand2 = OCRResult("arabic", v2, str(v2), raw_s, rot, True,
                                                  f"str psm={psm} thr={thr_use} inv={inv} bin={binarize} wl={'on' if wl else 'off'}")
                                maybe_update(cand2)
                                break

                            if roman_enabled:
                                rv2, rstr2 = extract_roman_from_text(raw_s)
                                if rv2 is not None:
                                    cand2 = OCRResult("roman", rv2, rstr2, raw_s, rot, True,
                                                      f"str psm={psm} thr={thr_use} inv={inv} bin={binarize} wl={'on' if wl else 'off'}")
                                    maybe_update(cand2)
                                    break

                            cand2 = OCRResult("none", None, "", raw_s, rot, False,
                                              f"str psm={psm} thr={thr_use} inv={inv} bin={binarize} wl={'on' if wl else 'off'}")
                            maybe_update(cand2)

                        if best and best.ok and best.value_type == "arabic":
                            break

                    if best and best.ok and best.value_type == "arabic":
                        return best

    return best or OCRResult("none", None, "", "", 0, False, "no result")

# -----------------------------
# Result structures
# -----------------------------
@dataclass
class PageCheckResult:
    pdf_page: int
    used_roi: str                   # "left" or "right"
    detected: str
    detected_type: str              # "arabic" | "roman" | "none"
    detected_int: Optional[int]
    reason: str
    severity: str                   # "OK" | "WARN" | "NG"
    raw_text: str
    rotation_used: int
    roi_box_px: Tuple[int, int, int, int]

# -----------------------------
# ROI Editor: explicit commit button
# -----------------------------
class ROIEditor(tk.Toplevel):
    """
    重要仕様:
    - ROIは「決定(Enter)」またはダブルクリックでのみ確定・保存
    - ×(右上) / Esc はキャンセル（保存されない）
    """
    def __init__(self, master, title: str, img: "Image.Image", init_roi: Tuple[float, float, float, float]):
        super().__init__(master)
        self.title(title)
        self.resizable(True, True)
        self.minsize(820, 560)

        self.original = img
        self.init_roi = init_roi
        self.result_roi: Optional[Tuple[float, float, float, float]] = None
        self.current_roi: Optional[Tuple[float, float, float, float]] = None

        self.columnconfigure(0, weight=1)
        self.rowconfigure(0, weight=1)
        self.rowconfigure(1, weight=0)

        body = ttk.Frame(self)
        body.grid(row=0, column=0, sticky="nsew", padx=8, pady=8)
        body.columnconfigure(0, weight=1)
        body.rowconfigure(0, weight=1)
        body.rowconfigure(1, weight=0)

        max_w = 1100
        max_h = 920
        ow, oh = self.original.size
        self.scale = min(max_w / ow, max_h / oh, 1.0)
        self.disp = self.original.resize((int(ow * self.scale), int(oh * self.scale)), RESAMPLE_LANCZOS)
        self.disp_tk = ImageTk.PhotoImage(self.disp)

        self.canvas = tk.Canvas(body, bg="black", highlightthickness=0)
        self.canvas.grid(row=0, column=0, sticky="nsew")
        self.canvas.create_image(0, 0, anchor="nw", image=self.disp_tk)
        self.canvas.config(width=self.disp.size[0], height=self.disp.size[1])

        self.info = tk.StringVar(value="ドラッグしてROIを指定 → [決定]で保存（×はキャンセル）")
        ttk.Label(body, textvariable=self.info).grid(row=1, column=0, sticky="w", pady=(6, 0))

        btns = ttk.Frame(self)
        btns.grid(row=1, column=0, sticky="ew", padx=10, pady=10)
        btns.columnconfigure(0, weight=1)

        ttk.Button(btns, text="初期ROIへ戻す", command=self.reset_roi).grid(row=0, column=0, sticky="w")
        ttk.Button(btns, text="決定(Enter)", command=self.on_commit).grid(row=0, column=1, sticky="e", padx=(0, 8))
        ttk.Button(btns, text="キャンセル(Esc/×)", command=self.on_cancel).grid(row=0, column=2, sticky="e")

        self.rect_id = None
        self.start_xy = None

        self.canvas.bind("<Button-1>", self.on_down)
        self.canvas.bind("<B1-Motion>", self.on_drag)
        self.canvas.bind("<ButtonRelease-1>", self.on_up)
        self.canvas.bind("<Double-Button-1>", lambda e: self.on_commit())

        self.bind("<Return>", lambda e: self.on_commit())
        self.bind("<Escape>", lambda e: self.on_cancel())
        self.protocol("WM_DELETE_WINDOW", self.on_cancel)

        self.reset_roi()
        self.grab_set()

    def _set_current_roi_from_rect(self):
        if not self.rect_id:
            self.current_roi = None
            return
        coords = self.canvas.coords(self.rect_id)
        if len(coords) != 4:
            self.current_roi = None
            return

        x1c, y1c, x2c, y2c = coords
        dx1 = min(x1c, x2c)
        dx2 = max(x1c, x2c)
        dy1 = min(y1c, y2c)
        dy2 = max(y1c, y2c)

        dx1 = max(0, min(self.disp.size[0], dx1))
        dx2 = max(0, min(self.disp.size[0], dx2))
        dy1 = max(0, min(self.disp.size[1], dy1))
        dy2 = max(0, min(self.disp.size[1], dy2))

        ow, oh = self.original.size
        x1p = dx1 / (ow * self.scale)
        x2p = dx2 / (ow * self.scale)
        y1p = dy1 / (oh * self.scale)
        y2p = dy2 / (oh * self.scale)

        x1p, y1p, x2p, y2p = clamp01(x1p), clamp01(y1p), clamp01(x2p), clamp01(y2p)
        if x2p <= x1p or y2p <= y1p:
            self.current_roi = None
            return
        self.current_roi = (x1p, y1p, x2p, y2p)

    def reset_roi(self):
        if self.rect_id:
            self.canvas.delete(self.rect_id)
        x1, y1, x2, y2 = self.init_roi
        ow, oh = self.original.size
        dx1 = int(x1 * ow * self.scale)
        dy1 = int(y1 * oh * self.scale)
        dx2 = int(x2 * ow * self.scale)
        dy2 = int(y2 * oh * self.scale)
        self.rect_id = self.canvas.create_rectangle(dx1, dy1, dx2, dy2, outline="red", width=2)
        self._set_current_roi_from_rect()
        if self.current_roi:
            cx1, cy1, cx2, cy2 = self.current_roi
            self.info.set(f"初期ROI: x1={cx1:.3f}, y1={cy1:.3f}, x2={cx2:.3f}, y2={cy2:.3f}")

    def on_down(self, event):
        self.start_xy = (event.x, event.y)
        if self.rect_id:
            self.canvas.delete(self.rect_id)
            self.rect_id = None
        self.current_roi = None

    def on_drag(self, event):
        if not self.start_xy:
            return
        x0, y0 = self.start_xy
        x1, y1 = event.x, event.y
        if self.rect_id:
            self.canvas.coords(self.rect_id, x0, y0, x1, y1)
        else:
            self.rect_id = self.canvas.create_rectangle(x0, y0, x1, y1, outline="red", width=2)

    def on_up(self, event):
        if not self.rect_id:
            return
        self.start_xy = None
        self._set_current_roi_from_rect()
        if not self.current_roi:
            self.info.set("ROIが小さすぎます。ドラッグし直してください。")
            return
        x1p, y1p, x2p, y2p = self.current_roi
        self.info.set(f"ROI: x1={x1p:.3f}, y1={y1p:.3f}, x2={x2p:.3f}, y2={y2p:.3f}  ※[決定]で保存")

    def on_commit(self):
        if not self.rect_id:
            messagebox.showwarning(APP_NAME, "ROIが未指定です。ドラッグして範囲を指定してください。")
            return
        self._set_current_roi_from_rect()
        if not self.current_roi:
            messagebox.showwarning(APP_NAME, "ROIが小さすぎます。ドラッグし直してください。")
            return
        self.result_roi = self.current_roi
        self.destroy()

    def on_cancel(self):
        self.result_roi = None
        self.destroy()



# -----------------------------
# Quality Preview Window (page-level)
# -----------------------------
class QualityPreviewWindow(tk.Toplevel):
    """
    指定ページの「原画像」と「前処理後（コントラスト/しきい値/反転）」を並べて表示します。
    画質調整がOCRに効いているか、ROIが狙い通りかを目視確認するためのウィンドウです。
    """
    def __init__(self, master: "App"):
        super().__init__(master)
        self.app = master
        self.title("画質プレビュー（原画像 / 前処理後）")
        self.geometry("1320x780")
        self.minsize(980, 620)

        self.columnconfigure(0, weight=1)
        self.rowconfigure(1, weight=1)

        # ---- controls ----
        ctrl = ttk.Frame(self)
        ctrl.grid(row=0, column=0, sticky="ew", padx=10, pady=10)
        ctrl.columnconfigure(10, weight=1)

        ttk.Label(ctrl, text="ページ:").grid(row=0, column=0, sticky="w")
        self.var_page = tk.IntVar(value=self._default_page())
        self.spn_page = make_spinbox(ctrl, from_=1, to=max(1, self._page_max()), textvariable=self.var_page, width=7)
        self.spn_page.grid(row=0, column=1, sticky="w", padx=(6, 10))

        self.var_show_roi = tk.BooleanVar(value=True)
        ttk.Checkbutton(ctrl, text="ROI枠を表示", variable=self.var_show_roi, command=self.refresh).grid(row=0, column=2, sticky="w", padx=(0, 10))

        self.var_show_both = tk.BooleanVar(value=True)
        ttk.Checkbutton(ctrl, text="左/右ROIを両方表示", variable=self.var_show_both, command=self.refresh).grid(row=0, column=3, sticky="w", padx=(0, 10))

        ttk.Label(ctrl, text="※前処理はメイン画面の設定（コントラスト/しきい値/反転）を使用").grid(row=0, column=4, sticky="w")

        ttk.Button(ctrl, text="更新", command=self.refresh).grid(row=0, column=11, sticky="e")

        self.var_info = tk.StringVar(value="")
        ttk.Label(ctrl, textvariable=self.var_info).grid(row=1, column=0, columnspan=12, sticky="w", pady=(6, 0))

        # ---- images ----
        body = ttk.Frame(self)
        body.grid(row=1, column=0, sticky="nsew", padx=10, pady=(0, 10))
        body.columnconfigure(0, weight=1)
        body.columnconfigure(1, weight=1)
        body.rowconfigure(0, weight=1)

        frm_a = ttk.LabelFrame(body, text="原画像")
        frm_b = ttk.LabelFrame(body, text="前処理後（プレビュー用）")
        frm_a.grid(row=0, column=0, sticky="nsew", padx=(0, 8))
        frm_b.grid(row=0, column=1, sticky="nsew", padx=(8, 0))
        frm_a.rowconfigure(0, weight=1); frm_a.columnconfigure(0, weight=1)
        frm_b.rowconfigure(0, weight=1); frm_b.columnconfigure(0, weight=1)
        self.canvas_a = tk.Canvas(frm_a, bg="black", highlightthickness=0)
        self.canvas_b = tk.Canvas(frm_b, bg="black", highlightthickness=0)
        self.canvas_a.grid(row=0, column=0, sticky="nsew", padx=8, pady=8)
        self.canvas_b.grid(row=0, column=0, sticky="nsew", padx=8, pady=8)

        self._tk_a = None
        self._tk_b = None

        self.bind("<Return>", lambda e: self.refresh())
        self.protocol("WM_DELETE_WINDOW", self.destroy)

        self.refresh()

    def _default_page(self) -> int:
        # 優先: 選択行 → なければ ROIテストページ
        try:
            sel = self.app.tree.selection()
            if sel:
                return int(sel[0])
        except Exception:
            pass
        try:
            return int(self.app.var_roi_page.get())
        except Exception:
            return int(self.app.cfg.get("roi_test_page", DEFAULT_ROI_TEST_PAGE))

    def _page_max(self) -> int:
        try:
            if self.app.total_pages:
                return int(self.app.total_pages)
        except Exception:
            pass
        # まだ解析していない場合はPDFから取得
        pdf_path = self.app.var_pdf.get().strip()
        if pdf_path and os.path.exists(pdf_path):
            try:
                # FIXED: DEFAULT_POPPLER
                return int(pdf_page_count(pdf_path, poppler_path=self.app.var_poppler.get().strip() or DEFAULT_POPPLER))
            except Exception:
                return 1
        return 1

    def _draw_roi_boxes(self, img: Image.Image, page: int) -> Image.Image:
        if not self.var_show_roi.get():
            return img

        opening = self.app.var_opening.get()
        pad = float(self.app.var_pad.get())
        roi_left = expand_roi(tuple(self.app.cfg.get("roi_left", DEFAULT_CONFIG["roi_left"])), pad)
        roi_right = expand_roi(tuple(self.app.cfg.get("roi_right", DEFAULT_CONFIG["roi_right"])), pad)

        w, h = img.size
        box_l = roi_to_px(roi_left, w, h)
        box_r = roi_to_px(roi_right, w, h)

        # which ROI is used for this page
        is_odd = (page % 2 == 1)
        use_right = is_odd if opening == "left" else (not is_odd)
        used = "right" if use_right else "left"

        draw = ImageDraw.Draw(img)
        if self.var_show_both.get():
            # left / right
            draw.rectangle(box_l, outline="red", width=4)
            draw.rectangle(box_r, outline="blue", width=4)
        else:
            draw.rectangle(box_r if used == "right" else box_l, outline="red", width=4)

        # small label (top-left)
        try:
            draw.rectangle((0, 0, 360, 38), fill=(0, 0, 0))
        except Exception:
            pass
        try:
            draw.text((8, 8), f"page={page} / opening={opening} / used ROI={used}", fill="white")
        except Exception:
            pass

        return img

    def _fit(self, img: Image.Image, maxw: int, maxh: int) -> Image.Image:
        w, h = img.size
        sc = min(maxw / w, maxh / h, 1.0)
        if sc <= 0:
            sc = 1.0
        nw = max(1, int(w * sc))
        nh = max(1, int(h * sc))
        return img.resize((nw, nh), RESAMPLE_LANCZOS)

    def refresh(self):
        pdf_path = self.app.var_pdf.get().strip()
        if not pdf_path or not os.path.exists(pdf_path):
            messagebox.showwarning(APP_NAME, "先にPDFを選択してください。")
            return

        page = int(self.var_page.get())
        page = max(1, min(self._page_max(), page))
        self.var_page.set(page)

        dpi = int(self.app.var_dpi.get())
        # FIXED: DEFAULT_POPPLER
        poppler_path = self.app.var_poppler.get().strip() or DEFAULT_POPPLER


        # 読み込み中表示
        self.var_status.set('読み込み中...')
        for cv in (self.canvas_a, self.canvas_b):
            cv.delete('all')
            w = max(240, cv.winfo_width())
            cv.create_text(10, 10, anchor='nw', fill='white', width=w-20, text='読み込み中...')
        self.update_idletasks()
        try:
            img = load_page_image(pdf_path, page, dpi, cache_dir=None, poppler_path=poppler_path)
        except Exception as e:
            msg = f"ページ画像の読み込みに失敗しました:\n{e}\n\npoppler_path: {poppler_path}"
            self.var_status.set("エラー")
            for cv in (self.canvas_a, self.canvas_b):
                cv.delete("all")
                w = max(240, cv.winfo_width())
                cv.create_text(10, 10, anchor="nw", fill="white", width=w-20, text=msg)
            messagebox.showerror(APP_NAME, msg)
            return

        # Prepare original with ROI overlay
        img_a = img.copy().convert("RGB")
        img_a = self._draw_roi_boxes(img_a, page)

        # Prepare processed (preview): keep scale=1.0 for responsiveness
        try:
            proc = preprocess_for_ocr(
                img.convert("RGB"),
                contrast=float(self.app.var_contrast.get()),
                threshold=int(self.app.var_threshold.get()),
                invert=bool(self.app.var_invert.get()),
                scale=1.0,
                binarize=True,
            ).convert("RGB")
        except Exception:
            # fallback: show grayscale
            proc = img.convert("L").convert("RGB")

        img_b = self._draw_roi_boxes(proc, page)

        # Fit to frames
        # estimate available size (rough)
        maxw, maxh = 620, 620
        img_a = self._fit(img_a, maxw, maxh)
        img_b = self._fit(img_b, maxw, maxh)
        self._tk_a = ImageTk.PhotoImage(img_a)
        self._tk_b = ImageTk.PhotoImage(img_b)

        # ttk.Label だと環境によって画像が表示されない事があるため、Canvas に描画する
        self.canvas_a.delete("all")
        self.canvas_b.delete("all")
        self.canvas_a.config(width=img_a.size[0], height=img_a.size[1])
        self.canvas_b.config(width=img_b.size[0], height=img_b.size[1])
        self.canvas_a.create_image(0, 0, anchor="nw", image=self._tk_a)
        self.canvas_b.create_image(0, 0, anchor="nw", image=self._tk_b)

        opening = self.app.var_opening.get()
        is_odd = (page % 2 == 1)
        use_right = is_odd if opening == "left" else (not is_odd)
        used = "right" if use_right else "left"
        self.var_info.set(
            f"ページ {page}（DPI={dpi}） / 開き方向={opening} / このページで使用されるROI={used} / しきい値={int(self.app.var_threshold.get())} / コントラスト={float(self.app.var_contrast.get()):.2f} / 反転={bool(self.app.var_invert.get())}"
        )

# -----------------------------
# Main App
# -----------------------------
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(f"{APP_NAME} v{APP_VERSION}")
        self.geometry("1480x860")
        self.minsize(1180, 700)

        self.cfg = load_config()
        self.results: List[PageCheckResult] = []
        self.cache_dir: Optional[str] = None
        self.pdf_id: Optional[str] = None
        self.total_pages = 0

        self.q = queue.Queue()
        self.worker: Optional[threading.Thread] = None
        self.stop_flag = threading.Event()

        self._build_ui()
        self._apply_cfg_to_ui()

        self.after(120, self._poll_queue)
        self.protocol("WM_DELETE_WINDOW", self.on_close)

    def _build_ui(self):
        top = ttk.Frame(self)
        top.pack(side="top", fill="x", padx=10, pady=8)

        # PDF
        self.var_pdf = tk.StringVar()
        ttk.Label(top, text="PDF:").grid(row=0, column=0, sticky="w")
        self.ent_pdf = ttk.Entry(top, textvariable=self.var_pdf, width=64)
        self.ent_pdf.grid(row=0, column=1, sticky="we", padx=6)
        ttk.Button(top, text="参照", command=self.browse_pdf).grid(row=0, column=2, padx=4)

        # Poppler
        self.var_poppler = tk.StringVar(value=self.cfg.get("poppler_path", DEFAULT_POPPLER))
        ttk.Label(top, text="Poppler(bin):").grid(row=1, column=0, sticky="w")
        self.ent_poppler = ttk.Entry(top, textvariable=self.var_poppler, width=64)
        self.ent_poppler.grid(row=1, column=1, sticky="we", padx=6)
        ttk.Button(top, text="参照", command=self.browse_poppler).grid(row=1, column=2, padx=4)

        # Tesseract
        self.var_tess = tk.StringVar(value=self.cfg.get("tesseract_cmd", DEFAULT_TESSERACT))
        ttk.Label(top, text="tesseract.exe:").grid(row=2, column=0, sticky="w")
        self.ent_tess = ttk.Entry(top, textvariable=self.var_tess, width=64)
        self.ent_tess.grid(row=2, column=1, sticky="we", padx=6)
        ttk.Button(top, text="参照", command=self.browse_tesseract).grid(row=2, column=2, padx=4)

        # DPI
        self.var_dpi = tk.IntVar(value=int(self.cfg.get("dpi", 250)))
        ttk.Label(top, text="DPI:").grid(row=0, column=3, sticky="e", padx=(16, 4))
        make_spinbox(top, from_=100, to=600, increment=25, textvariable=self.var_dpi, width=7).grid(row=0, column=4, sticky="w")

        # Opening direction
        self.var_opening = tk.StringVar(value=self.cfg.get("opening", "left"))
        frm_open = ttk.LabelFrame(top, text="開き方向")
        frm_open.grid(row=1, column=3, columnspan=2, rowspan=2, sticky="nsew", padx=(16, 4))
        ttk.Radiobutton(frm_open, text="左開き（横書き）", variable=self.var_opening, value="left").pack(anchor="w")
        ttk.Radiobutton(frm_open, text="右開き（縦書き）", variable=self.var_opening, value="right").pack(anchor="w")

        # Language selector
        self.var_lang = tk.StringVar(value=self.cfg.get("tess_lang", "auto"))
        frm_lang = ttk.LabelFrame(top, text="OCR言語")
        frm_lang.grid(row=0, column=5, rowspan=3, sticky="nsew", padx=(10, 0))
        self.cmb_lang = ttk.Combobox(frm_lang, textvariable=self.var_lang, width=12, state="readonly")
        self.cmb_lang.pack(anchor="w", padx=8, pady=(6, 6))

        # ROI line
        roi = ttk.Frame(top)
        roi.grid(row=3, column=0, columnspan=6, sticky="we", pady=(8, 2))
        ttk.Button(roi, text="ROI設定（左）", command=lambda: self.edit_roi("left")).pack(side="left", padx=4)
        ttk.Button(roi, text="ROI設定（右）", command=lambda: self.edit_roi("right")).pack(side="left", padx=4)

        self.var_roi_page = tk.IntVar(value=int(self.cfg.get("roi_test_page", DEFAULT_ROI_TEST_PAGE)))
        ttk.Label(roi, text="テストページ:").pack(side="left", padx=(16, 4))
        make_spinbox(roi, from_=1, to=99999, textvariable=self.var_roi_page, width=7).pack(side="left")

        # OCR params
        params = ttk.LabelFrame(top, text="OCR前処理パラメータ")
        params.grid(row=4, column=0, columnspan=6, sticky="we", pady=(6, 2))
        params.columnconfigure(1, weight=1)

        self.var_contrast = tk.DoubleVar(value=float(self.cfg.get("contrast", 2.0)))
        ttk.Label(params, text="コントラスト:").grid(row=0, column=0, sticky="w", padx=6, pady=2)
        self.sld_contrast = ttk.Scale(params, from_=0.5, to=4.0, variable=self.var_contrast, orient="horizontal")
        self.sld_contrast.grid(row=0, column=1, sticky="we", padx=6)
        self.lbl_contrast = ttk.Label(params, text="")
        self.lbl_contrast.grid(row=0, column=2, sticky="e", padx=6)

        self.var_threshold = tk.IntVar(value=int(self.cfg.get("threshold", 170)))
        ttk.Label(params, text="二値化しきい値:").grid(row=1, column=0, sticky="w", padx=6, pady=2)
        self.sld_threshold = ttk.Scale(params, from_=0, to=255, variable=self.var_threshold, orient="horizontal")
        self.sld_threshold.grid(row=1, column=1, sticky="we", padx=6)
        self.lbl_threshold = ttk.Label(params, text="")
        self.lbl_threshold.grid(row=1, column=2, sticky="e", padx=6)

        self.var_invert = tk.BooleanVar(value=bool(self.cfg.get("invert", False)))
        ttk.Checkbutton(params, text="白黒反転（※内部でON/OFFも試行）", variable=self.var_invert).grid(row=0, column=3, sticky="w", padx=10)

        self.var_try_rotate = tk.BooleanVar(value=bool(self.cfg.get("try_rotate", True)))
        ttk.Checkbutton(params, text="回転も試す(180/90/270)", variable=self.var_try_rotate).grid(row=1, column=3, sticky="w", padx=10)

        self.var_roman = tk.BooleanVar(value=bool(self.cfg.get("roman_enabled", True)))
        ttk.Checkbutton(params, text="ローマ数字を許可", variable=self.var_roman).grid(row=0, column=4, sticky="w", padx=10)

        self.var_pad = tk.DoubleVar(value=float(self.cfg.get("roi_padding_pct", 0.01)))
        ttk.Label(params, text="ROI余白(%):").grid(row=1, column=4, sticky="e", padx=6)
        make_spinbox(params, from_=0.0, to=0.05, increment=0.0025, textvariable=self.var_pad, width=8).grid(row=1, column=5, sticky="w", padx=6)

        opt = ttk.Frame(top)
        opt.grid(row=5, column=0, columnspan=6, sticky="we", pady=(6, 0))
        self.var_cache = tk.BooleanVar(value=bool(self.cfg.get("cache_enabled", True)))
        ttk.Checkbutton(opt, text="画像キャッシュを使う（再OCR高速化）", variable=self.var_cache).pack(side="left", padx=4)
        self.var_preview_pp = tk.BooleanVar(value=bool(self.cfg.get("preview_preprocessed", True)))
        ttk.Checkbutton(opt, text="プレビューは前処理後", variable=self.var_preview_pp).pack(side="left", padx=12)
        ttk.Button(opt, text="キャッシュ削除", command=self.clear_cache).pack(side="right", padx=4)

        act = ttk.Frame(top)
        act.grid(row=6, column=0, columnspan=6, sticky="we", pady=(8, 0))
        ttk.Button(act, text="解析開始", command=self.start_analysis).pack(side="left", padx=4)
        ttk.Button(act, text="中止", command=self.stop_analysis).pack(side="left", padx=4)
        ttk.Button(act, text="再OCR（パラメータ反映）", command=self.reocr).pack(side="left", padx=14)
        ttk.Button(act, text="CSV保存", command=self.export_csv).pack(side="left", padx=4)
        ttk.Button(act, text="画質プレビュー", command=self.show_quality_preview).pack(side="right", padx=4)
        ttk.Button(act, text="使い方", command=self.show_help).pack(side="right", padx=4)
        self.var_filter = tk.StringVar(value="all")
        ttk.Label(act, text="表示:").pack(side="left", padx=(18, 4))
        ttk.Combobox(act, textvariable=self.var_filter, values=["all", "suspicious"], width=12, state="readonly").pack(side="left")
        ttk.Button(act, text="更新", command=self.refresh_table).pack(side="left", padx=4)

        self.var_status = tk.StringVar(value="準備完了")
        ttk.Label(top, textvariable=self.var_status).grid(row=7, column=0, columnspan=6, sticky="w", pady=(6, 0))

        self.prog = ttk.Progressbar(top, orient="horizontal", mode="determinate")
        self.prog.grid(row=8, column=0, columnspan=6, sticky="we", pady=(4, 0))

        top.columnconfigure(1, weight=1)

        # Main panes
        paned = ttk.PanedWindow(self, orient="horizontal")
        paned.pack(side="top", fill="both", expand=True, padx=10, pady=10)

        left = ttk.Frame(paned)
        right = ttk.Frame(paned)
        paned.add(left, weight=3)
        paned.add(right, weight=4)  # ROI preview wider

        # Table
        cols = ("pdf_page", "detected", "type", "severity", "reason")
        self.tree = ttk.Treeview(left, columns=cols, show="headings", height=18)
        for c, t in [("pdf_page","PDFページ"), ("detected","検出"), ("type","形式"), ("severity","重大度"), ("reason","理由")]:
            self.tree.heading(c, text=t)

        self.tree.column("pdf_page", width=80, anchor="center")
        self.tree.column("detected", width=90, anchor="center")
        self.tree.column("type", width=70, anchor="center")
        self.tree.column("severity", width=70, anchor="center")
        self.tree.column("reason", width=600, anchor="w")

        ysb = ttk.Scrollbar(left, orient="vertical", command=self.tree.yview)
        xsb = ttk.Scrollbar(left, orient="horizontal", command=self.tree.xview)
        self.tree.configure(yscroll=ysb.set, xscroll=xsb.set)

        self.tree.grid(row=0, column=0, sticky="nsew")
        ysb.grid(row=0, column=1, sticky="ns")
        xsb.grid(row=1, column=0, sticky="we")

        left.rowconfigure(0, weight=1)
        left.columnconfigure(0, weight=1)

        self.tree.bind("<<TreeviewSelect>>", self.on_select_row)
        self.tree.bind("<Double-1>", self.on_double_click)

        # Preview
        prv = ttk.LabelFrame(right, text="ROIプレビュー（拡大）")
        prv.pack(side="top", fill="both", expand=True)

        self.lbl_preview = ttk.Label(prv)
        self.lbl_preview.pack(side="top", fill="both", expand=True, padx=8, pady=8)

        infof = ttk.Frame(right)
        infof.pack(side="top", fill="x", pady=(8, 0))
        self.var_preview_info = tk.StringVar(value="")
        ttk.Label(infof, textvariable=self.var_preview_info).pack(side="left")

        self._update_param_labels()
        self.sld_contrast.configure(command=lambda e: self._update_param_labels())
        self.sld_threshold.configure(command=lambda e: self._update_param_labels())

        self._refresh_lang_choices()

    def _refresh_lang_choices(self):
        langs = get_available_langs(self.var_tess.get().strip() or DEFAULT_TESSERACT)
        choices = ["auto"]
        if "eng" in langs:
            choices.append("eng")
        if "jpn" in langs:
            choices.append("jpn")
        if "eng" in langs and "jpn" in langs:
            choices.append("eng+jpn")
        if len(choices) == 1:
            choices = ["auto", "eng", "jpn", "eng+jpn"]
        self.cmb_lang["values"] = choices
        if self.var_lang.get() not in choices:
            self.var_lang.set("auto")

    def _update_param_labels(self):
        self.lbl_contrast.config(text=f"{self.var_contrast.get():.2f}")
        self.lbl_threshold.config(text=f"{int(self.var_threshold.get())}")

    def _apply_cfg_to_ui(self):
        self.var_pdf.set(self.cfg.get("last_pdf_path", ""))
        self.var_poppler.set(self.cfg.get("poppler_path", DEFAULT_POPPLER))
        self.var_tess.set(self.cfg.get("tesseract_cmd", DEFAULT_TESSERACT))
        self.var_lang.set(self.cfg.get("tess_lang", "auto"))
        self.var_dpi.set(int(self.cfg.get("dpi", 250)))
        self.var_opening.set(self.cfg.get("opening", "left"))
        self.var_roi_page.set(int(self.cfg.get("roi_test_page", DEFAULT_ROI_TEST_PAGE)))
        self.var_contrast.set(float(self.cfg.get("contrast", 2.0)))
        self.var_threshold.set(int(self.cfg.get("threshold", 170)))
        self.var_invert.set(bool(self.cfg.get("invert", False)))
        self.var_try_rotate.set(bool(self.cfg.get("try_rotate", True)))
        self.var_cache.set(bool(self.cfg.get("cache_enabled", True)))
        self.var_preview_pp.set(bool(self.cfg.get("preview_preprocessed", True)))
        self.var_pad.set(float(self.cfg.get("roi_padding_pct", 0.01)))
        self.var_roman.set(bool(self.cfg.get("roman_enabled", True)))
        self._update_param_labels()

    def _ui_to_cfg(self):
        self.cfg["last_pdf_path"] = self.var_pdf.get().strip()
        self.cfg["dpi"] = int(self.var_dpi.get())
        self.cfg["opening"] = self.var_opening.get()
        self.cfg["contrast"] = float(self.var_contrast.get())
        self.cfg["threshold"] = int(self.var_threshold.get())
        self.cfg["invert"] = bool(self.var_invert.get())
        self.cfg["try_rotate"] = bool(self.var_try_rotate.get())
        self.cfg["cache_enabled"] = bool(self.var_cache.get())
        self.cfg["preview_preprocessed"] = bool(self.var_preview_pp.get())
        self.cfg["roi_padding_pct"] = float(self.var_pad.get())
        self.cfg["roman_enabled"] = bool(self.var_roman.get())
        self.cfg["roi_test_page"] = int(self.var_roi_page.get())
        self.cfg["tess_lang"] = self.var_lang.get()
        self.cfg["poppler_path"] = self.var_poppler.get().strip()
        self.cfg["tesseract_cmd"] = self.var_tess.get().strip()

    # ---- Browse ----
    def browse_pdf(self):
        path = filedialog.askopenfilename(title="PDFを選択", filetypes=[("PDF files", "*.pdf"), ("All files", "*.*")])
        if path:
            self.var_pdf.set(path)

    def browse_poppler(self):
        path = filedialog.askdirectory(title="Poppler(bin) フォルダを選択")
        if path:
            self.var_poppler.set(path.strip())

    def browse_tesseract(self):
        path = filedialog.askopenfilename(
            title="tesseract.exe を選択",
            filetypes=[("tesseract.exe", "tesseract.exe"), ("EXE files", "*.exe"), ("All files", "*.*")]
        )
        if path:
            self.var_tess.set(path.strip())
            self._refresh_lang_choices()

    # ---- ROI page selection ----
    def _pick_roi_preview_page(self, pdf_path: str, base_page: int, side: str, opening: str) -> int:
        total = pdf_page_count(pdf_path, poppler_path=self.var_poppler.get().strip())
        page = max(1, min(total, int(base_page)))

        # For visual check: pick a page whose parity matches the intended side in a spread.
        # left-open: odd pages are "right page", even pages are "left page"
        if side == "right":
            want_odd = True if opening == "left" else False
        else:
            want_odd = False if opening == "left" else True

        if (page % 2 == 1) != want_odd:
            if page + 1 <= total:
                page += 1
            elif page - 1 >= 1:
                page -= 1
        return page

    def edit_roi(self, side: str):
        self._ui_to_cfg()
        pdf_path = self.var_pdf.get().strip()
        if not pdf_path or not os.path.exists(pdf_path):
            messagebox.showwarning(APP_NAME, "先にPDFを選択してください。")
            return

        dpi = int(self.var_dpi.get())
        base_page = int(self.var_roi_page.get())
        opening = self.var_opening.get()

        try:
            page = self._pick_roi_preview_page(pdf_path, base_page, side=side, opening=opening)
            img = load_page_image(
                pdf_path,
                page,
                dpi,
                cache_dir=None,
                poppler_path=self.var_poppler.get().strip(),
            )
        except Exception as e:
            messagebox.showerror(APP_NAME, f"ページ画像の読み込みに失敗しました:\n{e}")
            return

        init = tuple(self.cfg["roi_left"] if side == "left" else self.cfg["roi_right"])
        title = f"ROI設定（{'左' if side=='left' else '右'}） - 確認ページ {page}"
        editor = ROIEditor(self, title, img, init_roi=init)
        self.wait_window(editor)

        if editor.result_roi:
            if side == "left":
                self.cfg["roi_left"] = list(editor.result_roi)
            else:
                self.cfg["roi_right"] = list(editor.result_roi)
            # ROI is kept only for this session (not persisted).
            messagebox.showinfo(APP_NAME, "ROIを設定しました（この起動中のみ有効）。\n※確定は「決定(Enter)」でのみ行われます。")
        else:
            self.var_status.set("ROI変更はキャンセルされました。")

    # ---- Analysis ----
    def validate_ready(self) -> bool:
        pdf_path = self.var_pdf.get().strip()
        if not pdf_path or not os.path.exists(pdf_path):
            messagebox.showwarning(APP_NAME, "PDFファイルを指定してください。")
            return False

        poppler_path = self.var_poppler.get().strip()
        tesseract_cmd = self.var_tess.get().strip()

        if not poppler_path or not os.path.isdir(poppler_path):
            messagebox.showerror(APP_NAME, f"Poppler(bin) が見つかりません:\n{poppler_path or '(未設定)'}")
            return False
        if not tesseract_cmd or not os.path.exists(tesseract_cmd):
            messagebox.showerror(APP_NAME, f"tesseract.exe が見つかりません:\n{tesseract_cmd or '(未設定)'}")
            return False
        _set_tesseract_cmd(tesseract_cmd)
        return True

    def start_analysis(self):
        if self.worker and self.worker.is_alive():
            messagebox.showinfo(APP_NAME, "解析中です。")
            return
        if not self.validate_ready():
            return

        self._ui_to_cfg()
        save_config(self.cfg)

        self.stop_flag.clear()
        self.var_status.set("解析準備中...")
        self.prog["value"] = 0
        self.tree.delete(*self.tree.get_children())
        self.results = []
        self._clear_preview()

        pdf_path = self.var_pdf.get().strip()
        try:
            self.pdf_id = compute_pdf_id(pdf_path)
        except Exception as e:
            log_write("compute_pdf_id failed: " + repr(e))
            self.pdf_id = None

        self.cache_dir = get_cache_dir(self.pdf_id) if (self.cfg.get("cache_enabled", True) and self.pdf_id) else None

        self.worker = threading.Thread(target=self._worker_analyze, daemon=True)
        self.worker.start()

    def stop_analysis(self):
        self.stop_flag.set()
        self.var_status.set("中止要求を送信しました...")

    def reocr(self):
        if self.worker and self.worker.is_alive():
            messagebox.showinfo(APP_NAME, "解析中です。")
            return
        if not self.validate_ready():
            return

        self._ui_to_cfg()
        save_config(self.cfg)

        if not self.results:
            self.start_analysis()
            return
        if not self.cache_dir or not os.path.isdir(self.cache_dir):
            messagebox.showinfo(APP_NAME, "キャッシュがありません。通常解析を行います。")
            self.start_analysis()
            return

        self.stop_flag.clear()
        self.var_status.set("再OCR中...")
        self.prog["value"] = 0
        self.worker = threading.Thread(target=self._worker_reocr, daemon=True)
        self.worker.start()

    def _judge(self, prev_type, prev_val, cur_type, cur_val, ok: bool) -> Tuple[str, str]:
        if not ok or cur_type == "none" or cur_val is None:
            return ("未検出（OCR失敗）", "NG")
        if prev_val is None or prev_type is None:
            return ("OK（開始）", "OK")
        if cur_type != prev_type:
            return (f"形式変更（{prev_type}→{cur_type}）", "WARN")
        if cur_val == prev_val:
            return (f"重複の疑い（前={prev_val}）", "WARN")
        if cur_val == prev_val + 1:
            return ("OK", "OK")
        if cur_val > prev_val + 1:
            return (f"飛び番号の疑い（前={prev_val} 期待={prev_val+1}）", "WARN")
        if cur_val < prev_val:
            return (f"逆転の疑い（前={prev_val}）", "NG")
        return ("要確認", "WARN")

    def _worker_analyze(self):
        try:
            pdf_path = self.cfg["last_pdf_path"]
            dpi = int(self.cfg["dpi"])
            poppler_path = self.cfg.get("poppler_path", DEFAULT_POPPLER)
            tesseract_cmd = self.cfg.get("tesseract_cmd", DEFAULT_TESSERACT)

            total = pdf_page_count(pdf_path, poppler_path=poppler_path)
            self.total_pages = total
            self.q.put(("total", total))

            if self.cache_dir:
                os.makedirs(self.cache_dir, exist_ok=True)

            results: List[PageCheckResult] = []
            prev_type = None
            prev_val = None

            roi_left = expand_roi(tuple(self.cfg["roi_left"]), float(self.cfg.get("roi_padding_pct", 0.01)))
            roi_right = expand_roi(tuple(self.cfg["roi_right"]), float(self.cfg.get("roi_padding_pct", 0.01)))

            opening = self.cfg["opening"]
            contrast = float(self.cfg["contrast"])
            threshold = int(self.cfg["threshold"])
            invert = bool(self.cfg["invert"])
            try_rotate = bool(self.cfg["try_rotate"])
            roman_enabled = bool(self.cfg.get("roman_enabled", True))

            langs = get_available_langs(tesseract_cmd)
            lang = resolve_lang(self.cfg.get("tess_lang", "auto"), langs)

            for p in range(1, total + 1):
                if self.stop_flag.is_set():
                    break

                is_odd = (p % 2 == 1)
                use_right = is_odd if opening == "left" else (not is_odd)
                roi = roi_right if use_right else roi_left
                roi_name = "right" if use_right else "left"

                img = load_page_image(pdf_path, p, dpi, cache_dir=self.cache_dir, poppler_path=poppler_path)
                w, h = img.size
                box = roi_to_px(roi, w, h)
                x1, y1, x2, y2 = box
                roi_img = img.crop((x1, y1, x2, y2))

                ocr = ocr_extract_value(
                    roi_img,
                    tesseract_cmd=tesseract_cmd,
                    contrast=contrast,
                    threshold=threshold,
                    invert_user=invert,
                    try_rotate=try_rotate,
                    roman_enabled=roman_enabled,
                    lang=lang,
                )

                detected = ocr.value_str if ocr.ok else ""
                dtype = ocr.value_type if ocr.ok else "none"
                dint = ocr.value_int if ocr.ok else None

                reason, sev = self._judge(prev_type, prev_val, dtype, dint, ocr.ok)
                if ocr.ok:
                    prev_type, prev_val = dtype, dint

                res = PageCheckResult(
                    pdf_page=p,
                    used_roi=roi_name,
                    detected=detected,
                    detected_type=dtype,
                    detected_int=dint,
                    reason=reason,
                    severity=sev,
                    raw_text=ocr.raw_text + (f"\n\n[detail] {ocr.detail}" if ocr.raw_text else f"[detail] {ocr.detail}"),
                    rotation_used=ocr.rotation_used,
                    roi_box_px=box,
                )
                results.append(res)

                self.q.put(("progress", p, total))
                self.q.put(("row", res))

            self.q.put(("done", results, "", self.stop_flag.is_set()))
        except Exception:
            self.q.put(("error", traceback.format_exc()))
            log_write(traceback.format_exc())

    def _worker_reocr(self):
        try:
            pdf_path = self.cfg["last_pdf_path"]
            dpi = int(self.cfg["dpi"])
            poppler_path = self.cfg.get("poppler_path", DEFAULT_POPPLER)
            tesseract_cmd = self.cfg.get("tesseract_cmd", DEFAULT_TESSERACT)

            total = self.total_pages or pdf_page_count(pdf_path, poppler_path=poppler_path)
            self.q.put(("total", total))

            results: List[PageCheckResult] = []
            prev_type = None
            prev_val = None

            roi_left = expand_roi(tuple(self.cfg["roi_left"]), float(self.cfg.get("roi_padding_pct", 0.01)))
            roi_right = expand_roi(tuple(self.cfg["roi_right"]), float(self.cfg.get("roi_padding_pct", 0.01)))

            opening = self.cfg["opening"]
            contrast = float(self.cfg["contrast"])
            threshold = int(self.cfg["threshold"])
            invert = bool(self.cfg["invert"])
            try_rotate = bool(self.cfg["try_rotate"])
            roman_enabled = bool(self.cfg.get("roman_enabled", True))

            langs = get_available_langs(tesseract_cmd)
            lang = resolve_lang(self.cfg.get("tess_lang", "auto"), langs)

            self.q.put(("clear_table", None))

            for p in range(1, total + 1):
                if self.stop_flag.is_set():
                    break

                is_odd = (p % 2 == 1)
                use_right = is_odd if opening == "left" else (not is_odd)
                roi = roi_right if use_right else roi_left
                roi_name = "right" if use_right else "left"

                img = load_page_image(pdf_path, p, dpi, cache_dir=self.cache_dir, poppler_path=poppler_path)
                w, h = img.size
                box = roi_to_px(roi, w, h)
                x1, y1, x2, y2 = box
                roi_img = img.crop((x1, y1, x2, y2))

                ocr = ocr_extract_value(
                    roi_img,
                    tesseract_cmd=tesseract_cmd,
                    contrast=contrast,
                    threshold=threshold,
                    invert_user=invert,
                    try_rotate=try_rotate,
                    roman_enabled=roman_enabled,
                    lang=lang,
                )

                detected = ocr.value_str if ocr.ok else ""
                dtype = ocr.value_type if ocr.ok else "none"
                dint = ocr.value_int if ocr.ok else None

                reason, sev = self._judge(prev_type, prev_val, dtype, dint, ocr.ok)
                if ocr.ok:
                    prev_type, prev_val = dtype, dint

                res = PageCheckResult(
                    pdf_page=p,
                    used_roi=roi_name,
                    detected=detected,
                    detected_type=dtype,
                    detected_int=dint,
                    reason=reason,
                    severity=sev,
                    raw_text=ocr.raw_text + (f"\n\n[detail] {ocr.detail}" if ocr.raw_text else f"[detail] {ocr.detail}"),
                    rotation_used=ocr.rotation_used,
                    roi_box_px=box,
                )
                results.append(res)

                self.q.put(("progress", p, total))
                self.q.put(("row", res))

            self.q.put(("done", results, "", self.stop_flag.is_set()))
        except Exception:
            self.q.put(("error", traceback.format_exc()))
            log_write(traceback.format_exc())

    # ---- Table / Preview ----
    def refresh_table(self):
        self.tree.delete(*self.tree.get_children())
        mode = self.var_filter.get()
        for r in self.results:
            if mode == "suspicious" and r.severity == "OK":
                continue
            self._insert_row(r)

    def _insert_row(self, r: PageCheckResult):
        tags = ()
        if r.severity == "NG":
            tags = ("ng",)
        elif r.severity == "WARN":
            tags = ("warn",)
        iid = str(r.pdf_page)
        self.tree.insert("", "end", iid=iid, values=(r.pdf_page, r.detected, r.detected_type, r.severity, r.reason), tags=tags)
        self.tree.tag_configure("ng", background="#ffe5e5")
        self.tree.tag_configure("warn", background="#fff6d6")

    def on_select_row(self, event=None):
        sel = self.tree.selection()
        if not sel:
            return
        page = int(sel[0])
        r = next((x for x in self.results if x.pdf_page == page), None)
        if r:
            self.show_preview(r)


    def on_double_click(self, event=None):
        sel = self.tree.selection()
        if not sel:
            return
        page = int(sel[0])
        self.open_page_viewer(page)

    # ---- Full page viewer (double-click) ----
    def open_page_viewer(self, page: int):
        """結果一覧のページをダブルクリックすると、当該PDFページ全体を子ウインドウで表示します。"""
        pdf_path = self.var_pdf.get().strip()
        if not pdf_path or not os.path.exists(pdf_path):
            return

        dpi = int(self.var_dpi.get())
        try:
            # FIXED: DEFAULT_POPPLER
            img = load_page_image(pdf_path, page, dpi, cache_dir=self.cache_dir, poppler_path=self.cfg.get('poppler_path', DEFAULT_POPPLER))
        except Exception as e:
            messagebox.showerror(APP_NAME, f"ページ画像の読み込みに失敗しました:\n{e}")
            return

        win = tk.Toplevel(self)
        win.title(f"PDFページ {page}")
        try:
            sw = self.winfo_screenwidth()
            sh = self.winfo_screenheight()
            w = min(1200, int(sw * 0.85))
            h = min(900, int(sh * 0.85))
            win.geometry(f"{w}x{h}")
        except Exception:
            win.geometry("1100x850")
        win.minsize(700, 500)

        top = ttk.Frame(win)
        top.pack(side="top", fill="x", padx=10, pady=8)

        ttk.Label(top, text=f"ページ: {page} / DPI: {dpi}").pack(side="left")

        zoom_var = tk.IntVar(value=100)

        frame = ttk.Frame(win)
        frame.pack(side="top", fill="both", expand=True, padx=10, pady=(0, 10))
        frame.rowconfigure(0, weight=1)
        frame.columnconfigure(0, weight=1)

        canvas = tk.Canvas(frame, bg="black", highlightthickness=0)
        vbar = ttk.Scrollbar(frame, orient="vertical", command=canvas.yview)
        hbar = ttk.Scrollbar(frame, orient="horizontal", command=canvas.xview)
        canvas.configure(yscrollcommand=vbar.set, xscrollcommand=hbar.set)

        canvas.grid(row=0, column=0, sticky="nsew")
        vbar.grid(row=0, column=1, sticky="ns")
        hbar.grid(row=1, column=0, sticky="we")

        def render():
            z = max(10, min(300, int(zoom_var.get())))
            scale = z / 100.0
            nw = max(1, int(img.size[0] * scale))
            nh = max(1, int(img.size[1] * scale))
            disp = img.resize((nw, nh), RESAMPLE_LANCZOS)
            tkimg = ImageTk.PhotoImage(disp)
            canvas.delete("all")
            canvas.create_image(0, 0, anchor="nw", image=tkimg)
            canvas.config(scrollregion=(0, 0, nw, nh))
            canvas._tkimg = tkimg  # keep ref

        def fit():
            win.update_idletasks()
            cw = max(100, canvas.winfo_width())
            ch = max(100, canvas.winfo_height())
            scale = min(cw / img.size[0], ch / img.size[1])
            z = int(max(10, min(300, scale * 100)))
            zoom_var.set(z)
            render()

        ttk.Label(top, text="ズーム:").pack(side="left", padx=(16, 6))
        sld = ttk.Scale(top, from_=10, to=300, orient="horizontal", variable=zoom_var, command=lambda e: render())
        sld.pack(side="left", fill="x", expand=True)
        ttk.Label(top, textvariable=zoom_var, width=5).pack(side="left", padx=(6, 0))
        ttk.Label(top, text="%").pack(side="left")

        ttk.Button(top, text="フィット", command=fit).pack(side="right")
        ttk.Button(top, text="100%", command=lambda: (zoom_var.set(100), render())).pack(side="right", padx=(0, 8))

        def _on_mousewheel(evt):
            try:
                canvas.yview_scroll(int(-1 * (evt.delta / 120)), "units")
            except Exception:
                pass

        canvas.bind("<Enter>", lambda e: canvas.bind_all("<MouseWheel>", _on_mousewheel))
        canvas.bind("<Leave>", lambda e: canvas.unbind_all("<MouseWheel>"))

        render()
        win.after(150, fit)

    def _clear_preview(self):
        self.lbl_preview.config(image="")
        self.lbl_preview.image = None
        self.var_preview_info.set("")

    def show_preview(self, r: PageCheckResult):
        pdf_path = self.var_pdf.get().strip()
        if not pdf_path or not os.path.exists(pdf_path):
            return
        dpi = int(self.var_dpi.get())
        try:
            img = load_page_image(
                pdf_path,
                r.pdf_page,
                dpi,
                cache_dir=self.cache_dir,
                poppler_path=self.var_poppler.get().strip(),
            )
        except Exception as e:
            self.var_preview_info.set(f"プレビュー失敗: {e}")
            return

        x1, y1, x2, y2 = r.roi_box_px
        roi = img.crop((x1, y1, x2, y2))

        if self.var_preview_pp.get():
            roi = preprocess_for_ocr(
                roi,
                contrast=float(self.var_contrast.get()),
                threshold=int(self.var_threshold.get()),
                invert=bool(self.var_invert.get()),
                scale=3.0,
                binarize=True,
            )

        # Enlarged preview bounds
        maxw, maxh = 392, 288
        rw, rh = roi.size
        scale = min(maxw / max(rw, 1), maxh / max(rh, 1))
        if scale > 1.0:
            roi = roi.resize((int(rw * scale), int(rh * scale)), RESAMPLE_NEAREST)
        else:
            roi = roi.resize((max(1, int(rw * scale)), max(1, int(rh * scale))), RESAMPLE_LANCZOS)

        tkimg = ImageTk.PhotoImage(roi)
        self.lbl_preview.config(image=tkimg)
        self.lbl_preview.image = tkimg
        self.var_preview_info.set(
            f"PDFページ={r.pdf_page} / ROI={r.used_roi} / 検出={r.detected or '---'} / {r.severity} / {r.reason}"
        )

    # ---- CSV ----
    def export_csv(self):
        if not self.results:
            messagebox.showinfo(APP_NAME, "結果がありません。解析後に実行してください。")
            return
        out_path = filedialog.asksaveasfilename(title="CSV保存", defaultextension=".csv", filetypes=[("CSV", "*.csv")])
        if not out_path:
            return
        try:
            import csv
            with open(out_path, "w", encoding="utf-8-sig", newline="") as f:
                w = csv.writer(f)
                w.writerow(["pdf_page", "used_roi", "detected", "detected_type", "detected_int", "severity", "reason", "rotation_used", "roi_box_px", "raw_text"])
                for r in self.results:
                    w.writerow([r.pdf_page, r.used_roi, r.detected, r.detected_type, r.detected_int, r.severity, r.reason, r.rotation_used, repr(r.roi_box_px), r.raw_text])
            messagebox.showinfo(APP_NAME, f"保存しました:\n{out_path}")
        except Exception as e:
            messagebox.showerror(APP_NAME, f"CSV保存に失敗:\n{e}")
            log_write("CSV export failed: " + repr(e))

    # ---- Cache ----
    def clear_cache(self):
        pdf_path = self.var_pdf.get().strip()
        if not pdf_path or not os.path.exists(pdf_path):
            messagebox.showwarning(APP_NAME, "PDFを選択してください。")
            return
        try:
            pdf_id = compute_pdf_id(pdf_path)
            cdir = get_cache_dir(pdf_id)
            if os.path.isdir(cdir):
                shutil.rmtree(cdir, ignore_errors=True)
            messagebox.showinfo(APP_NAME, "キャッシュを削除しました。")
        except Exception as e:
            messagebox.showerror(APP_NAME, f"キャッシュ削除に失敗:\n{e}")
            log_write("cache clear failed: " + repr(e))

    # ---- Help ----

    def show_quality_preview(self):
        """画質調整（前処理）の見た目をページ全体で確認する"""
        # 設定は現在のUI値を反映（ROI枠表示も設定値を参照するため）
        self._ui_to_cfg()
        save_config(self.cfg)

        try:
            if hasattr(self, "_quality_win") and self._quality_win is not None and self._quality_win.winfo_exists():
                self._quality_win.lift()
                self._quality_win.focus_set()
                self._quality_win.refresh()
                return
        except Exception:
            pass

        self._quality_win = QualityPreviewWindow(self)
        # モーダルにしない（メイン画面のスライダー調整→更新しやすくする）
        try:
            self._quality_win.transient(self)
        except Exception:
            pass

    def show_help(self):
        help_text = """\
【このツールでできること】
スキャンPDFのヘッダー/フッター付近にある「ページ番号（ノンブル）」をOCRで読み取り、
「飛び番号 / 逆転 / 重複 / 未検出」を一覧表示します。
右側には「実際にOCRした領域（ROI）」のプレビューを表示し、設定や画質調整の当たりを確認できます。

────────────────────────────────────
【最短の使い方（まず動かす）】
1) 「PDF: 参照」からPDFを選択
2) 必要なら「Poppler(bin)」「tesseract.exe」を参照ボタンで指定
   - 既定値は最初から入っています（環境に合わせて変更してください）
3) 開き方向（左開き/右開き）を選択
4) 「ROI設定（左）」「ROI設定（右）」で、ページ番号がある領域をドラッグ指定 → [決定]
   ※ROIは「この起動中のみ有効」です（次回起動時には既定値に戻ります）
5) 「解析開始」

────────────────────────────────────
【画質（前処理）調整の考え方：ここが最重要】
OCRは「ROIにページ番号が写っている」だけでは成功しません。
画像が薄い／背景が汚い／紙が黄ばんでいる／印刷がかすれている場合、
次の前処理パラメータの“組み合わせ”で読めるようになります。

■ 1) コントラスト（Contrast）
- 目的：文字と背景の差を強調する
- 典型症状：
  ・数字が薄い → コントラストを上げる（例：2.0 → 2.5〜3.5）
  ・背景のムラも強調される → 上げすぎ注意（ノイズが増える）

■ 2) 二値化しきい値（Threshold）
- 目的：白黒に分けて文字を残す（黒い文字を“残す”設定）
- 典型症状と調整：
  ・文字が消える（真っ白になる） → しきい値を下げる（170 → 150 → 130）
  ・背景ノイズが黒く残って読めない → しきい値を上げる（170 → 190 → 210）
- コツ：
  「読ませたい文字が黒で残り、背景が白に落ちる」ポイントを探します。

■ 3) 白黒反転（Invert）
- 目的：OCRが“黒文字/白背景”を前提にしているケースを救う
- 使う場面：
  ・白抜き文字（黒背景に白文字）っぽい見た目
  ・二値化後に文字が白くなってしまう
- 本ツールでは、チェックON/OFFどちらも内部で試しますが、
  「プレビューを見て明らかに逆」なら手動で切り替えると判断が早いです。

■ 4) DPI（解像度）
- 目的：ROI内の数字の“画素数”を増やして識別しやすくする
- 推奨：
  ・基本：250
  ・薄い/小さいノンブル：300〜400
  ・注意：上げるほど処理時間・メモリ使用量が増えます

■ 5) ROI余白（Padding）
- 目的：ROIの周囲に少し余白を足して取りこぼしを減らす
- 推奨：
  ・0.01（1%）〜0.03（3%）
  ・ROIがギリギリだと、微妙なズレで数字が欠けて失敗します

■ 6) 回転も試す（Rotate）
- 目的：逆さスキャン・左右回転の救済
- 使う場面：
  ・見た目で上下が逆、または一部ページだけ回転している
- 注意：
  試す回転が増えるほど処理は重くなります（必要なときだけON）

────────────────────────────────────
【画質を“目で確認”する方法】
1) 解析後、一覧の行をクリック → 右側「ROIプレビュー」で
   - “いまOCRしている領域”が適切か
   - 二値化後に数字が潰れていないか
   を確認します。
2) しきい値/コントラスト/反転を調整したら、「再OCR（パラメータ反映）」で再計算します。
   ※ROIは再設定しなくてもOK（同じ起動中は保持されます）

────────────────────────────────────
【ROI設定のコツ（失敗しやすいポイント）】
- “ページ番号だけ”をギリギリで囲まない（少し余裕を持たせる）
- ページ番号の位置が「上」「下」「外側」「内側」どこかを目視で確認し、
  左ページ用ROI・右ページ用ROIをそれぞれ設定する
- 奇数/偶数で左右が逆に感じる場合：
  「開き方向」を切り替えて再実行（左開き/右開き）

────────────────────────────────────
【CSV保存】
解析結果をCSVで保存します（監査や後工程での確認用）。

【注意】
- 本ツールは“画像としてノンブルが存在するスキャンPDF”向けです。
- OCR言語：
  ・英数字のノンブルなら eng で十分
  ・漢数字（例：三一）が多い場合は jpn があると安定します

"""
        win = tk.Toplevel(self)
        win.title("使い方")
        win.geometry("920x700")
        win.minsize(700, 480)

        txtw = scrolledtext.ScrolledText(win, wrap="word")
        txtw.pack(fill="both", expand=True, padx=10, pady=10)
        txtw.insert("1.0", help_text)
        txtw.configure(state="disabled")

        ttk.Button(win, text="閉じる", command=win.destroy).pack(pady=(0, 10))
        win.transient(self)
        win.grab_set()

    # ---- Queue polling ----
    def _poll_queue(self):
        try:
            while True:
                item = self.q.get_nowait()
                kind = item[0]
                if kind == "total":
                    total = int(item[1])
                    self.prog["maximum"] = total
                    self.prog["value"] = 0
                    self.var_status.set(f"解析開始: 全{total}ページ")
                elif kind == "progress":
                    cur, total = int(item[1]), int(item[2])
                    self.prog["value"] = cur
                    self.var_status.set(f"解析中: {cur}/{total}")
                elif kind == "row":
                    res: PageCheckResult = item[1]
                    self.results.append(res)
                    mode = self.var_filter.get()
                    if mode == "all" or (mode == "suspicious" and res.severity != "OK"):
                        self._insert_row(res)
                elif kind == "clear_table":
                    self.tree.delete(*self.tree.get_children())
                    self.results = []
                elif kind == "done":
                    results, hint, stopped = item[1], item[2], bool(item[3])
                    self.results = results
                    self.refresh_table()
                    self.prog["value"] = self.prog["maximum"]
                    self.var_status.set("中止しました。" if stopped else "完了。")
                    if hint:
                        messagebox.showwarning(APP_NAME, hint)
                elif kind == "error":
                    msg = item[1]
                    self.var_status.set("エラー")
                    messagebox.showerror(APP_NAME, msg)
        except queue.Empty:
            pass
        self.after(120, self._poll_queue)

    def on_close(self):
        self.stop_flag.set()
        self._ui_to_cfg()
        save_config(self.cfg)
        self.destroy()

# -----------------------------
# Startup checks
# -----------------------------
def _startup_preflight_or_exit():
    missing = []
    details = []
    if PIL_IMPORT_ERROR is not None or Image is None:
        missing.append("Pillow (pip install pillow)")
        details.append(f"Pillow import error: {PIL_IMPORT_ERROR!r}")
    if convert_from_path is None or pdfinfo_from_path is None:
        missing.append("pdf2image (pip install pdf2image)")
    if pytesseract is None:
        missing.append("pytesseract (pip install pytesseract)")

    if missing:
        msg = "起動に必要なライブラリが不足しています。\n\n" + "\n".join("- " + x for x in missing)
        if details:
            msg += "\n\n詳細:\n" + "\n".join(details[:3])
        try:
            root = tk.Tk()
            root.withdraw()
            messagebox.showerror(APP_NAME, msg)
            root.destroy()
        except Exception:
            print(msg)
        raise SystemExit(1)

def main():
    ensure_dirs()
    log_write(f"start app v{APP_VERSION}")
    _startup_preflight_or_exit()
    app = App()
    app.mainloop()

if __name__ == "__main__":
    try:
        main()
    except SystemExit:
        raise
    except Exception:
        err = traceback.format_exc()
        log_write("FATAL:\n" + err)
        try:
            root = tk.Tk()
            root.withdraw()
            messagebox.showerror(APP_NAME, err)
            root.destroy()
        except Exception:
            print(err, file=sys.stderr)
        raise