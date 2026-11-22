#!/usr/bin/env python3
"""Extract IUT I-IV paper text with page markers using pypdf (A1037)."""
import os, sys, glob
try:
    from pypdf import PdfReader
except Exception as e:
    print("pypdf import failed:", e)
    sys.exit(2)

RAW = r"D:/lean/papers/motizuki_corpus/raw"
OUT = r"D:/lean/coord/IUT-TEXT"
FILES = {
    "I": "Inter-universal Teichmuller Theory I.pdf",
    "II": "Inter-universal Teichmuller Theory II.pdf",
    "III": "Inter-universal Teichmuller Theory III.pdf",
    "IV": "Inter-universal Teichmuller Theory IV.pdf",
}
os.makedirs(OUT, exist_ok=True)
for key, name in FILES.items():
    path = os.path.join(RAW, name)
    if not os.path.exists(path):
        print("MISSING", path)
        continue
    reader = PdfReader(path)
    parts = []
    for i, page in enumerate(reader.pages, start=1):
        try:
            txt = page.extract_text() or ""
        except Exception as e:
            txt = ""
            print("page error", key, i, e)
        parts.append("\n===== PAGE %d =====\n" % i)
        parts.append(txt)
    out = os.path.join(OUT, key + ".txt")
    with open(out, "w", encoding="utf-8") as f:
        f.write("".join(parts))
    print(key, "pages", len(reader.pages), "chars", sum(len(p) for p in parts), "->", out)