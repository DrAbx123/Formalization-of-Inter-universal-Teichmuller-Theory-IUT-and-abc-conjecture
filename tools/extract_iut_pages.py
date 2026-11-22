#!/usr/bin/env python3
"""Extract selected IUT PDF pages (page-marker txt) into a markdown long file (A1039)."""
import re, os
BASE = r"D:/lean/coord/IUT-TEXT"
OUT = r"D:/lean/coord/IUT-TEXT-LONG.md"

def pages(path):
    txt = open(path, encoding="utf-8").read()
    parts = re.split(r"\n===== PAGE (\d+) =====\n", txt)
    d = {}
    for i in range(1, len(parts), 2):
        d[int(parts[i])] = parts[i+1]
    return d

III = pages(os.path.join(BASE, "III.txt"))
IV = pages(os.path.join(BASE, "IV.txt"))

sections = [
    ("IUT III - Theorem 3.11 and indeterminacies (pp. 150-160)", III, list(range(150,161))),
    ("IUT III - Corollary 3.12 proof, Steps (x)-(xi) (pp. 181-183)", III, [181,182,183]),
    ("IUT IV - Theorem 1.10 normalization (pp. 22-23)", IV, [22,23]),
    ("IUT IV - Theorem 1.10 proof, Steps (iv)-(v) (pp. 27-29)", IV, [27,28,29]),
]

lines = []
lines.append("# IUT-TEXT-LONG - verbatim page ranges from IUT III/IV (A1039)")
lines.append("")
lines.append("Source: `coord/IUT-TEXT/III.txt` and `coord/IUT-TEXT/IV.txt`, produced by")
lines.append("`tools/pdftotext_iut.py` (pypdf) from the IUT PDFs.  Each page block below is the")
lines.append("raw extracted text for that PDF page; line breaks/OCR artifacts are preserved.")
lines.append("")
lines.append("Page index:")
for title, _, ps in sections:
    lines.append("- " + title + ": " + ", ".join(str(p) for p in ps))
lines.append("")
for title, src, ps in sections:
    lines.append("## " + title)
    lines.append("")
    for p in ps:
        lines.append("### Page " + str(p))
        lines.append("")
        lines.append("```text")
        lines.append(src.get(p, "(page not found)").strip("\n"))
        lines.append("```")
        lines.append("")

open(OUT, "w", encoding="utf-8").write("\n".join(lines))
print("wrote", OUT, "chars", len("\n".join(lines)))