#!/usr/bin/env python3
"""Build coord/IUT-TEXT-N5.md: contiguous OCR pages + display line index (A1041)."""
import re, os
BASE = r"D:/lean/coord/IUT-TEXT"
OUT = r"D:/lean/coord/IUT-TEXT-N5.md"

def load(name):
    path = os.path.join(BASE, name)
    lines = open(path, encoding="utf-8").read().split("\n")
    pages = {}
    cur = None
    for i, l in enumerate(lines, start=1):
        m = re.match(r"^===== PAGE (\d+) =====$", l)
        if m:
            cur = int(m.group(1)); pages[cur] = []
        elif cur is not None:
            pages[cur].append((i, l))
    return pages

III = load("III.txt")
IV = load("IV.txt")

sections = [
    ("IUT III pp. 174-175: Cor 3.12 proof beginning, hull/union definitions", III, [174,175]),
    ("IUT III pp. 181-183: Cor 3.12 proof Step (x) and Step (xi-a/c/d)", III, [181,182,183]),
    ("IUT IV pp. 27-29: Theorem 1.10 proof Step (iv)-(v)", IV, [27,28,29]),
]

out = []
out.append("# IUT-TEXT-N5 - contiguous OCR excerpts for N5 (A1041)")
out.append("")
out.append("Source: `coord/IUT-TEXT/III.txt`, `IV.txt` (pypdf extraction of the IUT PDFs).")
out.append("Each line is prefixed with its global source line number so displays can be cited")
out.append("as `III:NNNN` / `IV:NNNN`; OCR line breaks and artifacts are preserved.")
out.append("")
out.append("## Display index (source line numbers)")
out.append("")
out.append("IUT III:")
out.append("- `n,◦U` / `n,◦UQ` hull/union definitions: III:10361-10404.")
out.append("- proof assumption `−|log Θ|<0` and compactness: III:10356-10414.")
out.append("- Step (x) indeterminacies summary: III:10701-10751.")
out.append("- Step (x) log-volumes convert Ind3 to upper inequality: III:10724-10732.")
out.append("- Step (xi-a) q-pilot/Θ-pilot gluing: III:10752-10763.")
out.append("- Step (xi-b) IPL/SHE output data: III:10764-10800.")
out.append("- Step (xi-c) hull enlargement and arithmetic vector bundles: III:10801-10822.")
out.append("- Step (xi-d) determinant/log-volume and `R_{<=-|log Θ|}`, `-|log(q)|`: III:10825-10870.")
out.append("")
out.append("IUT IV:")
out.append("- Step (iv) instruction to bound hull log-volume: IV:1585-1625.")
out.append("- Step (v) tensor/log-shell reduction: IV:1626-1650.")
out.append("- Step (v) inclusion/upper-bound displays: IV:1651-1686.")
out.append("- Step (v) symmetrization and weighted average: IV:1706-1743.")
out.append("- Step (v) q-term and procession-normalized bound: IV:1737-1785.")
out.append("")
for title, src, ps in sections:
    out.append("## " + title)
    out.append("")
    for p in ps:
        out.append("### Page " + str(p))
        out.append("")
        out.append("```text")
        for lineno, text in src.get(p, []):
            out.append("[%05d] %s" % (lineno, text))
        out.append("```")
        out.append("")
open(OUT, "w", encoding="utf-8").write("\n".join(out))
print("wrote", OUT, len("\n".join(out)), "chars")