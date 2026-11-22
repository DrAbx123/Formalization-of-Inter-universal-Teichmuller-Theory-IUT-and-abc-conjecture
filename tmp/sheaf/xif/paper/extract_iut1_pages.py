import pymupdf, io
p = r"D:\lean\tmp\external\promachina-iut-lean\docs\papers\mochizuki-iut-i.pdf"
doc = pymupdf.open(p)
out = []
for i in range(58, 74):
    t = doc[i].get_text()
    if ("orders of the" in t) or ("2l-th root" in t) or ("local heights" in t):
        out.append("="*30 + " PDF page " + str(i+1))
        out.append(t)
with io.open(r"D:\lean\tmp\sheaf\xif\paper\extract_iut1_pages.out.txt", "w", encoding="utf-8") as f:
    f.write("\n".join(out))
print("wrote", len("\n".join(out)))
