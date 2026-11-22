import pymupdf, io, os, re
paths = [
 r"D:\lean\tmp\dsh-oct6-openai-math-survey-20261016\repos\lana\genl\genl-master\paper\mochizuki-mjou52.pdf",
 r"D:\lean\tmp\external\promachina-iut-lean\docs\papers\mochizuki-etale-theta-frobenioid.pdf",
]
out = []
for p in paths:
    try:
        doc = pymupdf.open(p)
        out.append("="*30 + " " + os.path.basename(p) + " pages " + str(doc.page_count))
        t = doc[0].get_text()[:2000]
        t = "".join(ch if (32 <= ord(ch) < 127 or ch in "\n\t") else " " for ch in t)
        out.append(t)
    except Exception as e:
        out.append(str(e))
io.open(r"D:\lean\tmp\sheaf\xif\paper\genl_first_pages.txt","w",encoding="utf-8").write("\n".join(out))
print("ok")
