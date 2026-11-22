import re, os, collections
root = r"D:\lean"
target = "LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31RootLemmas"
start = "tmp.sheaf.xif.paper.S1784SourceRetractionUnitActual"
mods = {}
for base, dirs, files in os.walk(root):
    if ".lake" in base or ".git" in base: continue
    for f in files:
        if f.endswith(".lean"):
            p = os.path.join(base,f)
            mod = os.path.relpath(p, root)[:-5].replace("\\",".").replace("/",".")
            try:
                with open(p, encoding="utf-8") as fh:
                    txt = fh.read(20000)
            except: continue
            imps = re.findall(r"^import\s+([A-Za-z0-9_.]+)", txt, re.M)
            mods[mod] = imps
# BFS
prev = {start: None}
q = collections.deque([start])
while q:
    m = q.popleft()
    if m == target: break
    for i in mods.get(m, []):
        if i not in prev:
            prev[i] = m
            q.append(i)
if target in prev:
    path = []
    x = target
    while x is not None:
        path.append(x); x = prev[x]
    print("PATH:", " -> ".join(reversed(path)))
else:
    print("no path via direct imports; modules parsed:", len(mods))
