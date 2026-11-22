
import os, re, sys
root = r"D:\lean"
start = r"tmp\sheaf\xif\paper\S2554Mod613ChainDataActual.lean"
seen = set()
found_mathlib = []
found_field = []
stack = [start]
while stack:
    rel = stack.pop()
    rel = rel.replace("/", "\\")
    if rel in seen: continue
    seen.add(rel)
    full = os.path.join(root, rel)
    if not os.path.exists(full):
        continue
    with open(full, encoding="utf-8", errors="replace") as f:
        for line in f:
            line=line.strip()
            if line.startswith("import "):
                mod = line[len("import "):].strip()
                if mod == "Mathlib":
                    found_mathlib.append(rel)
                if mod.startswith("Mathlib.Algebra.Field.ZMod"):
                    found_field.append(rel)
                path = mod.replace(".", "\\") + ".lean"
                # local modules start with tmp, LeanFormal, Iut
                if os.path.exists(os.path.join(root, path)):
                    stack.append(path)
print("files walked:", len(seen))
print("imports full Mathlib (count):", len(found_mathlib))
for x in found_mathlib[:5]: print("  ", x)
print("imports Field.ZMod (count):", len(found_field))
for x in found_field[:5]: print("  ", x)
