
import re, sys
from sympy import Poly, GF, symbols

path = r"D:/lean/tmp/sheaf/xif/paper/S2554Mod613ChainDataActual.lean"
src = open(path, encoding="utf-8").read()
p = 613
x = symbols("x")

def parse_poly(body):
    d = {}
    for t in body.split("+"):
        t = t.strip()
        m = re.fullmatch(r"C\s*(\d+)\s*\*\s*X\s*\^\s*(\d+)", t)
        if m:
            c, e = int(m.group(1)), int(m.group(2)); d[e] = (d.get(e,0)+c)%p; continue
        m = re.fullmatch(r"C\s*(\d+)\s*\*\s*X", t)
        if m:
            d[1] = (d.get(1,0)+int(m.group(1)))%p; continue
        m = re.fullmatch(r"C\s*(\d+)", t)
        if m:
            d[0] = (d.get(0,0)+int(m.group(1)))%p; continue
        m = re.fullmatch(r"X\s*\^\s*(\d+)", t)
        if m:
            d[int(m.group(1))] = (d.get(int(m.group(1)),0)+1)%p; continue
        m = re.fullmatch(r"X", t)
        if m:
            d[1] = (d.get(1,0)+1)%p; continue
        raise ValueError("bad term: "+t)
    return d

data = {}
for line in src.splitlines():
    m = re.match(r"def (G|T\d+) : \(ZMod 613\)\[X\] := (.*)", line)
    if m:
        data[m.group(1)] = parse_poly(m.group(2))

def to_poly(d):
    return Poly(sum(c*x**e for e,c in d.items()), x, domain=GF(p))

P = {k: to_poly(v) for k,v in data.items()}

def fmt(d, drop_zeros=True):
    if not d: return "0"
    terms = []
    for e in sorted(d):
        c = d[e] % p
        if c == 0 and drop_zeros: continue
        if e == 0: terms.append(f"C {c}")
        elif e == 1: terms.append(f"C {c} * X")
        else: terms.append(f"C {c} * X ^ {e}")
    return " + ".join(terms)

def dense(poly):
    if poly.is_zero: return {}
    coeffs = poly.all_coeffs()  # descending
    n = len(coeffs)-1
    return {n-i: int(c) % p for i,c in enumerate(coeffs)}

comps = {}
quos = {}
for k in range(1,12):
    C = P[f"T{k}"].compose(P["T1"])
    Q = C - P[f"T{k+1}"]
    quo, rem = divmod(Q, P["G"])
    assert rem.is_zero
    comps[k] = dense(C)
    quos[k] = dense(quo)

if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "defs":
        ks = [int(a) for a in sys.argv[2].split(",")]
        out = []
        for k in ks:
            out.append(f"def P{k} : (ZMod 613)[X] :=\n  {fmt(comps[k])}\n")
            out.append(f"def S{k} : (ZMod 613)[X] :=\n  {fmt(quos[k])}\n")
        print("\n".join(out))
    elif mode == "info":
        for k in comps:
            print(k, "P deg", max(comps[k]), "len", len(comps[k]), "S deg", max(quos[k]) if quos[k] else -1, "len", len(quos[k]))
