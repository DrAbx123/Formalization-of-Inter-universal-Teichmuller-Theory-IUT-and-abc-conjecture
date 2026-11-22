
import re, json

P = 613
path = r"D:\lean\tmp\sheaf\xif\paper\S2554Mod613ChainDataActual.lean"
src = open(path, encoding="utf-8").read()

def parse_poly(name):
    m = re.search(r"def " + name + r" : \(ZMod 613\)\[X\] := (.*)", src)
    body = m.group(1).strip()
    if body == "X":
        return [0,1]
    terms = [t.strip() for t in body.split("+")]
    coeffs = {}
    for t in terms:
        if t == "X":
            c, e = 1, 1
        else:
            mm = re.fullmatch(r"C (\d+)(?: \* X(?: \^ (\d+))?)?", t)
            c = int(mm.group(1))
            if "X" not in t: e = 0
            elif mm.group(2): e = int(mm.group(2))
            else: e = 1
        coeffs[e] = (coeffs.get(e,0) + c) % P
    n = max(coeffs)
    return [coeffs.get(i,0) for i in range(n+1)]

G = parse_poly("G")
Ts = {i: parse_poly(f"T{i}") for i in range(1,13)}

def trim(a):
    while len(a)>1 and a[-1]==0: a.pop()
    return a
def add(a,b):
    n=max(len(a),len(b)); r=[0]*n
    for i in range(n):
        r[i]=((a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0))%P
    return trim(r)
def sub(a,b):
    n=max(len(a),len(b)); r=[0]*n
    for i in range(n):
        r[i]=((a[i] if i<len(a) else 0)-(b[i] if i<len(b) else 0))%P
    return trim(r)
def mul(a,b):
    if (len(a)==1 and a[0]==0) or (len(b)==1 and b[0]==0): return [0]
    r=[0]*(len(a)+len(b)-1)
    for i,ai in enumerate(a):
        if ai:
            for j,bj in enumerate(b):
                if bj: r[i+j]=(r[i+j]+ai*bj)%P
    return trim(r)
def compose(f,g):
    r=[0]
    for c in reversed(f):
        r=add(mul(r,g),[c])
    return r
def divmod_poly(a,b):
    a=a[:]; trim(a); b=trim(b[:])
    db=len(b)-1
    if len(a)-1 < db: return [0], a
    q=[0]*(len(a)-db)
    inv_lead=pow(b[-1], P-2, P)
    while len(a)-1 >= db:
        d=len(a)-1-db
        c=a[-1]*inv_lead%P
        q[d]=c
        for i,bi in enumerate(b):
            a[d+i]=(a[d+i]-c*bi)%P
        trim(a)
    return trim(q), trim(a)

def to_lean(a):
    parts=[]
    for e,c in enumerate(a):
        if c==0: continue
        if e==0: parts.append(f"C {c}")
        elif e==1: parts.append(f"C {c} * X")
        else: parts.append(f"C {c} * X ^ {e}")
    if not parts: parts=["C 0"]
    return " + ".join(parts)

out = {}
for k in [9,10,11]:
    comp = compose(Ts[k], Ts[1])
    Pk = sub(comp, Ts[k+1])
    q, r = divmod_poly(Pk, G)
    print(f"k={k}: deg comp={len(comp)-1}, deg P={len(Pk)-1}, deg q={len(q)-1}, rem={r}")
    assert r == [0], (k, r)
    assert mul(G,q) == Pk, k
    out[k] = {"P": Pk, "S": q}

Q = {0:[1]}
for i in range(1,12):
    Q[i]=mul(Q[i-1],Ts[1])

with open(r"D:\lean\tmp\sheaf\xif\paper\_comp3_data.json","w") as f:
    json.dump({"G":G,"T1":Ts[1],"P":{str(k):out[k]["P"] for k in out},"S":{str(k):out[k]["S"] for k in out},"Q":{str(i):Q[i] for i in Q}}, f)
for k in [9,10,11]:
    print(f"--- S{k} ---")
    print(to_lean(out[k]["S"]))
print("--- Q degrees ---")
for i in Q: print(i, len(Q[i])-1)
print("saved")
