"""C2 invariants via Sage Cremona database (N <= 2000).

WSL: /opt/miniconda/envs/sage/bin/sage tools/c2_invariants.sage
Outputs coord/c2_invariants.csv and coord/c2_invariants.jsonl.
"""
import json, csv, time, os
from sage.databases.cremona import CremonaDatabase

LIMIT = 2000
AP_LIMIT = 10000
db = CremonaDatabase()
primes = list(prime_range(AP_LIMIT))
def py(o):
    if isinstance(o, dict):
        return {str(k): py(v) for k, v in o.items()}
    if isinstance(o, (list, tuple)):
        return [py(v) for v in o]
    if o is None or isinstance(o, (bool, int, float, str)):
        return o
    try:
        return int(o)
    except Exception:
        return str(o)

rows = []
t0 = time.time()
errors = []
n_total = 0
n_semi = 0
for N in range(1, LIMIT + 1):
    try:
        data = db.allcurves(N)
    except Exception as e:
        errors.append([N, "allcurves", repr(e)])
        continue
    for lab, dat in sorted(data.items()):
        n_total += 1
        try:
            E = EllipticCurve(dat[0])
            if not E.is_semistable():
                continue
            n_semi += 1
            D = Integer(E.discriminant())
            fac = D.factor()
            bad = sorted([int(p) for p, v in fac])
            vp = {int(p): int(v) for p, v in fac}
            tam = {}
            for p in bad:
                try:
                    tam[int(p)] = int(E.tamagawa_number(p))
                except Exception as e:
                    tam[int(p)] = None
            tor = E.torsion_subgroup()
            ap = {int(p): int(E.ap(p)) for p in primes if p not in bad}
            try:
                deg = int(E.modular_degree())
            except Exception as e:
                deg = None
            rec = {
                "N": int(N),
                "label": f"{N}{lab}",
                "ainvs": [int(x) for x in E.ainvs()],
                "discriminant": int(D),
                "semistable": True,
                "bad_primes": [int(p) for p in bad],
                "vp_delta": {str(p): int(v) for p, v in vp.items()},
                "tamagawa": {str(p): v for p, v in tam.items()},
                "torsion_order": int(tor.order()),
                "torsion_invariants": [int(x) for x in tor.invariants()],
                "modular_degree": deg,
                "a_p": {str(p): v for p, v in ap.items()},
                "a_p_limit": AP_LIMIT,
            }
            rows.append(py(rec))
        except Exception as e:
            errors.append([N, lab, repr(e)])

os.makedirs("data", exist_ok=True)
with open("data/c2_invariants.jsonl", "w") as f:
    for r in rows:
        f.write(json.dumps(r) + "\n")
os.makedirs("coord", exist_ok=True)
with open("coord/c2_invariants_summary.csv", "w", newline="") as f:
    w = csv.writer(f)
    w.writerow(["metric","value"])
    w.writerow(["N_total", n_total])
    w.writerow(["N_semistable", n_semi])
    w.writerow(["rows_written", len(rows)])
    w.writerow(["LIMIT", LIMIT])
    w.writerow(["a_p_limit", AP_LIMIT])
    w.writerow(["errors", len(errors)])
print("LIMIT", LIMIT, "N_total", n_total, "N_semistable", n_semi, "rows", len(rows), "elapsed", round(elapsed,2))
print("deg_nonnull", sum(1 for r in rows if r["modular_degree"] is not None))
print("errors", len(errors), errors[:5])
