# B0 modular pipeline: S2(Gamma0(N)) integral basis, integral T_p matrices,
# newform eigencharacters, r_f (congruence number), deg phi (modular degree).
# Run: wsl ... sage tools/b0_modular.sage
import json, os, sys, time
from sage.all import *

OUT_JSON = os.environ.get("B0_JSON", "coord/b0_modular_data.json")
OUT_CSV  = os.environ.get("B0_CSV",  "coord/b0_data.csv")
NMAX = int(os.environ.get("B0_NMAX", "30"))
PMAX = 25   # Hecke primes p <= PMAX

def is_squarefree(n):
    return n == 1 or all(e == 1 for _, e in factor(n))

def jsonable(x):
    try:
        if x in ZZ: return int(x)
        if x in QQ: return str(x)
        return str(x)
    except Exception:
        return str(x)

def matrix_rows(M):
    M = Matrix(M)
    return [[jsonable(x) for x in row] for row in M.rows()]

def integral_matrix(M):
    M = Matrix(M)
    return all(x in ZZ for x in M.list())

data = {
    "sage_version": str(version()),
    "NMAX": NMAX, "PMAX": PMAX,
    "levels": {}, "curves": [], "known_checks": {}, "errors": [],
}
t0 = time.time()
for N in range(1, NMAX + 1):
    try:
        cs = list(cremona_curves(N))
    except Exception as e:
        data["errors"].append({"level": N, "stage": "cremona_curves", "error": str(e)})
        continue
    sem = [E for E in cs if E.is_semistable()]
    if not sem:
        continue
    lev = {"N": N, "squarefree": bool(is_squarefree(N)),
           "n_curves": len(cs), "n_semistable": len(sem),
           "symbols": {}, "T_p": {}, "newforms": []}
    # ---- modular symbols / S2 integral basis ----
    try:
        M = ModularSymbols(Gamma0(N), 2)
        C = M.cuspidal_submodule()
        lev["symbols"] = {
            "ambient_dim": int(M.dimension()),
            "cuspidal_dim": int(C.dimension()),
            "integral_basis": [str(b) for b in C.integral_basis()],
            "integral_coords": [list(map(int, C.coordinate_vector(b))) for b in C.integral_basis()],
        }
        # q-expansion integral basis of S2 (for cross-check)
        try:
            lev["symbols"]["q_integral_basis"] = [str(f) for f in CuspForms(Gamma0(N),2).integral_basis()]
        except Exception as e:
            lev["symbols"]["q_integral_basis_error"] = str(e)
        # ---- integral T_p matrices ----
        for p in primes(PMAX):
            T = C.hecke_matrix(p)
            entry = {"integral": bool(integral_matrix(T)),
                     "base_ring": str(T.base_ring()),
                     "matrix": matrix_rows(T)}
            lev["T_p"][int(p)] = entry
    except Exception as e:
        data["errors"].append({"level": N, "stage": "modular_symbols", "error": str(e)})
    # ---- newforms ----
    try:
        NF = CuspForms(Gamma0(N), 2).newforms(names='a')
        for i, f in enumerate(NF):
            coeffs = f.coefficients(20)
            lev["newforms"].append({
                "index": i,
                "level": int(f.level()),
                "q_expansion": str(f.q_expansion(20)),
                "coeffs_1_20": [jsonable(c) for c in coeffs],
                "degree": int(getattr(f, "degree", 0)) if hasattr(f, "degree") else None,
            })
    except Exception as e:
        data["errors"].append({"level": N, "stage": "newforms", "error": str(e)})
    data["levels"][int(N)] = lev
    print("LEVEL", N, "dim_cuspidal", lev["symbols"].get("cuspidal_dim"),
          "newforms", len(lev["newforms"]), "semistable", len(sem), flush=True)
    # ---- curves ----
    for E in sem:
        try:
            lab = str(E.label())
            rf, dphi = E.congruence_number(), E.modular_degree()
            sq = is_squarefree(N)
            row = {
                "N": int(N), "curve": lab, "conductor": int(E.conductor()),
                "is_semistable": True, "squarefree": bool(sq),
                "r_f": str(rf), "deg_phi": str(dphi),
                "deg_eq_rf": bool(sq and rf == dphi),
            }
            data["curves"].append(row)
            print("CURVE", lab, "r_f", rf, "deg_phi", dphi, "ARS", row["deg_eq_rf"], flush=True)
        except Exception as e:
            data["errors"].append({"N": int(N), "curve": str(getattr(E,'label',lambda: E)()),
                                   "stage": "invariants", "error": str(e)})
# ---- known checks (including N=37 outside the sample) ----
for lab, expected in [("11a1",1), ("14a1",1), ("37a1",2)]:
    try:
        E = EllipticCurve(lab)
        got = [str(E.modular_degree()), str(E.congruence_number())]
        data["known_checks"][lab] = {
            "conductor": int(E.conductor()), "expected_deg_phi": expected,
            "modular_degree": got[0], "congruence_number": got[1],
            "ok": int(E.modular_degree()) == expected,
            "semistable": bool(E.is_semistable()),
        }
    except Exception as e:
        data["known_checks"][lab] = {"error": str(e)}
data["elapsed_sec"] = round(time.time() - t0, 2)

os.makedirs("coord", exist_ok=True)
with open(OUT_JSON, "w") as fh:
    json.dump(data, fh, indent=1, sort_keys=True, default=lambda o: jsonable(o))
# ---- CSV summary ----
header = ["N","curve","conductor","semistable","squarefree","r_f","deg_phi","deg_eq_rf","dim_cuspidal","n_newforms","Tp_all_integral"]
with open(OUT_CSV, "w") as fh:
    fh.write(",".join(header) + "\n")
    for row in data["curves"]:
        lev = data["levels"].get(row["N"], {})
        dim = lev.get("symbols", {}).get("cuspidal_dim", "")
        nf = len(lev.get("newforms", []))
        tp = lev.get("T_p", {})
        tpall = bool(tp) and all(v["integral"] for v in tp.values())
        fh.write(",".join(map(str, [row["N"], row["curve"], row["conductor"], row["is_semistable"],
            row["squarefree"], row["r_f"], row["deg_phi"], row["deg_eq_rf"], dim, nf, tpall])) + "\n")
print("SUMMARY curves", len(data["curves"]), "levels", len(data["levels"]),
      "errors", len(data["errors"]), "elapsed", data["elapsed_sec"], flush=True)
print("KNOWN", json.dumps(data["known_checks"], sort_keys=True, default=str), flush=True)
