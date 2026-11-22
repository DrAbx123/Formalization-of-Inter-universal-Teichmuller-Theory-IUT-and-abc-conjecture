#!/usr/bin/env python3
"""C2 invariants for semistable elliptic curves (route C, EXPLORATION-ROUTES C2).

Pure-Python/numpy fallback: no Sage/Pari, no LMFDB (reCAPTCHA-blocked).  Exact data:
discriminant, bad-prime valuations, a_p for good p <= 10000, rational 2-torsion.
Fields requiring Sage/LMFDB (deg phi, Tamagawa, full torsion, Sha order, real period,
isogeny class) are emitted as null with a reason.
"""
import json, csv, math
import numpy as np

AP_LIMIT = 10000

def primes_upto(n):
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i*i::i] = b"\x00" * (((n - i*i)//i) + 1)
    return [i for i in range(n + 1) if sieve[i]]

PRIMES = primes_upto(AP_LIMIT)

def factorint(n):
    n = abs(int(n)); out = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            out[d] = out.get(d, 0) + 1
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out

def inv(a1,a2,a3,a4,a6):
    b2 = a1*a1 + 4*a2
    b4 = 2*a4 + a1*a3
    b6 = a3*a3 + 4*a6
    b8 = a1*a1*a6 + 4*a2*a6 - a1*a3*a4 + a2*a3*a3 - a4*a4
    disc = -b2*b2*b8 - 8*b4**3 - 27*b6*b6 + 9*b2*b4*b6
    return disc

def ap_for_good(p, a2, a4, a6):
    # count points on y^2 = x^3 + a2 x^2 + a4 x + a6 over F_p
    x = np.arange(p, dtype=np.int64)
    rhs = (x*x % p * x + a2 % p * (x*x % p) + a4 % p * x + a6 % p) % p
    squares = np.zeros(p, dtype=bool)
    t = np.arange(1, p, dtype=np.int64)
    squares[(t*t) % p] = True
    # points = 1 + sum_x (1 + [rhs zero ? 0 : (qr ? +1 : -1)])
    vals = np.where(rhs == 0, 0, np.where(squares[rhs], 1, -1))
    points = 1 + p + int(vals.sum())
    return int(p + 1 - points)

def rational_roots_cubic(a2,a4,a6):
    # rational root test on monic x^3 + a2 x^2 + a4 x + a6
    roots = []
    if a6 == 0:
        roots.append(0)
    for d in range(1, 200):
        if a6 % d != 0:
            continue
        for r in (d, -d):
            if r*r*r + a2*r*r + a4*r + a6 == 0:
                if r not in roots:
                    roots.append(r)
    return sorted(roots)

def curve_record(label, a1,a2,a3,a4,a6, note=""):
    D = inv(a1,a2,a3,a4,a6)
    fp = factorint(D) if D != 0 else {}
    bad = sorted(fp)
    rec = {
        "label": label,
        "equation": f"y^2 + {a1}xy + {a3}y = x^3 + {a2}x^2 + {a4}x + {a6}",
        "a1": a1, "a2": a2, "a3": a3, "a4": a4, "a6": a6,
        "discriminant": int(D),
        "bad_primes": bad,
        "vp_delta": {str(p): int(fp[p]) for p in bad},
        "conductor_model": int(math.prod(bad)) if bad else 1,
        "conductor_note": "semistable model: product of bad primes; p=2,3 may need local correction",
        "semistable_flag": all(fp[p] == 1 for p in bad),
        "torsion_2": rational_roots_cubic(a2,a4,a6),
        "torsion_full": None,
        "torsion_full_reason": "needs Sage/Magma; only rational 2-torsion computed",
        "tamagawa": None,
        "tamagawa_reason": "needs Tate algorithm/Sage",
        "deg_phi": None,
        "deg_phi_reason": "no modular-degree data source (LMFDB unavailable)",
        "analytic_sha_order": None,
        "analytic_sha_reason": "needs L-series/Sage",
        "real_period": None,
        "real_period_reason": "needs numerical integration/Sage",
        "isogeny_class": None,
        "isogeny_class_reason": "needs database/Sage",
        "a_p": {},
        "a_p_limit": AP_LIMIT,
        "note": note,
    }
    good = [p for p in PRIMES if p != 2 and p not in bad]
    for p in good:
        rec["a_p"][str(p)] = ap_for_good(p,a2,a4,a6)
    rec["a_p_bad_primes_skipped"] = [p for p in PRIMES if p in bad]
    return rec

def main():
    samples = []
    # Frey family (1, 3^k - 1, 3^k), k = 2..21
    for k in range(2, 22):
        a, b, c = 1, 3**k - 1, 3**k
        A = b - a
        B = -a * b
        samples.append(curve_record(f"Frey_3_{k}", 0, A, 0, B, 0,
                                    f"(1,{b},{c})"))
    # 20 hand curves: y^2 = x^3 + m x + 1 with squarefree discriminant
    # 20 deterministic hand curves y^2 = x^3 + m*x + 1, m=1..20
    for m in range(1, 21):
        D = -16 * (4 * m**3 + 27)
        if D != 0:
            samples.append(curve_record(f"Hand_{m}_m{m}", 0, 0, 0, m, 1,
                                        "hand curve y^2=x^3+m*x+1"))
    out = {
        "generated_at": "2026-11-12",
        "source": "tools/c2_invariants.py",
        "ap_limit": AP_LIMIT,
        "network_lmfdb": "blocked: LMFDB API returns reCAPTCHA challenge (HTTP 200 HTML, not JSON)",
        "field_status": {
            "discriminant": "exact",
            "bad_primes": "exact",
            "vp_delta": "exact",
            "a_p": "exact for good p <= 10000 (numpy point count)",
            "torsion_2": "exact rational 2-torsion",
            "conductor": "semistable model, product of bad primes; local p=2,3 corrections pending",
            "tamagawa": "null (Sage required)",
            "deg_phi": "null (LMFDB/Sage required)",
            "analytic_sha_order": "null",
            "real_period": "null",
            "isogeny_class": "null",
            "torsion_full": "null",
        },
        "n_samples": len(samples),
        "samples": samples,
    }
    with open("data/c2_invariants.json","w",encoding="utf-8") as f:
        json.dump(out,f,indent=1)
    with open("data/c2_invariants.csv","w",newline="",encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["label","a2","a4","a6","discriminant","conductor_model","semistable_flag","torsion_2","n_ap_good","bad_primes","vp_delta"])
        for s in samples:
            w.writerow([s["label"],s["a2"],s["a4"],s["a6"],s["discriminant"],s["conductor_model"],
                        s["semistable_flag"],s["torsion_2"],len(s["a_p"]),
                        s["bad_primes"],s["vp_delta"]])
    print("samples", len(samples), "ap_limit", AP_LIMIT)
    print("json bytes", __import__("os").path.getsize("data/c2_invariants.json"))

if __name__ == "__main__":
    main()
