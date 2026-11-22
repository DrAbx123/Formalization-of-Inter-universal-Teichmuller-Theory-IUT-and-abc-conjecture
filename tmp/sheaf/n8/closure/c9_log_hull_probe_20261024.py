"""Exact local check for the C9 natural-language contradiction attack.

This checks a genuine Q_3 logarithm/hull obstruction.  It does not instantiate
complete initial Theta-data or prove/refute Corollary 3.12.
"""
from fractions import Fraction
import json
from pathlib import Path


def vp(n: int, p: int) -> int:
    if n == 0:
        raise ValueError("valuation at zero is not used")
    result = 0
    while n % p == 0:
        n //= p
        result += 1
    return result


def log_mod(u: int, p: int, precision: int) -> int:
    modulus = p ** precision
    t = u - 1
    assert t % p == 0
    result = 0
    # For j >= 2*precision, j-v_3(j) >= j/2 >= precision.
    # Thus the omitted terms all vanish modulo 3**precision for t in 3 Z_3.
    for j in range(1, 2 * precision):
        denominator_power = vp(j, p)
        denominator_unit = j // (p ** denominator_power)
        numerator = pow(t, j)
        assert numerator % (p ** denominator_power) == 0
        term = (numerator // (p ** denominator_power)) % modulus
        term = term * pow(denominator_unit, -1, modulus) % modulus
        result += term if j % 2 else -term
    return result % modulus


def main() -> None:
    p, precision = 3, 6
    modulus = p ** precision
    cases = []
    for depth in (2, 3):
        units = set(range(1, modulus, p ** depth))
        log_images = {log_mod(u, p, precision) for u in units}
        expected = set(range(0, modulus, p ** depth))
        assert log_images == expected
        assert len(log_images) == len(units)
        assert min(vp(u, p) for u in units) == 0
        nonzero_images = log_images - {0}
        assert min(vp(x, p) for x in nonzero_images) == depth
        assert all(x % p == 0 for x in log_images)
        assert not any(x % p for x in log_images)
        cases.append({
            "unit_region": f"1 + 3^{depth} Z_3",
            "log_region": f"3^{depth} Z_3",
            "residue_count": len(units),
            "log_bijection_mod_3_power_6": True,
            "additive_volume": str(Fraction(1, p ** depth)),
            "unit_region_hull": "Z_3",
            "log_region_hull": f"3^{depth} Z_3",
            "intersection_with_next_unit_domain": "empty",
        })
    report = {
        "task": "C9-CONTRADICTION-ATTACK-20261024",
        "scope": "Actual local Q_3 operations only; not full source Theta-data",
        "modulus": modulus,
        "precision": precision,
        "cases": cases,
        "natural_language_proofs_required": [
            "log/exp bijection 1+3^k Z_3 -> 3^k Z_3 for all k>=1",
            "tail valuation bound for the exact finite logarithm computation",
            "hull is the smallest fractional Z_3 ideal containing the set",
        ],
        "actual_IUT_refutation": False,
        "target_accepted": False,
        "checks": "all assertions passed",
    }
    target = Path(__file__).with_name("C9-LOG-HULL-PROBE-CERTIFICATE-20261024.json")
    target.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({"certificate": str(target.resolve()), "checks": report["checks"],
                      "residue_counts": [c["residue_count"] for c in cases]}, ensure_ascii=False))


if __name__ == "__main__":
    main()
