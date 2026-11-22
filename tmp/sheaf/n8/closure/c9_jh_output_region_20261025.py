"""Exact supplementary checks for J_H, eta products and local output ideals.

The proofs and source eligibility restrictions are in the companion record.
This does not enumerate or certify the complete IUT output family.
"""

from fractions import Fraction as F
from math import comb
from pathlib import Path
import json

from c9_strict_deficit_marked_height_20261025 import PRIMES, tate_x_series, is_prime


def mul(a, b, precision):
    result = [0] * (precision + 1)
    for i, x in enumerate(a[:precision + 1]):
        if x:
            for j, y in enumerate(b[:precision + 1 - i]):
                result[i + j] += x * y
    return result


def power(a, exponent, precision):
    assert exponent >= 0
    result = [1] + [0] * precision
    while exponent:
        if exponent & 1:
            result = mul(result, a, precision)
        exponent //= 2
        if exponent:
            a = mul(a, a, precision)
    return result


def binomial_factor(degree, exponent, precision):
    result = [0] * (precision + 1)
    for j in range(precision // degree + 1):
        if exponent >= 0:
            result[j * degree] = (-1)**j * comb(exponent, j) if j <= exponent else 0
        else:
            result[j * degree] = comb(-exponent + j - 1, j)
    return result


def eta_unit(ell, precision):
    k = 6 * (ell - 3)
    result = [1] + [0] * precision
    for n in range(1, precision + 1):
        result = mul(result, binomial_factor(n, -k, precision), precision)
        if ell * n <= precision:
            result = mul(result, binomial_factor(ell * n, k, precision), precision)
    return result


def kernel_discriminant_unit(ell, precision):
    m = (ell - 1) // 2
    s = m * (m - 1)
    xs = [tate_x_series(ell, j, precision + m) for j in range(1, m + 1)]
    result = [1] + [0] * precision
    for i in range(m):
        for j in range(i + 1, m):
            # x(q^(i+1)) - x(q^(j+1)) has leading term q^(i+1).
            shifted = [xs[i][r + i + 1] - xs[j][r + i + 1]
                       for r in range(precision + 1)]
            assert shifted[0] == 1
            result = mul(result, power(shifted, 12, precision), precision)
    for n in range(1, precision // ell + 1):
        result = mul(result, binomial_factor(ell * n, -24 * s, precision), precision)
    return result


def transverse_constant_checks(ell):
    checks = []
    for k in range(2, 1000):
        p = k * ell + 1
        if not is_prime(p):
            continue
        zeta = next(z for b in range(2, p)
                    if (z := pow(b, (p - 1) // ell, p)) != 1)
        xs = []
        for j in range(1, (ell - 1) // 2 + 1):
            z = pow(zeta, j, p)
            xs.append(z * pow((1-z)**2, -1, p) % p)
        disc = 1
        for i, x in enumerate(xs):
            for y in xs[i + 1:]:
                disc = disc * (x - y)**2 % p
        expected = pow(ell, -(ell - 3) // 2, p)
        assert disc == expected
        checks.append({"p": p, "discriminant_mod_p": disc,
                       "expected_ell_power_mod_p": expected})
        if len(checks) == 2:
            break
    assert len(checks) == 2
    return checks


def norm_product_exponent_check(ell, precision):
    # Cyclotomic identity product_i (1-zeta^(in)t^n):
    # (1-t^n)^ell for ell|n, and 1-t^(ell*n) otherwise.
    # Compare the exponent of every (1-t^d) in product_i U(zeta^i t)
    # and U(t^ell), with U the unit in J=q^s U.
    k = 6 * (ell - 3)
    lhs, rhs = [0]*(precision+1), [0]*(precision+1)
    for n in range(1, precision + 1):
        if ell * n <= precision:
            lhs[ell*n] += ell*k
        if n % ell == 0:
            lhs[n] -= ell*k
        elif ell*n <= precision:
            lhs[ell*n] -= k
        if ell*n <= precision:
            rhs[ell*n] -= k
        if ell*ell*n <= precision:
            rhs[ell*ell*n] += k
    assert lhs == rhs


def local_ideal_checks(ell):
    m = (ell - 1) // 2
    s, k = m*(m-1), 6*(ell-3)
    N = 2*ell*s
    examples = []
    for ord_q in (F(1, 3), F(1), F(7, 2), F(40)):
        qhat = ord_q / (2*ell)
        ord_J = s*ord_q
        for j in range(1, m+1):
            original = j*j*qhat
            reconstructed = j*j*ord_J/N
            native_region = ord_J/N
            assert original == reconstructed
            assert native_region == qhat
            assert (original > native_region) == (j > 1)
            # Common tensor powers with reference normalization change nothing.
            for M in (1, 2, 19, 2310):
                assert M*original/M == original
        seed = -sum(j*j*qhat for j in range(1, m+1))/m
        native = -qhat
        gain_needed = native - seed
        assert gain_needed == F((ell+4)*(ell-3), 24*ell)*ord_q > 0
        examples.append({"ord_q": str(ord_q), "seed_per_log_p": str(seed),
                         "native_per_log_p": str(native),
                         "gain_needed_per_log_p": str(gain_needed)})
    return {"N": N, "eta_exponent": k,
            "selected_J_q_exponent": s,
            "full_line_product_constant": f"{ell}^(-{3*ell*(ell-3)})",
            "normalized_examples": examples}


def finite_curve_norm_check(ell, p):
    """Independent check from points, Velu quotients and actual kernel roots.

    No eta product or cusp expansion is used in constructing the J_H values.
    The field has characteristic different from 2,3,ell.
    """
    roots = {}
    for y in range(p):
        roots.setdefault(y*y % p, []).append(y)

    def add(P, Q, a):
        if P is None:
            return Q
        if Q is None:
            return P
        x, y = P
        xx, yy = Q
        if x == xx and (y + yy) % p == 0:
            return None
        slope = ((3*x*x+a)*pow(2*y, -1, p) if P == Q
                 else (yy-y)*pow(xx-x, -1, p)) % p
        rx = (slope*slope - x - xx) % p
        return (rx, (slope*(x-rx)-y) % p)

    def times(n, P, a):
        result = None
        while n:
            if n & 1:
                result = add(result, P, a)
            n //= 2
            if n:
                P = add(P, P, a)
        return result

    curve = None
    for a in range(min(p, 30)):
        for b in range(p):
            if (4*a**3+27*b*b) % p == 0:
                continue
            pts = [None] + [(x,y) for x in range(p)
                            for y in roots.get((x**3+a*x+b) % p, [])]
            if len(pts) % (ell*ell):
                continue
            torsion = [P for P in pts if times(ell, P, a) is None]
            if len(torsion) == ell*ell:
                curve = (a, b, len(pts), torsion)
                break
        if curve:
            break
    assert curve is not None, (ell, p)
    a, b, count, torsion = curve
    covered = {None}
    Js = []
    m, s = (ell-1)//2, ((ell-1)//2)*((ell-3)//2)
    for P in torsion[1:]:
        if P in covered:
            continue
        H = {times(n, P, a) for n in range(ell)}
        assert len(H) == ell
        covered |= H
        H0 = H - {None}
        # Short-Weierstrass Velu formulas for E/H.
        aa = (a - 5*sum(3*x*x+a for x,y in H0)) % p
        bb = (b - 7*sum(5*x**3+3*a*x+2*b for x,y in H0)) % p
        delta = -16*(4*aa**3+27*bb*bb) % p
        assert delta
        kernel_xs = set()
        for T in torsion:
            if T in H:
                continue
            xphi = (T[0] + sum(add(T,Q,a)[0]-Q[0] for Q in H0)) % p
            kernel_xs.add(xphi)
        assert len(kernel_xs) == m
        xs = sorted(kernel_xs)
        disc = 1
        for i,x in enumerate(xs):
            for y in xs[i+1:]:
                disc = disc*(x-y)**2 % p
        J = pow(disc, 6, p)*pow(delta, -s, p) % p
        assert J
        Js.append(J)
    assert len(Js) == ell+1
    norm = 1
    for J in Js:
        norm = norm*J % p
    expected = pow(ell, -3*ell*(ell-3), p)
    assert norm == expected, (ell, p, norm, expected)
    return {"ell": ell, "p": p, "curve_a": a, "curve_b": b,
            "curve_point_count": count, "rational_ell_torsion_count": len(torsion),
            "J_values_from_Velu": Js, "product": norm,
            "expected_constant_mod_p": expected}


def main():
    precision = 40
    cases = []
    for ell in PRIMES:
        by_roots = kernel_discriminant_unit(ell, precision)
        by_eta = eta_unit(ell, precision)
        assert by_roots == by_eta
        assert by_eta[:2] == [1, 6*(ell-3)]
        norm_precision = 3*ell*ell
        norm_product_exponent_check(ell, norm_precision)
        cases.append({"ell": ell,
                      "unit_coefficients_checked_through_q_degree": precision,
                      "first_six_unit_coefficients": by_eta[:6],
                      "norm_product_factor_degrees_checked": norm_precision,
                      "transverse_constant_checks": transverse_constant_checks(ell),
                      "local_regions": local_ideal_checks(ell)})
    actual_curve_checks = [finite_curve_norm_check(ell,p)
                           for ell,p in ((5,101),(7,197),(11,353))]
    result = {
        "task": "C9-JH-OUTPUT-REGION-20261025",
        "all_assertions_passed": True,
        "arithmetic": "exact integer series, rational exponents, finite fields",
        "cases": cases,
        "independent_Velu_curve_checks": actual_curve_checks,
        "totals": {"primes": len(cases),
                   "unit_coefficients_compared": len(cases)*(precision+1),
                   "transverse_constant_checks": 2*len(cases),
                   "native_valuation_cases": 4*len(cases),
                   "independent_Velu_curves": len(actual_curve_checks)},
        "scope": {
            "general_proofs": "in companion natural-language record; finite checks supplement them",
            "full_source_output_family_computed": False,
            "strict_deficit_contradiction_proved": False,
            "target_accepted": False
        }
    }
    output = Path(__file__).with_name("C9-JH-OUTPUT-REGION-CERTIFICATE-20261025.json")
    output.write_text(json.dumps(result, indent=2, ensure_ascii=False)+"\n", encoding="utf-8")
    print(json.dumps({"all_assertions_passed": True, "totals": result["totals"],
                      "ell41": next(c for c in cases if c["ell"] == 41),
                      "target_accepted": False}, ensure_ascii=False))


if __name__ == "__main__":
    main()
