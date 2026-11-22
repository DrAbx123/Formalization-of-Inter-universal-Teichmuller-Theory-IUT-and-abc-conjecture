"""Exact checks for a marked, non-cancelling torsion-height observable.

These are rational coefficient and finite SL2 checks.  They neither compute
the complete IUT output family nor certify the original P6 contradiction.
The mathematical proofs, normalization and scope are in the task record.
"""

from collections import Counter
from fractions import Fraction as F
import json
from pathlib import Path


PRIMES = (5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43)


def b2(x):
    return x * x - x + F(1, 6)


def projective_line(a, c, ell):
    # Finite t denotes the line spanned by (1,t); ell denotes infinity.
    return (c * pow(a, -1, ell)) % ell if a else ell


def sl2_matrices(ell):
    # Enumerate every determinant-one matrix, once, by its first column.
    for a in range(ell):
        for c in range(ell):
            if not (a or c):
                continue
            if a:
                ia = pow(a, -1, ell)
                for b in range(ell):
                    yield (a, b, c, ((1 + b * c) * ia) % ell)
            else:
                b = -pow(c, -1, ell) % ell
                for d in range(ell):
                    yield (a, b, c, d)


def line_permutation(matrix, ell):
    a, b, c, d = matrix
    points = [(1, t) for t in range(ell)] + [(0, 1)]
    return [projective_line((a*x + b*y) % ell,
                            (c*x + d*y) % ell, ell)
            for x, y in points]


def transport(values, perm):
    result = [None] * len(values)
    for i, j in enumerate(perm):
        result[j] = values[i]
    return result


def avg(values):
    return sum(values, F(0)) / len(values)


def pairing(left, right):
    return avg([x*y for x, y in zip(left, right)])


def tate_x_series(ell, j, precision):
    """x(q^j; q^ell) through the stated q degree, using integral coefficients."""
    result = [0]*(precision+1)
    radius = precision//ell+2
    for n in range(-radius, radius+1):
        exponent = abs(ell*n+j)
        for k in range(1, precision//exponent+1):
            result[k*exponent] += k
    for n in range(1, precision//ell+1):
        for k in range(1, precision//(ell*n)+1):
            result[ell*n*k] -= 2*n
    return result


def leading(series):
    return next((i, a) for i, a in enumerate(series) if a)


def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, int(n**0.5)+1))


def discriminant_checks(ell):
    """Check the coordinate-invariant nonzero source number J.

    J = disc(kernel_polynomial)^6 / Delta(E')^(m(m-1)).
    Its non-vanishing and formulas for every prime are proved in the record;
    series/finite-field calculations below are finite independent checks.
    """
    m = (ell-1)//2
    series = [tate_x_series(ell, j, 2*ell) for j in range(1, m+1)]
    for j, s in enumerate(series, 1):
        assert leading(s) == (j, 1)
    disc_exponent = 0
    for i in range(m):
        for j in range(i+1, m):
            power, coefficient = leading([a-b for a, b in zip(series[i], series[j])])
            assert (power, coefficient) == (i+1, 1)
            disc_exponent += 2*power
    assert disc_exponent == m*(m*m-1)//3
    selected_J_exponent = 6*disc_exponent - ell*m*(m-1)
    other_J_exponent = -F(m*(m-1), ell)
    assert selected_J_exponent == m*(m-1)

    fields = []
    for k in range(2, 200):
        p = k*ell+1
        if not is_prime(p):
            continue
        zeta = next(z for b in range(2, p)
                    if (z := pow(b, (p-1)//ell, p)) != 1)
        xs = []
        for j in range(1, m+1):
            z = pow(zeta, j, p)
            xs.append(z*pow((1-z)**2, -1, p) % p)
        assert len(set(xs)) == m
        disc = 1
        for i in range(m):
            for j in range(i+1, m):
                disc = disc*(xs[i]-xs[j])**2 % p
        assert disc != 0
        fields.append({"p": p, "zeta": zeta, "kernel_discriminant_mod_p": disc})
        if len(fields) == 2:
            break
    assert len(fields) == 2
    native_power = 2*ell*m*(m-1)
    for j in range(1, m+1):
        assert native_power*F(j*j, 2*ell) == j*j*selected_J_exponent
    marker = [-ell]+[1]*ell
    log_J = [-F(selected_J_exponent)]+[-other_J_exponent]*ell
    assert avg(log_J) == 0
    assert pairing(marker, log_J) == m*(m-1)
    return {
        "kernel_polynomial_degree": m,
        "kernel_discriminant_q_exponent": disc_exponent,
        "selected_ord_J_per_ord_q": str(selected_J_exponent),
        "other_ord_J_per_ord_q": str(other_J_exponent),
        "marked_log_J_moment_per_L": str(pairing(marker, log_J)),
        "gaussian_to_J_power": native_power,
        "tate_series_precision": 2*ell,
        "other_type_finite_field_checks": fields,
    }


def check_prime(ell):
    n = ell + 1
    half = (ell - 1) // 2

    # Ordinary E(q)[ell] averaging: the q coefficient cancels.
    assert sum((b2(F(j, ell)) for j in range(ell)), F(0)) == F(1, 6*ell)
    all_torsion_q = ((ell - 1)*b2(F(0))
                     + ell*sum((b2(F(j, ell)) for j in range(1, ell)), F(0))) / 2
    assert all_torsion_q == 0

    # The source degree-ell cover is E(q^ell) -> E(q), with kernel q^j.
    selected_heights = [F(ell, 2)*b2(F(j, ell)) for j in range(1, ell)]
    assert avg(selected_heights) == -F(1, 12)
    assert avg(selected_heights[:half]) == -F(1, 12)
    transverse_dual_height = F(1, 12*ell)  # Residue characteristic != ell.

    gaussian = [-F(j*j, 2*ell) for j in range(1, half+1)]
    for j, g in enumerate(gaussian, 1):
        lam = F(ell, 2)*b2(F(j, ell))
        assert g == -lam - F(j, 2) + F(ell, 12)
    seed = avg(gaussian)
    native_q = -F(1, 2*ell)
    assert seed == -F(ell+1, 24)
    assert native_q - seed == F((ell+4)*(ell-3), 24*ell) > 0

    # Both the height profile and the type marker are indexed by P^1(F_ell).
    # All values below are coefficients of L = -log|q|; L is not set to a
    # purported algebraic realization by this numerical calculation.
    marker = [-ell] + [1]*ell
    height = [F(r, 12*ell) for r in marker]
    assert height[0] == avg(selected_heights)
    assert height[1] == transverse_dual_height
    assert avg(height) == 0
    assert pairing(marker, height) == F(1, 12)
    assert pairing(height, height) == F(1, 144*ell)
    assert avg([abs(a) for a in height]) == F(1, 6*n)
    assert all(r*a > 0 for r, a in zip(marker, height))

    # The full marked Gram matrix is n*I-J, not a zero scalar trace.
    marked_profiles = [[-ell if i == t else 1 for i in range(n)]
                       for t in range(n)]
    gram_checks = 0
    for t in range(n):
        for s in range(n):
            actual = pairing(marked_profiles[t], marked_profiles[s])
            expected = ell if t == s else -1
            assert actual == expected
            gram_checks += 1

    # An actual source Galois image contains SL2, so this verifies the
    # transitive line counting used in the general group-theoretic proof.
    image_counts = Counter()
    group_count = 0
    for a, b, c, d in sl2_matrices(ell):
        assert (a*d - b*c) % ell == 1
        image_counts[projective_line(a, c, ell)] += 1
        group_count += 1
    assert group_count == ell*(ell*ell-1)
    assert len(image_counts) == n
    assert set(image_counts.values()) == {ell*(ell-1)}

    # A reproducible 20-step example of simultaneous transport.  The proof
    # covers every finite length; this is just an implementation check.
    h, r = height, marker
    for k in range(20):
        t = (k+1) % ell
        matrix = (1, t, 0, 1) if k % 2 == 0 else (1, 0, t, 1)
        perm = line_permutation(matrix, ell)
        assert sorted(perm) == list(range(n))
        h, r = transport(h, perm), transport(r, perm)
        assert pairing(r, h) == F(1, 12)
        assert pairing(h, h) == F(1, 144*ell)
        assert avg(h) == 0

    # Freeze a marker in the wrong frame: the average over all displaced
    # height profiles vanishes.  Thus simultaneous transport is essential.
    wrong_frame_pairings = [pairing(marker, [F(x, 12*ell) for x in profile])
                            for profile in marked_profiles]
    assert wrong_frame_pairings[0] == F(1, 12)
    assert wrong_frame_pairings[1:] == [-F(1, 12*ell)]*ell
    assert avg(wrong_frame_pairings) == 0

    return {
        "ell": ell,
        "q_coefficient_complete_torsion_sum": str(all_torsion_q),
        "source_cover_kernel_height_per_L": str(avg(selected_heights)),
        "other_cover_kernel_height_per_L": str(transverse_dual_height),
        "unmarked_mean_per_L": str(avg(height)),
        "marked_pairing_per_L": str(pairing(marker, height)),
        "energy_per_L_squared": str(pairing(height, height)),
        "absolute_mean_per_L": str(avg([abs(x) for x in height])),
        "gaussian_seed_per_L": str(seed),
        "native_q_per_L": str(native_q),
        "seed_gap_per_L": str(native_q-seed),
        "sl2_matrices_checked": group_count,
        "images_per_projective_line": ell*(ell-1),
        "gram_entries_checked": gram_checks,
        "simultaneous_transport_steps": 20,
        "incorrectly_frozen_marker_average_per_L": str(avg(wrong_frame_pairings)),
        "source_kernel_discriminant": discriminant_checks(ell),
    }


def main():
    cases = [check_prime(ell) for ell in PRIMES]
    result = {
        "task": "C9-STRICT-DEFICIT-LOOP-20261024",
        "completed": "2026-10-25",
        "all_assertions_passed": True,
        "arithmetic": "Exact rational arithmetic and finite SL2 enumeration",
        "cases": cases,
        "totals": {
            "primes": len(cases),
            "sl2_matrices": sum(c["sl2_matrices_checked"] for c in cases),
            "gram_entries": sum(c["gram_entries_checked"] for c in cases),
            "transport_steps": sum(c["simultaneous_transport_steps"] for c in cases),
        },
        "scope": {
            "proved_in_record": "General marked height and energy identities; finite-depth simultaneous permutation invariance",
            "actual_full_IUT_output_family_computed": False,
            "strict_deficit_source_contradiction_proved": False,
            "target_accepted": False,
            "warning": "A positive auxiliary invariant is not the paper's normalized region volume and supplies no zero identity by itself.",
        },
    }
    output = Path(__file__).with_name("C9-STRICT-DEFICIT-MARKED-HEIGHT-CERTIFICATE-20261025.json")
    output.write_text(json.dumps(result, indent=2, ensure_ascii=False)+"\n", encoding="utf-8")
    print(json.dumps({"all_assertions_passed": True, "totals": result["totals"],
                      "ell41": next(c for c in cases if c["ell"] == 41),
                      "certificate": str(output), "target_accepted": False},
                     ensure_ascii=False))


if __name__ == "__main__":
    main()
