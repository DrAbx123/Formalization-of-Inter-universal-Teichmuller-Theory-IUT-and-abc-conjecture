"""Exact local checks for the root's natural-language evaluation investigation.

These are tensor lattices of actual quadratic local fields, not complete
initial Theta-data and not certificates for IUT III Corollary 3.12.
Only rational arithmetic is used; log(p) is retained as a formal unit.
"""
from fractions import Fraction as F
from math import comb
from pathlib import Path
import json


def vp(x, p):
    x = F(x)
    if not x:
        return None
    a, b, n = abs(x.numerator), x.denominator, 0
    while a % p == 0:
        a //= p
        n += 1
    while b % p == 0:
        b //= p
        n -= 1
    return n


def inverse(a):
    n = len(a)
    b = [list(map(F, row)) + [F(i == j) for j in range(n)]
         for i, row in enumerate(a)]
    for j in range(n):
        k = next(k for k in range(j, n) if b[k][j])
        b[j], b[k] = b[k], b[j]
        pivot = b[j][j]
        b[j] = [x / pivot for x in b[j]]
        for k in range(n):
            if k != j and b[k][j]:
                factor = b[k][j]
                b[k] = [x - factor * y for x, y in zip(b[k], b[j])]
    return [row[n:] for row in b]


def mul(a, b):
    # Sparse enough for the small independent matrix checks below.
    out = [[F(0) for _ in b[0]] for _ in a]
    for i, row in enumerate(a):
        for k, x in enumerate(row):
            if x:
                for j, y in enumerate(b[k]):
                    if y:
                        out[i][j] += x * y
    return out


def tensor_basis(p, r, beta_power=0, distinguished_power=0,
                 rational_p_power=0):
    """Columns evaluated at X_1=pi, X_i=epsilon_i*pi, pi^2=p.

    Source basis: monomials X_S of R = O_K tensor ... tensor O_K.
    Multiply by (product X_i)^beta_power, X_1^distinguished_power,
    and p^rational_p_power.  Rows are (1,pi) in each field component.
    """
    d, components = 2 ** r, 2 ** (r - 1)
    out = [[F(0) for _ in range(d)] for _ in range(d)]
    for eps in range(components):
        for subset in range(d):
            degree = subset.bit_count() + beta_power * r + distinguished_power
            sign_mask = (subset >> 1) ^ (((1 << (r - 1)) - 1)
                                         if beta_power % 2 else 0)
            sign = -1 if (sign_mask & eps).bit_count() % 2 else 1
            out[2 * eps + (degree % 2)][subset] = (
                sign * F(p) ** (degree // 2 + rational_p_power))
    return out


def ideal_basis(p, r, exponent):
    """The lattice pi^exponent O_E in the same field-component coordinates."""
    d = 2 ** r
    out = [[F(0) for _ in range(d)] for _ in range(d)]
    for component in range(2 ** (r - 1)):
        for parity in (0, 1):
            degree = exponent + parity
            out[2 * component + degree % 2][2 * component + parity] = (
                F(p) ** (degree // 2))
    return out


def content(relative_basis, p):
    return min(vp(x, p) for row in relative_basis for x in row if x)


def hull_exponents(basis, p):
    # v_pi(a+b*pi)=min(2*v_p(a), 2*v_p(b)+1); parity rules out cancellation.
    out = []
    for component in range(len(basis) // 2):
        values = []
        for j in range(len(basis[0])):
            for parity in (0, 1):
                x = basis[2 * component + parity][j]
                if x:
                    values.append(2 * vp(x, p) + parity)
        out.append(min(values))
    return out


def main():
    checks = []
    for p in (5, 7, 11):
        for r in range(1, 5):
            log_basis = tensor_basis(p, r, beta_power=1)
            inv_log = inverse(log_basis)
            assert hull_exponents(log_basis, p) == [r] * (2 ** (r - 1))
            shell_basis = tensor_basis(p, r, beta_power=1, rational_p_power=-r)
            assert hull_exponents(shell_basis, p) == [-r] * (2 ** (r - 1))
            # Verify the sharp conductor: pi^(2r-1) O_E lies in L,
            # while pi^(2r-2) O_E does not.
            assert content(mul(inv_log, ideal_basis(p, r, 2*r-1)), p) == 0
            assert content(mul(inv_log, ideal_basis(p, r, 2*r-2)), p) == -1
            for m in range(-5, 13):
                ideal_coordinates = mul(inv_log, ideal_basis(p, r, m))
                ideal_t = content(ideal_coordinates, p)
                assert ideal_t == (m - 2*r + 1) // 2
                output_basis = tensor_basis(p, r, beta_power=1,
                                            distinguished_power=m,
                                            rational_p_power=-r)
                output_t = content(mul(inv_log, output_basis), p)
                assert output_t == m // 2 - r
                assert hull_exponents(output_basis, p) == [m-r] * (2 ** (r - 1))
                # An early O_E-hull can cause strict artificial enlargement
                # when a later lattice automorphism is allowed.
                premature_t = content(mul(inv_log, ideal_basis(p, r, m-r)), p)
                correct_exponent = 2*output_t + r
                premature_exponent = 2*premature_t + r
                assert premature_exponent <= correct_exponent
                checks.append({"p": p, "r": r, "m": m,
                               "ideal_content": ideal_t,
                               "shell_image_content": output_t,
                               "correct_outer_hull_exponent": correct_exponent,
                               "premature_hull_exponent": premature_exponent})

    averages = []
    for ell in (5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43):
        jmax = (ell - 1) // 2
        mean_j2 = F(sum(j*j for j in range(1, jmax + 1)), jmax)
        mean_factors = F(sum(j+1 for j in range(1, jmax + 1)), jmax)
        assert mean_j2 == F(ell*(ell+1), 12)
        assert mean_factors == F(ell+5, 4)
        assert mean_j2 / (2*ell) == F(ell+1, 24)
        averages.append({"ell": ell, "mean_j_squared": str(mean_j2),
                         "mean_tensor_factors": str(mean_factors),
                         "raw_Tate_q_coefficient": str(mean_j2/(2*ell))})

    # A true local Tate parameter and a 20-factor packet, with symbolic proof
    # giving the large-dimensional certificate rather than allocating it.
    p, ell, r, j, n = 821, 41, 20, 19, 1
    assert all(p % divisor for divisor in range(2, 29))
    assert (p-1) % (4*ell) == 0  # mu_(4ell) already lies in Q_p.
    m = n*j*j
    smith = [{"pi_exponent": s, "multiplicity": comb(r-1, s)}
             for s in range(r)]
    assert sum(item["multiplicity"] for item in smith) == 2**(r-1)
    assert sum(item["pi_exponent"]*item["multiplicity"] for item in smith) == (r-1)*2**(r-2)
    correct = 2*(m//2-r)+r
    premature = 2*((m-3*r+1)//2)+r
    assert (m, correct, premature) == (361, 340, 322)
    assert F(correct-premature, 2) == 9
    large_packet = {
        "p": p, "ell": ell, "tensor_factors": r, "j": j,
        "field": "K=Q_821(pi), pi^2=821",
        "local_Tate_q": "821^41", "q_hat": "pi",
        "Qp_dimension": 2**r, "field_components": 2**(r-1),
        "R_in_OE_Smith_over_OK": smith,
        "native_Gaussian_hull_exponent": m,
        "shell_image_hull_exponent": m-r,
        "full_GL_outer_hull_exponent": correct,
        "premature_hull_then_full_GL_exponent": premature,
        "artificial_gain_in_units_of_log_p": "9",
        "source_scope": "local packet only; no complete initial Theta-data certificate"
    }

    jmax = (ell - 1) // 2
    outer_coefficient = F(sum(-(n*a*a) + (a+1) + (n*a*a % 2)
                              for a in range(1, jmax + 1)), 2*jmax)
    native_q_coefficient = F(-n, 2)
    assert outer_coefficient == F(-263, 4)
    assert native_q_coefficient - outer_coefficient == F(261, 4)
    local_procession = {
        "scope": "uniform quadratic local blocks, not a global source certificate",
        "p": p, "ell": ell, "q_hat_pi_valuation": n,
        "full_GL_shell_outer_volume_in_log_p": str(outer_coefficient),
        "native_q_local_volume_in_log_p": str(native_q_coefficient),
        "remaining_local_deficit_in_log_p": str(native_q_coefficient - outer_coefficient),
        "outer_hull_witnesses_are_not_claimed_source_admissible": True
    }

    result = {
        "task": "C9-EVALUATION-DEFECT-ATTACK-20261024",
        "arithmetic": "exact rational matrices; logarithmic coefficients symbolic",
        "matrix_case_count": len(checks), "matrix_checks": checks,
        "procession_averages": averages,
        "twenty_factor_packet": large_packet,
        "uniform_local_procession": local_procession,
        "checks_passed": True,
        "whole_IUT_source_coverage_proved": False,
        "formal_kernel_checked": False,
    }
    destination = Path(__file__).with_name("C9-EVALUATION-DEFECT-CERTIFICATE-20261024.json")
    destination.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"matrix_cases": len(checks), "procession_cases": len(averages),
                      "large_dimension": 2**r, "all_assertions_passed": True,
                      "certificate": str(destination)}, ensure_ascii=False))


if __name__ == "__main__":
    main()
