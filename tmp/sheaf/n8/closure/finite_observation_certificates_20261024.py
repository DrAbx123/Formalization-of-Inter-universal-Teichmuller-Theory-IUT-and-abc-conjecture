"""Exact certificates for finite-observation lemmas; not IUT source instances.

Run: python tmp/sheaf/n8/closure/finite_observation_certificates_20261024.py
Only integer/rational arithmetic is used. General statements are proved in the
companion Markdown record; these finite examples check the constructions.
"""

from fractions import Fraction
from hashlib import sha256
from itertools import product
import json
from math import factorial, gcd
from pathlib import Path
import time

import sympy
from sympy import Matrix, eye, zeros, ZZ
from sympy.matrices.normalforms import hermite_normal_form, smith_normal_form
from sympy.polys.matrices import DomainMatrix
from sympy.polys.matrices.normalforms import smith_normal_decomp


BASE = Path(__file__).resolve().parent
OUT = BASE / "C9-FINITE-OBSERVATION-CERTIFICATES-20261024.json"


def matrix_rows(a):
    return [[int(x) for x in row] for row in a.tolist()]


def vp(a, p):
    a = abs(int(a))
    if a == 0:
        return None
    n = 0
    while a % p == 0:
        n += 1
        a //= p
    return n


def lattice_sum(*matrices):
    return hermite_normal_form(Matrix.hstack(*matrices))


def split_hull_exponents(basis, p):
    return [min(vp(x, p) for x in basis.row(i) if x != 0)
            for i in range(basis.rows)]


def saturate(basis, generators, p, bound):
    current = hermite_normal_form(basis)
    history = [{"iteration": 0, "index_exponent": vp(current.det(), p),
                "hull_exponents": split_hull_exponents(current, p)}]
    for iteration in range(1, bound + 2):
        nxt = lattice_sum(current, *(g * current for g in generators))
        if nxt == current:
            return current, history, iteration
        current = nxt
        history.append({"iteration": iteration,
                        "index_exponent": vp(current.det(), p),
                        "hull_exponents": split_hull_exponents(current, p)})
    raise AssertionError("Saturation exceeded the proved length bound")


def early_hull_and_sandwich():
    p = 3
    lattice = Matrix([[1, p], [1, 0]])
    transform = Matrix([[1, -1], [0, 1]])
    outer_generator = Matrix([[1, 1], [0, 1]])
    inner = hermite_normal_form(lattice)
    outer, history, _ = saturate(lattice, [outer_generator], p, 2)
    assert outer == eye(2) and abs(inner.det()) == p
    assert split_hull_exponents(inner, p) == [0, 0]
    assert split_hull_exponents(transform * inner, p) == [1, 0]
    assert split_hull_exponents(transform * eye(2), p) == [0, 0]
    return {
        "p": p, "initial_basis": matrix_rows(lattice),
        "linear_map": matrix_rows(transform),
        "inner_module_basis": matrix_rows(inner),
        "outer_generator": matrix_rows(outer_generator),
        "outer_module_basis": matrix_rows(outer),
        "inner_and_outer_final_hull_exponents": [0, 0],
        "hull_after_actual_linear_map": [1, 0],
        "hull_after_premature_hull_then_map": [0, 0],
        "outer_saturation": history,
        "conclusion": "Final hull equality can certify an observation even when modules differ; early holomorphic hull is unsound for later linear maps."
    }


def orbit_saturation():
    p, d, width = 3, 20, 3
    initial = Matrix.diag(1, *([p ** width] * (d - 1)))
    cycle = zeros(d)
    for i in range(d):
        cycle[(i + 1) % d, i] = 1
    sharp_bound = vp(initial.det(), p)
    final, history, stationary_test = saturate(initial, [cycle], p, sharp_bound)
    assert final == eye(d)
    assert len(history) - 1 == d - 1
    direct_orbit = lattice_sum(*(cycle ** i * initial for i in range(d)))
    assert direct_orbit == final
    residues = {tuple(int(x) % (p ** width) for x in cycle ** i)
                for i in range(d)}
    assert len(residues) == d
    # A lift changed by p^width need not be in the actual cyclic group.
    # Its action gives the same lattice sum once the baseline L is retained.
    perturbation = Matrix(d, d, lambda i, j: ((7 * i + 3 * j) % 5) - 2)
    changed_lift = cycle + p ** width * perturbation
    assert int(changed_lift.det()) % p != 0
    assert ((changed_lift - cycle) * initial).applyfunc(lambda x: int(x) % (p ** width)) == zeros(d)
    assert lattice_sum(initial, cycle * initial) == lattice_sum(initial, changed_lift * initial)
    sharp_lattice = Matrix.diag(1, p ** width)
    shallowly_equal_map = Matrix([[1, 0], [p ** (width - 1), 1]])
    assert split_hull_exponents(sharp_lattice, p) == [0, width]
    assert split_hull_exponents(shallowly_equal_map * sharp_lattice, p) == [0, width - 1]
    # Pure homothety leaves the required observation width unchanged.
    scalar_exponent = 37
    scaled_r, scaled_s = scalar_exponent, scalar_exponent + width
    assert scaled_s - scaled_r == width
    return {
        "p": p, "dimension": d, "r": 0, "s": width,
        "observation_modulus": p ** width, "finite_group_image_order": len(residues),
        "initial_diagonal_exponents": [0] + [width] * (d - 1),
        "general_strict_increase_bound": d * width,
        "initial_index_strict_increase_bound": sharp_bound,
        "actual_strict_increases": len(history) - 1,
        "stationary_test_iteration": stationary_test,
        "history": history,
        "final_basis_is_identity": final == eye(d),
        "full_cyclic_orbit_sum_agrees": direct_orbit == final,
        "congruent_lift_preserves_one_step_sum": True,
        "congruent_lift_preserves_whole_Zp_lattice_via_residue_criterion": True,
        "one_less_digit_counterexample": {
            "lattice_diagonal": [1, p ** width],
            "map_congruent_to_identity_modulus": p ** (width - 1),
            "map": matrix_rows(shallowly_equal_map),
            "hull_exponents_before": [0, width],
            "hull_exponents_after": [0, width - 1]
        },
        "homothety_exponent": scalar_exponent,
        "homothety_observation_width": scaled_s - scaled_r,
        "scalar_readout_correction_retained_symbolically": "-37 * log(3) for degree-normalized local log-volume relative to the fixed reference"
    }


def compatibility_matrix(edges, vertices, dimension):
    variables = vertices * dimension ** 2
    result = zeros(len(edges) * dimension ** 2, variables)
    for edge_index, (u, v, a) in enumerate(edges):
        for i, j in product(range(dimension), repeat=2):
            row = edge_index * dimension ** 2 + i * dimension + j
            for k in range(dimension):
                result[row, v * dimension ** 2 + i * dimension + k] += a[k, j]
                result[row, u * dimension ** 2 + k * dimension + j] -= a[i, k]
    return result


def graph_elimination():
    p, layers, torsion_exponent = 3, 20, 4
    frames = [eye(2)]
    for i in range(1, layers):
        a, b = i, i % 4
        frames.append(Matrix([[1, a], [b, 1 + a * b]]))
    holonomy = Matrix([[1, p ** torsion_exponent], [0, 1]])
    edges = [(i, i + 1, frames[i + 1] * frames[i].inv())
             for i in range(layers - 1)]
    edges.append((layers - 1, 0, holonomy * frames[-1].inv()))
    assert all(a.det() == 1 for _, _, a in edges)
    for index, (u, v, a) in enumerate(edges):
        reduced_edge = frames[v].inv() * a * frames[u]
        assert reduced_edge == (eye(2) if index < layers - 1 else holonomy)
    full = compatibility_matrix(edges, layers, 2)
    reduced = compatibility_matrix([(0, 0, holonomy)], 1, 2)
    full_smith = smith_normal_form(full, domain=ZZ)
    dm = DomainMatrix.from_Matrix(reduced).convert_to(ZZ)
    ds, left, right = smith_normal_decomp(dm)
    small_smith, left, right = ds.to_Matrix(), left.to_Matrix(), right.to_Matrix()
    assert left * reduced * right == small_smith
    assert abs(left.det()) == abs(right.det()) == 1
    full_diag = [abs(int(full_smith[i, i])) for i in range(full_smith.rows)]
    small_diag = [abs(int(small_smith[i, i])) for i in range(small_smith.rows)]
    expected = [1] * (4 * (layers - 1)) + [p ** torsion_exponent] * 2 + [0] * 2
    assert full_diag == expected
    assert small_diag == [p ** torsion_exponent] * 2 + [0] * 2
    # Check exact transport of a non-scalar integral invertible centralizer.
    root = Matrix([[1, 2], [0, 1]])
    lifted = [frame * root * frame.inv() for frame in frames]
    assert all(lifted[v] * a == a * lifted[u] for u, v, a in edges)
    return {
        "p": p, "layers": layers, "matrix_dimension_per_vertex": 2,
        "full_compatibility_matrix_shape": list(full.shape),
        "full_scalar_unknowns": full.cols,
        "reduced_compatibility_matrix_shape": list(reduced.shape),
        "reduced_scalar_unknowns": reduced.cols,
        "frames": [matrix_rows(a) for a in frames],
        "edges": [{"from": u, "to": v, "matrix": matrix_rows(a)} for u, v, a in edges],
        "holonomy": matrix_rows(holonomy),
        "full_smith_diagonal": full_diag,
        "reduced_compatibility_matrix": matrix_rows(reduced),
        "reduced_smith_diagonal": small_diag,
        "reduced_smith_left_witness": matrix_rows(left),
        "reduced_smith_right_witness": matrix_rows(right),
        "precision_loss_exponent": torsion_exponent,
        "for_output_precision_exponent_2_compute_constraints_modulus": p ** (2 + torsion_exponent),
        "non_scalar_exact_root_solution": matrix_rows(root),
        "all_20_transported_equations_checked": True,
        "full_matrix_sha256": sha256(json.dumps(matrix_rows(full), separators=(",", ":")).encode()).hexdigest()
    }


def finite_precision_lifting():
    p, n, loss = 3, 2, 2
    observed, sufficient = p ** n, p ** (n + loss)
    coefficients = (9, 27)
    approximate = {(x % observed, y % observed)
                   for x, y in product(range(sufficient), repeat=2)
                   if (coefficients[0] * x + coefficients[1] * y) % sufficient == 0}
    exact = {((-3 * y) % observed, y) for y in range(observed)}
    too_shallow = {(x, y) for x, y in product(range(observed), repeat=2)
                   if (coefficients[0] * x + coefficients[1] * y) % observed == 0}
    assert approximate == exact and len(exact) == 9 and len(too_shallow) == 81
    assert (1, 0) in too_shallow and (1, 0) not in exact
    return {
        "p": p, "linear_equation_coefficients": list(coefficients),
        "output_precision_exponent": n, "smith_loss_exponent": loss,
        "constraint_modulus": sufficient,
        "finite_pairs_exhaustively_examined": sufficient ** 2,
        "projected_approximate_solution_count": len(approximate),
        "exact_kernel_reduction_count": len(exact),
        "too_shallow_solution_count": len(too_shallow),
        "false_shallow_solution": [1, 0],
        "exact_kernel_generator": [-3, 1],
        "projected_solution_set": [list(t) for t in sorted(exact)]
    }


def fraction_mod(a, modulus):
    assert gcd(a.denominator, modulus) == 1
    return a.numerator * pow(a.denominator, -1, modulus) % modulus


def local_log(p, c, n):
    modulus, order = p ** n, 2 * n - 1
    units = list(range(1, modulus, p ** c))
    logs = {}
    for u in units:
        value = sum((Fraction((-1) ** (k + 1) * (u - 1) ** k, k)
                     for k in range(1, order + 1)), Fraction(0))
        logs[u] = fraction_mod(value, modulus)
    assert set(logs.values()) == set(range(0, modulus, p ** c))
    for u, v in product(units, repeat=2):
        assert logs[(u * v) % modulus] == (logs[u] + logs[v]) % modulus
        ud, ld = (u - v) % modulus, (logs[u] - logs[v]) % modulus
        assert (n if ud == 0 else vp(ud, p)) == (n if ld == 0 else vp(ld, p))
    for u in units:
        z = logs[u]
        value = sum((Fraction(z ** k, factorial(k)) for k in range(order + 1)), Fraction(0))
        assert fraction_mod(value, modulus) == u
    return {
        "p": p, "principal_unit_depth": c, "precision_exponent": n,
        "modulus": modulus, "series_last_degree": order,
        "unit_cosets": len(units), "all_pairs_checked": len(units) ** 2,
        "bijection": True, "isometry_modulo_precision": True,
        "multiplicative_to_additive_homomorphism": True, "exp_inverse": True,
        "finite_table": [[u, logs[u]] for u in units]
    }


def delayed_constraint_and_guard():
    p, delay = 3, 100
    initial = Matrix.diag(p, 1)
    swap = Matrix([[0, 1], [1, 0]])
    first_tower_final = lattice_sum(initial, swap * initial)
    second_tower_final = hermite_normal_form(initial)
    assert split_hull_exponents(first_tower_final, p) == [0, 0]
    assert split_hull_exponents(second_tower_final, p) == [1, 0]
    edges = {("start", "middle0"), ("middle1", "finish")}
    quotient = {"start": "start", "middle0": "middle", "middle1": "middle", "finish": "finish"}
    abstract = {(quotient[u], quotient[v]) for u, v in edges}
    concrete_path = any(("start", mid) in edges and (mid, "finish") in edges
                        for mid in quotient)
    abstract_path = ("start", "middle") in abstract and ("middle", "finish") in abstract
    assert not concrete_path and abstract_path
    return {
        "identical_initial_tower_levels": delay,
        "tower_A_groups": "<swap> at every level",
        "tower_B_groups": "<swap> through level 100, identity from level 101",
        "tower_A_final_hull_exponents": [0, 0],
        "tower_B_final_hull_exponents": [1, 0],
        "guard_example_concrete_edges": [list(e) for e in sorted(edges)],
        "guard_example_abstract_edges": [list(e) for e in sorted(abstract)],
        "concrete_two_step_path_exists": concrete_path,
        "abstract_two_step_path_exists": abstract_path,
        "conclusion": "Neither observed finite plateaus nor existential edgewise quotient witnesses justify full-path lifting."
    }


def main():
    started = time.perf_counter()
    result = {
        "schema": "iut-natural-research-exact-certificates/v1",
        "task": "n8-c9-finite-observation-theorems-20261024",
        "source_instances": False,
        "arithmetic": "exact integers and rational numbers; no floating-point mathematical assertions",
        "sympy_version": sympy.__version__,
        "early_hull_and_sandwich": early_hull_and_sandwich(),
        "orbit_saturation": orbit_saturation(),
        "twenty_layer_graph_elimination": graph_elimination(),
        "smith_precision_lifting": finite_precision_lifting(),
        "logarithm_blocks": [local_log(3, 1, 5), local_log(2, 2, 6)],
        "invalid_finite_cutoffs_and_guard_loss": delayed_constraint_and_guard(),
        "all_assertions_passed": True,
        "target_accepted": False
    }
    OUT.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"output": str(OUT), "all_assertions_passed": True,
                      "elapsed_seconds": round(time.perf_counter() - started, 3),
                      "orbit_strict_steps": result["orbit_saturation"]["actual_strict_increases"],
                      "graph_unknowns_before_after": [80, 4],
                      "smith_loss": result["twenty_layer_graph_elimination"]["precision_loss_exponent"],
                      "log_pair_checks": sum(x["all_pairs_checked"] for x in result["logarithm_blocks"])},
                     ensure_ascii=False))


if __name__ == "__main__":
    main()
