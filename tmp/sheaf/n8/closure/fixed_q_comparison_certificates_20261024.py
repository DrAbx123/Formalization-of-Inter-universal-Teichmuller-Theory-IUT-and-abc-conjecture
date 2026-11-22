"""Exact diagnostic certificates for the natural-language fixed-q investigation.

This is not an IUT implementation.  The graph and matrix inputs below are
explicit donor models, NOT source-qualified Theta-data or output branches.
General statements and their proofs are in the adjacent research record.
No floating-point value is used to decide any sign or equality.
"""

from fractions import Fraction
from itertools import product
import hashlib
import json
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parent
OUT = ROOT / "C9-FIXED-Q-EXACT-CERTIFICATES-20261024.json"


def qs(x):
    return str(sp.Rational(x))


def vec(xs):
    return [qs(x) for x in xs]


def flow_certificate(n, edges, resistances, charge):
    """Produce B f=d and R f=B^t u; both are exact and cheap to verify."""
    B = sp.zeros(n, len(edges))
    for e, (source, target) in enumerate(edges):
        B[source, e] = 1
        B[target, e] = -1
    R = sp.diag(*resistances)
    lap = B * sp.diag(*(sp.Rational(1, r) for r in resistances)) * B.T
    u = sp.Matrix(list(lap[: n - 1, : n - 1].inv() * charge[: n - 1, 0]) + [0])
    f = sp.diag(*(sp.Rational(1, r) for r in resistances)) * B.T * u
    assert B * f == charge
    assert R * f == B.T * u
    energy = (f.T * R * f)[0]
    assert energy == (charge.T * u)[0]
    return f, energy, {
        "resistances": resistances,
        "flow": vec(f),
        "potential": vec(u),
        "energy": qs(energy),
    }


def multilayer_energy():
    # Twenty independently varying length vectors on a fixed connected graph.
    n = 8
    edges = [(i, (i + 1) % n) for i in range(n)] + [
        (i, (i + 3) % n) for i in range(n)
    ]
    charge = sp.Matrix([1, 0, 0, 0, -1, 0, 0, 0])
    layers = [
        [1 + ((a + 3) * (e + 5) + a * e * e) % 17 for e in range(len(edges))]
        for a in range(20)
    ]
    total = [sum(r[e] for r in layers) for e in range(len(edges))]
    total_f, total_energy, total_cert = flow_certificate(n, edges, total, charge)
    certificates = []
    energies = []
    sos = sp.Rational(0)
    for r in layers:
        f, energy, cert = flow_certificate(n, edges, r, charge)
        energies.append(energy)
        certificates.append(cert)
        terms = [r[e] * (total_f[e] - f[e]) ** 2 for e in range(len(edges))]
        assert all(t >= 0 for t in terms)
        sos += sum(terms)
    jump = total_energy - sum(energies)
    assert jump == sos and jump > 0

    # A separate exact negative control: adding homothetic layers gives zero.
    base = list(range(1, len(edges) + 1))
    base_f, base_energy, _ = flow_certificate(n, edges, base, charge)
    scales = list(range(1, 21))
    hom_f, hom_energy, _ = flow_certificate(
        n, edges, [sum(scales) * r for r in base], charge
    )
    assert hom_f == base_f
    assert hom_energy - sum(scales) * base_energy == 0
    return {
        "scope": "exact graph-energy donor; no IUT defect identification asserted",
        "vertices": n,
        "edges": edges,
        "charge": vec(charge),
        "layers": certificates,
        "total": total_cert,
        "square_terms": 20 * len(edges),
        "jump": qs(jump),
        "sos": qs(sos),
        "positive_exact": bool(jump > 0),
        "homothetic_twenty_layer_jump": "0",
    }


def two_edge_identity():
    a = list(range(1, 21))
    b = [k * k + 1 for k in a]
    s = [x + y for x, y in zip(a, b)]
    total = sum(s)
    lhs = Fraction(sum(a) * sum(b), total) - sum(
        (Fraction(x * y, x + y) for x, y in zip(a, b)), Fraction(0)
    )
    summands = [
        Fraction((a[i] * b[j] - a[j] * b[i]) ** 2, total * s[i] * s[j])
        for i in range(20)
        for j in range(i + 1, 20)
    ]
    assert len(summands) == 190
    assert lhs == sum(summands, Fraction(0)) and lhs > 0
    return {
        "scope": "specialization of universally proved weighted-variance identity",
        "a": a,
        "b": b,
        "pair_terms": len(summands),
        "lhs": str(lhs),
        "rhs": str(sum(summands, Fraction(0))),
    }


def centralizer_diagnostic():
    p = 3
    vectors = [(0, y) for y in range(p)]
    gl = []
    centralizer = []
    for a, b, c, d in product(range(p), repeat=4):
        if (a * d - b * c) % p == 0:
            continue
        matrix = (a, b, c, d)
        gl.append(matrix)
        # Commutation with diag(1,-1) over F_3 is b=c=0.
        if b == 0 and c == 0:
            centralizer.append(matrix)

    def orbit_union(matrices):
        return sorted(
            {
                ((a * x + b * y) % p, (c * x + d * y) % p)
                for a, b, c, d in matrices
                for x, y in vectors
            }
        )

    actual = orbit_union(centralizer)
    enlarged = orbit_union(gl)
    assert len(centralizer) == 4 and len(gl) == 48
    assert len(actual) == 3 and len(enlarged) == 9
    return {
        "scope": "finite representation diagnostic, NOT the source Ism group",
        "prime": p,
        "representation_generator": [[1, 0], [0, -1]],
        "lattice_over_Z3": "3 Z_3 x Z_3",
        "centralizer_mod_3_size": len(centralizer),
        "GL2_mod_3_size": len(gl),
        "centralizer_union": actual,
        "unrestricted_union": enlarged,
        "p_adic_hull_exponents_centralizer": [1, 0],
        "p_adic_hull_exponents_unrestricted_GL": [0, 0],
    }


def valuation(x, p):
    x = sp.Rational(x)
    if x == 0:
        return None
    n, d = abs(int(x.p)), int(x.q)
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    while d % p == 0:
        d //= p
        v -= 1
    return v


def finite_hull_certificate():
    # Exact split-etale Q_3^4 model. Each column belongs to a specified lattice.
    # This tests extraction of witnesses, without claiming source admissibility.
    p = 3
    matrices = [
        sp.diag(3**4, 3**2, 3**5, 3),
        sp.Matrix([[3**3, 0, 0, 0], [3, 3**2, 0, 0], [0, 0, 3**4, 0], [0, 0, 0, 3**2]]),
        sp.Matrix([[3**2, 0, 0, 0], [0, 3**3, 0, 0], [0, 3, 3**2, 0], [0, 0, 0, 1]]),
    ]
    witnesses = []
    exponents = []
    for row in range(4):
        choices = [
            (valuation(A[row, col], p), branch, col)
            for branch, A in enumerate(matrices)
            for col in range(4)
            if A[row, col] != 0
        ]
        exponent, branch, col = min(choices)
        exponents.append(exponent)
        witnesses.append(
            {"component": row, "branch": branch, "column": col,
             "point": vec(matrices[branch][:, col]), "valuation": exponent}
        )
    assert exponents == [2, 1, 1, 0]
    return {
        "scope": "finite-hull extraction in a split algebra; no source input supplied",
        "prime": p,
        "lattice_matrices": [[[qs(x) for x in row] for row in A.tolist()] for A in matrices],
        "hull_exponents": exponents,
        "component_witnesses": witnesses,
        "unnormalized_log_volume_coefficient_of_log_3": -sum(exponents),
        "singleton_measure_used": False,
    }


def verify_saved_graph(cert):
    n, edges = cert["vertices"], cert["edges"]
    B = sp.zeros(n, len(edges))
    for e, (source, target) in enumerate(edges):
        B[source, e], B[target, e] = 1, -1
    d = sp.Matrix([sp.Rational(x) for x in cert["charge"]])
    energy_sum = sp.Rational(0)
    total_f = sp.Matrix([sp.Rational(x) for x in cert["total"]["flow"]])
    sos = sp.Rational(0)
    for block in cert["layers"] + [cert["total"]]:
        R = sp.diag(*block["resistances"])
        f = sp.Matrix([sp.Rational(x) for x in block["flow"]])
        u = sp.Matrix([sp.Rational(x) for x in block["potential"]])
        assert B * f == d and R * f == B.T * u
        assert (f.T * R * f)[0] == sp.Rational(block["energy"])
    for block in cert["layers"]:
        energy_sum += sp.Rational(block["energy"])
        f = sp.Matrix([sp.Rational(x) for x in block["flow"]])
        for e, r in enumerate(block["resistances"]):
            sos += r * (total_f[e] - f[e]) ** 2
    assert sp.Rational(cert["total"]["energy"]) - energy_sum == sos
    assert sos == sp.Rational(cert["jump"]) and sos > 0


def main():
    result = {
        "status": "exact donor/model certificates only; fixed-q source comparison remains open",
        "graph_energy": multilayer_energy(),
        "two_edge_variance": two_edge_identity(),
        "galois_centralizer_diagnostic": centralizer_diagnostic(),
        "finite_hull": finite_hull_certificate(),
        "Lean_checks": "not_run",
        "target_accepted": False,
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    saved = json.loads(OUT.read_text(encoding="utf-8"))
    verify_saved_graph(saved["graph_energy"])
    print(json.dumps({
        "output": OUT.as_posix(),
        "sha256": hashlib.sha256(OUT.read_bytes()).hexdigest(),
        "graph_layers": len(saved["graph_energy"]["layers"]),
        "graph_square_terms": saved["graph_energy"]["square_terms"],
        "graph_positive_exact": saved["graph_energy"]["positive_exact"],
        "homothetic_jump": saved["graph_energy"]["homothetic_twenty_layer_jump"],
        "two_edge_pair_terms": saved["two_edge_variance"]["pair_terms"],
        "finite_hull_exponents": saved["finite_hull"]["hull_exponents"],
        "source_theorem_proved": False,
    }, indent=2))


if __name__ == "__main__":
    main()
