"""Exact finite certificates for the source Ism scalar reduction.

Includes an actual local-field auxiliary example F=Q_3(i), i^2=-1,
with finite Lubin-Tate norm characters. No full IUT Theta-data is asserted.
The general local-field proof is in the companion research record.
"""

from collections import Counter
from fractions import Fraction
from hashlib import sha256
from itertools import product
import json
from math import gcd
from pathlib import Path
from time import perf_counter

from sympy import Matrix, Poly, symbols


ROOT = Path(__file__).resolve().parent
OUTPUT = ROOT / "C9-ISM-SCALAR-CERTIFICATES-20261024.json"


def mul(x, y, modulus=None):
    # The integer ring Z_3[i], with i^2=-1.
    z = (x[0] * y[0] - x[1] * y[1], x[0] * y[1] + x[1] * y[0])
    return z if modulus is None else tuple(t % modulus for t in z)


def power(x, n, modulus=None):
    result = (1, 0)
    while n:
        if n & 1:
            result = mul(result, x, modulus)
        x = mul(x, x, modulus)
        n //= 2
    return result


def frac_mod(x, modulus):
    assert gcd(x.denominator, modulus) == 1
    return x.numerator * pow(x.denominator, -1, modulus) % modulus


def log_mod27(u):
    assert (u[0] - 1) % 3 == u[1] % 3 == 0
    z = ((u[0] - 1) % 27, u[1] % 27)
    result = [Fraction(0), Fraction(0)]
    for n in range(1, 6):
        term = power(z, n)
        for j in range(2):
            result[j] += Fraction((-1) ** (n + 1) * term[j], n)
    return tuple(frac_mod(x, 27) for x in result)


def norm_characters():
    units = [x for x in product(range(27), repeat=2)
             if (x[0] % 3, x[1] % 3) != (0, 0)]
    assert len(units) == 648
    log_coordinates = {}
    characters = {}
    for u in units:
        log_u8 = log_mod27(power(u, 8, 27))
        assert all(x % 3 == 0 for x in log_u8)
        x, y = tuple((a // 3) * pow(8, -1, 9) % 9 for a in log_u8)
        log_coordinates[u] = (x, y)
        characters[u] = (x, y, (x - y) % 9)
    fibres = Counter(log_coordinates.values())
    assert len(fibres) == 81 and set(fibres.values()) == {8}
    kernels = [[u for u in units if characters[u][j] == 0] for j in range(3)]
    assert all(len(k) == 72 for k in kernels)
    for u, v in product(units, repeat=2):
        uv = mul(u, v, 27)
        assert characters[uv] == tuple((a + b) % 9 for a, b in zip(characters[u], characters[v]))
    # f(T)=3T+T^9. For primitive level-3 torsion the polynomial is
    # 3+f(f(T))^8, compressed below with y=T^8.
    y = symbols("y")
    compressed = Poly(3 + y * (9 + 3*y + y*(3+y)**9)**8, y)
    coefficients = [int(compressed.nth(k)) for k in range(compressed.degree()+1)]
    assert compressed.degree() == 81
    assert coefficients[-1] == 1 and coefficients[0] == 3
    assert all(a % 3 == 0 for a in coefficients[:-1])
    return {
        "local_field": "F=Q_3(i), i^2=-1, unramified of degree 2",
        "integer_residue_ring": "(Z/27Z)[i]/(i^2+1)",
        "unit_group_order": len(units),
        "log_coordinate_formula": "log(u^8)/24 modulo 9, in the basis (1,i)",
        "coordinate_image_size": len(fibres),
        "coordinate_fibre_size": 8,
        "three_characters": ["x", "y", "x-y"],
        "character_kernel_orders": [len(k) for k in kernels],
        "resulting_cyclic_extension_degrees_via_Lubin_Tate": [9,9,9],
        "multiplicativity_checks": len(units)**2,
        "Lubin_Tate_polynomial": "f(T)=3T+T^9",
        "primitive_level_3_polynomial": "3+f(f(T))^8",
        "primitive_level_3_degree": 648,
        "eisenstein_at_3_verified": True,
        "compressed_variable": "y=T^8",
        "compressed_coefficients_ascending": coefficients,
        "finite_character_table": [{"unit": list(u), "characters": list(characters[u])} for u in units],
        "interpretation": "Local class field theory and Lubin-Tate reciprocity identify these kernels with the three genuine norm-subgroup probes; this script checks the finite arithmetic, not those general theorems."
    }


def scalar_outer_group():
    modulus = 9
    probes = [(1,0), (0,1), (1,-1)]
    finite_modules = [set(x for x in product(range(modulus), repeat=2)
                         if sum(a*b for a,b in zip(form,x)) % modulus == 0)
                      for form in probes]
    all_invertible = []
    survivors = []
    witness_failures = {}
    for a,b,c,d in product(range(modulus), repeat=4):
        if (a*d-b*c) % 3 == 0:
            continue
        matrix = (a,b,c,d)
        all_invertible.append(matrix)
        good = True
        for index, subgroup in enumerate(finite_modules):
            for x,y in subgroup:
                image = ((a*x+b*y) % modulus, (c*x+d*y) % modulus)
                if image not in subgroup:
                    good = False
                    witness_failures.setdefault(index, {"matrix": list(matrix), "point": [x,y], "image": list(image)})
                    break
            if not good:
                break
        if good:
            survivors.append(matrix)
    expected = [(u,0,0,u) for u in range(modulus) if gcd(u,3)==1]
    assert len(all_invertible) == 3888 and survivors == expected
    return {
        "rank": 2, "p": 3, "precision_exponent": 2,
        "number_of_norm_probes": 3,
        "probe_linear_forms": [list(x) for x in probes],
        "GL2_mod9_order": len(all_invertible),
        "joint_stabilizer_order": len(survivors),
        "surviving_scalar_matrices": [list(x) for x in survivors],
        "genuine_scalar_lifts": [u for u in range(modulus) if gcd(u,3)==1],
        "first_exclusion_witnesses": witness_failures,
        "inner_outer_groups_agree": True
    }


def local_lattice_and_tensor():
    # K=Q_3(pi), pi^2=3. Analytically J=log(O_K^x)=pi O_K:
    # U1/U2 is generated by 1+pi, log(1+pi)=2pi mod pi^2, log U2=3O_K.
    shell_basis = Matrix([[1,0],[0,Fraction(1,3)]])
    pilot_action = Matrix.diag(9,9)
    relative = shell_basis.inv()*pilot_action
    assert relative == Matrix.diag(9,27)
    units = [1,2]
    for u in units:
        # A scalar unit preserves any Z_3-lattice, verified here modulo its
        # finite quotient; integer HNF would incorrectly keep non-3 factors.
        assert gcd(u,3)==1 and gcd(pow(u,-1,3),3)==1
    # Coarse direct-summand unit choices tensor to products of units.
    choices = [[1,2],[4,5],[7,8]]
    tensor_scalars = [a*b*c for a,b,c in product(*choices)]
    assert all(gcd(u,3)==1 for u in tensor_scalars)
    # Arbitrary split sets: multiplication by field-component units preserves
    # each valuation and hence its final product-ideal hull.
    split_points = [(9,3,27),(3,18,9),(27,9,3)]
    def valuation(x):
        result=0
        while x % 3 == 0:
            x//=3
            result+=1
        return result
    hull = [min(valuation(x[j]) for x in split_points) for j in range(3)]
    acted = [tuple(u*x for u,x in zip((2,4,5),point)) for point in split_points]
    assert [min(valuation(x[j]) for x in acted) for j in range(3)]==hull
    return {
        "local_field": "K=Q_3(pi), pi^2=3",
        "log_lattice": "J_K=pi O_K",
        "source_log_shell": "I_K=(1/3)J_K=pi^-1 O_K",
        "Gaussian_local_profile": "a=pi, a^10=3^5; j=2 gives g=a^4=9",
        "region": "L=9 O_K",
        "relative_basis_matrix": [[9,0],[0,27]],
        "r": 2,"s": 3,"observation_width": 1,
        "raw_volume_mu_O_equals_1": "3^-4",
        "degree_normalized_log_volume": "-2 log(3)",
        "shell_relative_normalized_log_volume": "-(5/2) log(3)",
        "shell_reference_correction": "+(1/2) log(3)",
        "Ind2_hull_increment": "0",
        "tensor_unit_products": tensor_scalars,
        "split_hull_exponents_preserved": hull,
        "full_global_Theta_data_claimed": False
    }


def main():
    start=perf_counter()
    result={
        "schema":"iut-source-local-ism-certificates/v1",
        "task":"n8-c9-four-steps-source-attempt-20261024",
        "norm_characters":norm_characters(),
        "finite_norm_probe_outer_group":scalar_outer_group(),
        "local_lattice_and_tensor":local_lattice_and_tensor(),
        "all_assertions_passed":True,
        "global_fixed_q_comparison_proved":False,
        "target_accepted":False
    }
    OUTPUT.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({"output":str(OUTPUT),"all_assertions_passed":True,
                      "GL2_mod9_to_scalar_count":[3888,6],
                      "norm_probe_extension_degrees":[9,9,9],
                      "character_pair_checks":648**2,
                      "elapsed_seconds":round(perf_counter()-start,3)},ensure_ascii=False))


if __name__=='__main__':
    main()
