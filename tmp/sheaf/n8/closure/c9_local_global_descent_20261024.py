"""Exact arithmetic checks for the local/global Frobenioid distinction.

All coordinates below are in units of log(3), with two places: 3 and infinity.
This checks an arithmetic submodel, not a complete IUT output realization.
The proofs for arbitrary number fields/towers are in the accompanying record.
"""

from dataclasses import dataclass
from fractions import Fraction as Q
import json
from pathlib import Path


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def scale(n, a):
    return tuple(n * x for x in a)


def degree(a):
    return sum(a, Q(0))


@dataclass(frozen=True)
class LocalComparison:
    source: tuple
    target: tuple
    frobenius_degree: int
    local_multiplier_divisor: tuple
    effective_zero_divisor: tuple

    def verify(self):
        assert self.frobenius_degree >= 1
        assert all(z >= 0 for z in self.effective_zero_divisor)
        assert add(scale(self.frobenius_degree, self.source),
                   self.effective_zero_divisor) == add(
                       self.target, self.local_multiplier_divisor)
        assert degree(self.target) - self.frobenius_degree * degree(self.source) == (
            degree(self.effective_zero_divisor)
            - degree(self.local_multiplier_divisor))

    def as_dict(self):
        self.verify()
        return {
            "source": list(self.source),
            "target": list(self.target),
            "frobenius_degree": self.frobenius_degree,
            "local_multiplier_divisor": list(self.local_multiplier_divisor),
            "effective_zero_divisor": list(self.effective_zero_divisor),
            "defect": degree(self.local_multiplier_divisor),
            "source_volume": degree(self.source),
            "target_volume": degree(self.target),
        }


def then(first, second):
    assert first.target == second.source
    result = LocalComparison(
        first.source, second.target,
        first.frobenius_degree * second.frobenius_degree,
        add(second.local_multiplier_divisor,
            scale(second.frobenius_degree, first.local_multiplier_divisor)),
        add(second.effective_zero_divisor,
            scale(second.frobenius_degree, first.effective_zero_divisor)),
    )
    result.verify()
    return result


def main():
    source = (-1, 0)  # 3 Z_3; radius 1 at infinity
    small = (-2, 0)   # 9 Z_3; radius 1 at infinity
    zero = (0, 0)
    principal_three = (1, -1)
    assert degree(principal_three) == 0

    # Locally: multiply by 3 at the place 3, and by 1 at infinity.
    local_only = LocalComparison(source, small, 1, (1, 0), zero)
    local_only.verify()
    assert degree(small) - degree(source) == -1
    assert degree(local_only.local_multiplier_divisor) == 1

    # A dual obstruction to ANY global linear arrow with these endpoints:
    # principal divisors have degree 0; its required effective divisor would
    # have degree -1. This is not a search over finitely many multipliers.
    global_linear_obstruction = {
        "dual_degree_vector": [1, 1],
        "principal_generator": list(principal_three),
        "dual_on_principal_generator": 0,
        "required_degree_of_effective_divisor": -1,
        "effective_divisor_degree_lower_bound": 0,
    }

    # A degree-2 morphism exists, but compares 2Q with h, not Q with h.
    frobenius_two = LocalComparison(source, small, 2, zero, zero)
    frobenius_two.verify()

    # Enlarging the archimedean radius to 3 supplies the missing compensation.
    repaired = LocalComparison(source, (-2, 1), 1, principal_three, zero)
    repaired.verify()
    assert degree(repaired.target) == degree(source)

    # A genuine global isomorphism after the bad local comparison preserves
    # its defect. It does not create a global descent of the composite.
    global_next = LocalComparison(small, (-3, 1), 1, principal_three, zero)
    composite = then(local_only, global_next)
    assert degree(composite.local_multiplier_divisor) == 1

    # Check the Frobenius weight in the actual model composition law.
    square_next = LocalComparison(small, (-4, 0), 2, zero, zero)
    square_composite = then(local_only, square_next)
    assert square_composite.local_multiplier_divisor == (2, 0)
    assert square_composite.frobenius_degree == 2

    # Simultaneous tensor powers and unnormalized base-change degrees must
    # be divided back by the SAME factors in the original normalization.
    normalized_checks = []
    for tensor_power in (1, 2, 3, 5, 12):
        for extension_degree in (1, 2, 3, 6):
            factor = tensor_power * extension_degree
            scaled_defect = factor * degree(local_only.local_multiplier_divisor)
            normalized_defect = Q(scaled_defect, factor)
            assert normalized_defect == 1
            normalized_checks.append({
                "tensor_power": tensor_power,
                "extension_degree": extension_degree,
                "normalized_defect": normalized_defect,
            })

    certificate = {
        "task": "C9-LOCAL-GLOBAL-DESCENT-ATTACK-20261024",
        "scope": "Exact arithmetic line/Frobenioid submodel; not full initial Theta-data",
        "coordinate_unit": "log(3)",
        "places": ["3", "infinity"],
        "local_only_comparison": local_only.as_dict(),
        "global_linear_dual_obstruction": global_linear_obstruction,
        "frobenius_degree_two_arrow": frobenius_two.as_dict(),
        "archimedean_repair": repaired.as_dict(),
        "composition_with_global_isomorphism": composite.as_dict(),
        "composition_with_frobenius_degree_two": square_composite.as_dict(),
        "normalization_checks": normalized_checks,
        "all_assertions_passed": True,
        "infinite_tower_claim": "Proved in natural language; not inferred from enumeration",
        "actual_IUT_refutation_certificate": False,
        "target_accepted": False,
    }
    output = Path(__file__).with_name("C9-LOCAL-GLOBAL-DESCENT-CERTIFICATE-20261024.json")
    output.write_text(json.dumps(certificate, ensure_ascii=False, indent=2,
                                 default=str) + "\n", encoding="utf-8")
    print(json.dumps({"certificate": str(output), "all_assertions_passed": True,
                      "normalization_cases": len(normalized_checks),
                      "target_accepted": False}, ensure_ascii=False))


if __name__ == "__main__":
    main()
