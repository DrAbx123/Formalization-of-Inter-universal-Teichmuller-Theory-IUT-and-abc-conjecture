"""Exact certificates for the marked-image/Kummer obstruction investigation.

The arithmetic-line checks use Q with one finite place and its archimedean
place.  They test a category model, not a complete IUT input.  The Kummer checks
test valuations and actual finite cyclic root actions; the all-level statement
is proved separately in the accompanying natural-language record.
"""
from dataclasses import dataclass, asdict
from fractions import Fraction
from pathlib import Path
import json


@dataclass(frozen=True)
class TaggedImage:
    tag_finite: int
    tag_arch: int
    multiplier_finite: int
    multiplier_arch: int

    @property
    def tag_degree(self):
        return self.tag_arch - self.tag_finite

    @property
    def image_finite(self):
        return self.tag_finite + self.multiplier_finite

    @property
    def image_arch(self):
        return self.tag_arch + self.multiplier_arch

    @property
    def image_degree(self):
        return self.image_arch - self.image_finite

    @property
    def defect(self):
        return self.image_degree - self.tag_degree

    def into(self, hull_finite=2, hull_arch=0):
        return self.image_finite >= hull_finite and self.image_arch <= hull_arch


def compatible_global_multiplier(a, b, exponent):
    # The global number 3^exponent has the SAME exponent at 3 and infinity.
    return (
        a.multiplier_finite == b.multiplier_finite + exponent
        and a.multiplier_arch == b.multiplier_arch + exponent
        and a.tag_finite + exponent >= b.tag_finite
        and a.tag_arch + exponent <= b.tag_arch
    )


def r_order(x, r):
    assert x > 0
    k = 0
    while x % r == 0:
        x //= r
        k += 1
    return k


def prime_factor(n):
    for r in range(2, n + 1):
        if n % r == 0:
            return r
    raise AssertionError(n)


def main():
    # A finite portion of a genuinely unbounded family of local images with
    # the SAME q-tag.  Local inclusions do not lift to q-fixed morphisms.
    fixed_q = [TaggedImage(1, 0, n + 1, 0) for n in range(20)]
    assert all(a.into() for a in fixed_q)
    rejected_pairs = 0
    for i, a in enumerate(fixed_q):
        for j, b in enumerate(fixed_q):
            if i != j:
                assert a.defect != b.defect
                # Archimedean compatibility forces the only candidate f=1.
                candidate = a.multiplier_arch - b.multiplier_arch
                assert not compatible_global_multiplier(a, b, candidate)
                rejected_pairs += 1

    # Nontrivial actual morphisms in the arithmetic-line category preserve
    # the defect even while the tag degree and the image degree change.
    path = []
    for i in range(20):
        image_finite = 21-i
        s = (-1)**i * (i*i + 2*i + 1)
        a = TaggedImage(image_finite-s, 1-s, s, s-1)
        assert a.into() and a.defect == -1
        path.append(a)
    edge_certificates = []
    for a, b in zip(path, path[1:]):
        f = a.multiplier_finite - b.multiplier_finite
        assert compatible_global_multiplier(a, b, f)
        assert b.tag_degree-a.tag_degree == b.image_degree-a.image_degree == 1
        edge_certificates.append({"global_multiplier_exponent": f,
                                  "preserved_defect": a.defect})
    canonical_hull = TaggedImage(2, 0, 0, 0)
    assert canonical_hull.defect == 0
    assert path[-1].tag_degree == -1 and path[-1].image_degree == -2
    assert not compatible_global_multiplier(path[-1], canonical_hull,
                                            path[-1].multiplier_finite)

    # Positive control: an ACTUAL global multiplier pays both local and
    # archimedean factors, so the degree defect vanishes.
    repaired = TaggedImage(1, 0, 1, 1)
    repaired_target = TaggedImage(2, 1, 0, 0)
    assert repaired.defect == 0
    assert compatible_global_multiplier(repaired, repaired_target, 1)

    kummer_checks = []
    for ell in (5, 7, 11, 19, 41):
        for j in range(2, (ell-1)//2 + 1):
            r = prime_factor(j)
            a = r_order(j, r)
            b = r_order(2*ell, r)
            for q_valuation in (1, 2, 3, 19):
                for ramification in (1, 2, 3, 19):
                    for common_power in (1, 2, 7, 19):
                        dval = common_power * ramification * q_valuation
                        n = r_order(dval, r) + b + 1
                        modulus = r**n
                        # Detect that [q^M] has order at least r^(b+1)
                        # from the valuation quotient alone.
                        val_class_order = modulus // __import__('math').gcd(modulus, dval)
                        assert val_class_order == r**(b+1)
                        # Its actual order can be larger due to a unit part.
                        # All possible actual orders are covered here.
                        for d in range(b+1, n+1):
                            theta_order_exponent_bound = max(max(0, d-2*a), b)
                            assert theta_order_exponent_bound < d
                        kummer_checks.append({"ell": ell, "j": j, "r": r,
                                              "q_valuation": q_valuation,
                                              "ramification": ramification,
                                              "common_power": common_power,
                                              "detecting_root_level": n})

    # Actual local example K=Q_821(pi), pi^2=821; ell=41, j=19.
    # mu_82 has uniquely defined 19th roots within mu_82.
    # g=pi^361 has a 19th root pi^19 in K, whereas pi does not.
    r, j = 19, 19
    assert (j*j) % r == 0 and 1 % r != 0
    assert __import__('math').gcd(r, 82) == 1
    # Over the maximal unramified field, tame inertia acts on the root
    # torsors Z/19 by translation 0 (g) and translation 1 (q).
    fixed_theta = sum((x + j*j) % r == x for x in range(r))
    fixed_q_count = sum((x + 1) % r == x for x in range(r))
    assert (fixed_theta, fixed_q_count) == (19, 0)
    # Even allowing every cyclotomic automorphism and torsor translation
    # cannot make these two actions equivariant.
    equivariant_affine_maps = []
    for u in range(1, r):
        for shift in range(r):
            if all((u*((x+j*j) % r)+shift) % r == (u*x+shift+1) % r
                   for x in range(r)):
                equivariant_affine_maps.append((u, shift))
    assert not equivariant_affine_maps

    result = {
        "task": "C9-MARKED-IMAGE-DESCENT-20261024",
        "arithmetic_line_model": {
            "field": "Q", "finite_place": 3,
            "degree_unit": "log(3)",
            "scope": "standard arithmetic cQ3-type model, not complete IUT Theta-data",
            "fixed_q_images": [asdict(x) | {"defect": x.defect} for x in fixed_q],
            "distinct_fixed_q_morphism_pairs_rejected": rejected_pairs,
            "same_defect_path": [asdict(x) | {"defect": x.defect} for x in path],
            "path_edges": edge_certificates,
            "canonical_hull_defect": 0,
            "positive_control_global_multiplier": 3
        },
        "kummer": {
            "finite_parameter_checks": len(kummer_checks),
            "checks": kummer_checks,
            "explicit_example": {
                "field": "Q_821(pi), pi^2=821", "ell": 41, "j": 19,
                "q_hat": "pi", "g_j": "zeta*pi^361, zeta in mu_82",
                "root_exponent": 19,
                "q_class_order": 19, "g_class_order": 1,
                "inertia_fixed_points_q": fixed_q_count,
                "inertia_fixed_points_theta": fixed_theta,
                "affine_equivariant_torsor_maps": equivariant_affine_maps,
                "meaning": "rules out strengthened full nonunit Kummer compatibility, not IUT volume coverage"
            }
        },
        "all_assertions_passed": True,
        "full_source_P6_proved": False,
        "formal_kernel_checked": False
    }
    destination = Path(__file__).with_name("C9-MARKED-IMAGE-DESCENT-CERTIFICATE-20261024.json")
    destination.write_text(json.dumps(result, ensure_ascii=False, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"fixed_q_pairs_rejected":rejected_pairs,
                      "defect_preserving_edges":len(edge_certificates),
                      "kummer_parameter_cases":len(kummer_checks),
                      "all_assertions_passed":True}, ensure_ascii=False))


if __name__ == "__main__":
    main()
