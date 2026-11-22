# S2767: 196a1 at l=5 -- Sage data / E[5] basis / Frobenius matrices
# Reference only. No Lean actual claim.
# Curve: 196.a1 / Cremona 196a2
E = EllipticCurve([0, -1, 0, -142, 701])
assert E.conductor() == 196
assert E.discriminant() == 784
assert E.j_invariant() == 406749952
assert E.torsion_order() == 1
assert E.isogeny_class().matrix() == [[1, 3], [3, 1]]

rho = E.galois_representation()
assert rho.is_reducible(3) is True
assert rho.is_surjective(5) is True
assert rho.reducible_primes() == [3]
assert rho.non_surjective() == [2, 3]
print("image_type(5):", rho.image_type(5))   # 'The image is all of GL_2(F_5).'

# 5-division field and an E[5] basis.
f5 = E.division_polynomial(5)
print("deg prePsi5:", f5.degree())
K = E.division_field(5)
print("division field degree:", K.degree())
EK = E.change_ring(K)
P, Q = EK.torsion_basis(5)[0:2]             # Sage API: torsion_basis(5) returns two points
print("P =", P)
print("Q =", Q)

# Frobenius matrices: for each good prime ell, pick a prime above ell in K,
# apply its Frobenius to P,Q, and read coordinates in the basis (P,Q).
G = K.galois_group()
F5 = GF(5)
mats = []
for ell in [3, 11, 13, 17, 19, 23, 29, 31]:
    if E.conductor() % ell == 0:
        continue
    for frak in K.primes_above(ell):
        frob = frak.frobenius()              # element of G
        # action on points:
        R1 = EK(frob(P[0]), frob(P[1])) if P != EK(0) else EK(0)
        R2 = EK(frob(Q[0]), frob(Q[1])) if Q != EK(0) else EK(0)
        # solve R = a*P + b*Q in E[5] (Sage discrete log / linear algebra on E[5])
        # For Sage >= 9.2: EK.abelian_group() or use Weil pairing coordinates.
        # Use the basis coordinates via E[5] linear algebra:
        M = matrix(F5, 2, 2, [0,0,0,0])
        # Placeholder: replace with explicit E[5] linear-coordinate extraction.
        print("ell", ell, "frob order", frob.order())
        mats.append((ell, M))
        break

# For GL2(F5) verification from matrices:
#   - check each matrix det != 0
#   - check generated subgroup order 480 (= #GL2(F5))
#   - check generated subgroup contains SL2: determinants cover F5^* and
#     the determinant-1 subgroup has order 120.
