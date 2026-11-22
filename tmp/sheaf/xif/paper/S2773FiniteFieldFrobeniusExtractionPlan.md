# S2773 — Sage division_field job check + finite-field Frobenius extraction plan

Date: 2026-11-07. Audit/plan only; no fake matrices.

## 1. Sage job output check

Available files:

- `tmp/sheaf/xif/paper/S2767Curve196a1SageExtraction.sage` (placeholder script)
- `tmp/sheaf/xif/paper/_S2767test1.sage` (curve invariants, is_surjective, degree)
- `tmp/sheaf/xif/paper/_S2767test2.sage` (division_field(5), torsion_basis(5))

Search for job output (`start division field`, `basis len`, division_field logs):
NO output/log file exists.  The scripts were never run to completion.

Sage availability check:
- `Get-Command sage` -> empty;
- `wsl -e sage --version` -> WSL error `ERROR_PATH_NOT_FOUND` (no Ubuntu distro).

FIRST ERROR: Sage is not installed in this environment, and no output of the
division_field/basis job was produced.  There is no basis data to extract.

## 2. What the Sage script would produce

`_S2767test2.sage`:

```sage
E = EllipticCurve([0,-1,0,-142,701])   # 196a1
K = E.division_field(5)
EK = E.change_ring(K)
B = EK.torsion_basis(5)                # should return two 5-torsion points
```

Expected exact outputs (not yet produced): `K.degree()`, `K.discriminant()`,
two points P,Q in E(K)[5].

## 3. Finite-field E[5] extraction plan (small primes)

For an auxiliary good prime p (p ∤ 5*N, N=196) choose k with `5 | p^k - 1`
(k = order of p mod 5; k=1 if p≡1 mod5, else 4).  Work over `F = F_{p^k}`.

Algorithm:

1. `prePsi5 = E.division_polynomial(5)` mod p; factor over F.
2. For each root x, compute y from the Weierstrass equation; get a point P=(x,y)
   (if no y, x is the x-coordinate of a 2-torsion point; skip).
3. Find two F5-linearly independent points P,Q in E[5](F):
   - enumerate roots / random points R;
   - compute `5-torsion part` by `( #E(F) / 25 ) * R` when 25 | #E(F);
   - check independence via Weil pairing `e_5(P,Q) != 1` (or order-25 subgroup).
4. Frobenius matrix at the finite-field prime p:
   - `Fr = pow(p, k)`? Use the p-power Frobenius on coordinates:
     `Fr(x,y) = (x^p, y^p)` on F_{p^k};
   - solve `Fr(P) = aP + bQ`, `Fr(Q) = cP + dQ` in E[5] (discrete log in E[5],
     e.g. by enumerating all 25 combinations);
   - output `M_p = [[a,b],[c,d]]` in GL2(F5).

This yields LOCAL finite-field Frobenius matrices.  It does NOT directly
produce matrices for all global Frobenius conjugacy classes in one common
basis.

## 4. Global extraction plan (needed for SL2 image)

1. Compute K = Q(E[5]) (division field) once.
2. Choose a basis P,Q of E(K)[5] (Sage `EK.torsion_basis(5)`).
3. For each good rational prime ell, choose a prime ideal `frak` above ell in
   K; let `frob = frak.frobenius()`.
4. Compute frob(P), frob(Q) in E(K)[5], solve coordinates in basis (P,Q)
   mod 5; output 2x2 matrix.
5. The generated subgroup of GL2(F5) gives the mod-5 image.

The local finite-field matrices from section 3 are not a substitute: bases
are different for each p, and a finite-field Frobenius is not a global
Frobenius matrix.

## 5. Lean interface (no fake matrices)

Required Lean objects:

```lean
def S196a1Curve : WeierstrassCurve ℚ := mk 0 (-1) 0 (-142) 701
instance : S196a1Curve.IsElliptic
def S196a1 : PuncturedEllipticCurve ℚ
abbrev S196a1FiveBasis :=
  (Fin 2 -> ZMod 5) ≃ₗ[ZMod 5] S196a1.LTorsion 5
def S196a1_frobMatrix (ell) (b) : Matrix.GL (Fin 2) (ZMod 5)
theorem S196a1_SL2_le_range (b) :
  SL2(F5) <= (galoisLTorsionMatrixRepresentation 5 b).range
```

None of `S196a1FiveBasis`, `S196a1_frobMatrix`, or `S196a1_SL2_le_range`
can be filled until the Sage/Magma extraction above produces exact P,Q and
matrices.  Do not fabricate them.

## 6. Verdict

- Sage job output: ABSENT; Sage not installed (first error recorded).
- Sage division_field basis: NOT extracted.
- Finite-field extraction scheme: specified (small p, F_{p^k}, prePsi5 roots,
  independence via Weil pairing, p-power Frobenius matrices).
- Global common-basis extraction: specified (division field K, primes above
  ell, frobenius action, coordinate solve).
- Lean matrix interface: specified, data missing.
- No fake matrices; no SL2 containment claim.