# S2760 — 11a1 at l=5 Serre-style large-image target

Date: 2026-11-07. Statement/target audit; no range proof.

## 1. Curve

```lean
11a1: y^2 + y = x^3 - x^2 - 10x - 20
Weierstrass (a1,a2,a3,a4,a6) = (0,-1,1,-10,-20).
```

Actual Lean: `E11a1Curve : WeierstrassCurve QQ` in S2760ElevenA1SerreTargetActual.lean.

## 2. Discriminant

```lean
E11a1Curve.Delta = -161051 = -11^5     (proved, norm_num)
```

Nonzero, so `E11a1Curve.IsElliptic` actual.

## 3. j-invariant

```lean
E11a1.jInvariant = -122023936 / 161051
                 = -2^12 * 31^3 / 11^5     (proved)
```

## 4. CM determination

`j = -2^12 * 31^3 / 11^5` has denominator divisible by 11, so it is NOT an
algebraic integer.  Classical CM theory: if E has CM by an order in an
imaginary quadratic field, then j(E) is an algebraic integer.  Therefore 11a1
is NON-CM.  (No formal IsCM predicate exists in Mathlib; this is the exact
classical criterion, evidence at the level of the proved rational j value.)

## 5. Target statement instance

```lean
def S2760FiveLabel : PrimeGeFive := { value := 5, ... }
def S2760SerreLargeImageTarget : Prop :=
  SerreStyleLargeImageStatement E11a1 S2760FiveLabel
```

Unfolds to:

```lean
exists basis : (Fin 2 -> ZMod 5) ~= E11a1.LTorsion fiveLabel,
  SL2(ZMod 5) <= (E11a1.galoisLTorsionMatrixRepresentation fiveLabel basis).range
```

## 6. Repository / Mathlib data check

- Mathlib: no 11a1-specific Weierstrass curve, no LMFDB data, no mod-l Galois
  image computation.  Search for 11a1 equation found no hits.
- Repo: SerreStyleLargeImageStatement is a Prop definition only
  (SourceTorsionCarrierReduction.lean:298); no theorem proves it for a concrete
  curve.  S1725SourceTorsionFPrimeActual proves only equivalences/conditional
  reduction to this statement, not the statement itself.
- The curve/representation objects ARE available: PuncturedEllipticCurve,
  LTorsion, galoisLTorsionMatrixRepresentation.  The missing piece is the
  actual range computation / Serre open-image theorem for 11a1 at l=5.

## 7. Exact object gap

```text
GAP: no actual proof of
  exists basis, SL2(F_5) <= range(galoisLTorsionMatrixRepresentation E11a1 5 basis).
```

Needed:

1. an explicit rank-two basis of E11a1.LTorsion 5;
2. computation of the mod-5 Galois representation of 11a1;
3. proof that SL2(F_5) is contained in its image (Serre open-image theorem for
   non-CM E without rational 5-isogeny).

None of 1-3 is formalized in Mathlib/repo.  The target Prop is well-typed,
actual as a statement, but UNPROVED.

## 8. Verdict

- Curve equation, discriminant, j: actual and proved.
- Non-CM: classical criterion from j non-integral; no formal CM predicate.
- Target instance: S2760SerreLargeImageTarget actual Prop.
- Range proof: MISSING; precise gap above.  Do not claim large image/Serre.
