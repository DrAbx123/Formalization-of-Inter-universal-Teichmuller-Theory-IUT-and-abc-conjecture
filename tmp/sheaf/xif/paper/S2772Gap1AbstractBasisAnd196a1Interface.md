# S2772 — Gap1 abstract basis audit + 196a1 matrix-extraction Lean interface

Date: 2026-11-07. Audit only; no fake matrices.

## 1. Gap1 status

### ACTUAL: S2769RankTwoTorsionBasisActual

File: `tmp/sheaf/xif/paper/S2769RankTwoTorsionBasisActual.lean`

- source 5157 B; olean 187840 B;
- `S2769_fiveTorsion_projective_card`: projective E[5] card = 25;
- `S2769_fiveTorsion_finrank`: finrank over ZMod 5 = 2;
- `S2769_rankTwoTorsionBasis`:
  ```lean
  Nonempty ((Fin 2 -> ZMod 5) ≃ₗ[ZMod 5]
    AddSubgroup.torsionBy W.toProjective.Point 5)
  ```
  for `W : WeierstrassCurve K`, `K` algebraically closed CharZero,
  `W.IsElliptic`.
- axioms trio.

### ACTUAL: S2769ProjAffineCardActual

- `S2769ProjAffineTorsionEquiv` and `S2769_projective_fiveTorsion_card`
  transport the affine 25-card theorem to projective E[5]; axioms trio.

### NOT ACTUAL: S2771Gap1ClosedActual

File `S2771Gap1ClosedActual.lean` has NO olean.  Compile first error:

```text
Type mismatch: After simplification, term h has type
  Nonempty ((Fin 2 → ZMod 5) ≃ₗ[ZMod 5]
    ↥(AddSubgroup.torsionBy W.toProjective.Point 5))
but is expected to have type
  Nonempty ((Fin 2 → ZMod 5) ≃ₗ[ZMod 5]
    ↥(AddSubgroup.torsionBy (X.curve.toProjective.baseChange (AlgebraicClosure F)).Point 5))
```

and `#print axioms S2771_rankTwoTorsionBasis` includes `sorryAx`.

So Gap1 is ACTUAL at the abstract closed-field curve level
(S2769RankTwo), but the S2771 transfer to `PuncturedEllipticCurve.LTorsion`
is NOT actual yet.  Do not claim Gap1 closed by S2771.

## 2. What S2771 needs

A base-change/projective compatibility lemma:

```lean
WeierstrassCurve.Projective.Point
  ((S2771W X).toProjective)  ≃+
WeierstrassCurve.Projective.Point
  (X.curve.toProjective.baseChange (AlgebraicClosure F))
```

or a definitional bridge showing `PuncturedEllipticCurve.LTorsion` unfolds to
`AddSubgroup.torsionBy ((S2771W X).toProjective.Point) 5`.  The current `simpa`
cannot close it.

## 3. Lean interface needed for 196a1 matrix extraction

### 3.1 Curve

```lean
def S196a1Curve : WeierstrassCurve ℚ :=
  WeierstrassCurve.mk 0 (-1) 0 (-142) 701
-- a1,a2,a3,a4,a6 = 0,-1,0,-142,701
theorem S196a1_discriminant : S196a1Curve.Δ = 784
instance : S196a1Curve.IsElliptic
def S196a1 : PuncturedEllipticCurve ℚ := ...
```

### 3.2 E[5] basis

```lean
abbrev S196a1FiveBasis : Type :=
  (Fin 2 → ZMod 5) ≃ₗ[ZMod 5] S196a1.LTorsion fiveLabel
noncomputable def S196a1_fiveBasis : S196a1FiveBasis := ...
```

or the affine form

```lean
AddSubgroup.torsionBy (S196a1.curve.toProjective.Point) (5 : ℤ)
```

with a projective/affine equivalence.  This can be obtained from the S2769
generic rank-two basis once the base-change bridge is fixed.

### 3.3 Frobenius matrices

```lean
-- for a good prime ell, a Frobenius element in the absolute Galois group
Frob196a1 (ell : Nat) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

-- its matrix in the chosen E[5] basis
noncomputable def S196a1_frobMatrix
    (ell : Nat) (b : S196a1FiveBasis) :
    Matrix.GeneralLinearGroup (Fin 2) (ZMod 5) :=
  S196a1.galoisLTorsionMatrixRepresentation fiveLabel b (Frob196a1 ell)
```

Requires: explicit Frobenius choice at each good ell, and the project's
`galoisLTorsionMatrixRepresentation` API.  Not available from LMFDB/Sage
class data: Sage `gal_reps` computes traces and surjectivity, NOT matrices
in a common basis.

### 3.4 SL2 containment

```lean
theorem S196a1_SL2_le_range
    (b : S196a1FiveBasis) :
    Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))) ≤
      (S196a1.galoisLTorsionMatrixRepresentation fiveLabel b).range
```

### 3.5 Exact data gap for 196a1

- LMFDB 196.a1 page: curve/disc/torsion/isogeny exact (see S2766);
  LMFDB does not expose mod-5 image.
- Sage `gal_reps` source: `is_surjective(5)=True` and
  `image_type(5)='The image is all of GL_2(F_5).'` are CLASS-LEVEL
  (trace/Kronecker algorithm, `_ex_set(5)=[0,1,2,4]`), not matrices.
- No explicit E[5] basis or Frobenius matrices in LMFDB/Sage source;
  extracting them needs Sage/Magma `gal_reps`/`galrep` or a division-polynomial
  computation.
- Do NOT fabricate matrices or claim SL2 containment before this extraction.

## 4. Verdict

- Gap1 abstract closed-field basis: ACTUAL (S2769RankTwo).
- S2771 X-level transfer: NOT actual (type mismatch + sorryAx).
- 196a1 matrix extraction interface specified above; data currently missing.
- No fake matrices; no claim of actual 196a1 LargeImage/SL2 containment.