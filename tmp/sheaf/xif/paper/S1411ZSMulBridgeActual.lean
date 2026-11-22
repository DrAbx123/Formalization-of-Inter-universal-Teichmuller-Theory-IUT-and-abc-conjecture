/-
Copyright (c) 2026 The IUT/ABC formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT/ABC formalization project
-/

import tmp.sheaf.xif.paper.S1373ZeroCriterionActual
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point

/-!
# S1411: the TauCeti `ZSMul` point-evaluation bridge, ported to Mathlib v4.32.2

TauCeti's `DivisionPolynomial/ZSMul.lean` proves that the Jacobian coordinates of
`n • (x, y)` are `(φₙ(x,y) : ωₙ(x,y) : ψₙ(x,y))` (`zsmul_point_eq_smulEval`) and hence that
a vanishing `ψₙ(x,y)` forces `n • P = 0` (`zsmul_eq_zero_of_evalEval_ψ_eq_zero`). This file
ports the *reduction* half of that bridge: it states the bridge in the language of this tree,
derives both torsion criteria from it, and records the exact first field of the port that
Mathlib v4.32.2 cannot supply.

## What is ported, with proofs

* `ZSMulEvalBridge`: the conclusion of TauCeti's `zsmul_point_eq_smulEval`, stated with
  `WeierstrassCurve.evalDivisionPolynomial`. The middle coordinate is left existential because
  Mathlib v4.32.2 has no bivariate `ωₙ`; the third coordinate is `ψₙ`.
* `zsmulEvalBridge_zero`, `zsmulEvalBridge_one`: the `n = 0, 1` base cases, proved.
* `zsmulEvalBridge_neg`: the bridge is invariant under `n ↦ -n` (TauCeti's `smulPoly_neg` /
  `smulEval_neg` step), proved.
* `zsmul_eq_zero_of_evalDivisionPolynomial_eq_zero`: **the root half**,
  `ψₙ(P) = 0 → n • P = 0`, from the bridge (TauCeti's `zsmul_eq_zero_of_evalEval_ψ_eq_zero`).
* `evalDivisionPolynomial_eq_zero_of_zsmul_eq_zero`: the forward half,
  `n • P = 0 → ψₙ(P) = 0`, from the same bridge (TauCeti's
  `evalEval_ψ_eq_zero_of_zsmul_eq_zero`).
* `divisionPolynomialRootsAreTorsion_of_bridge`, `divisionPolynomialZeroCriterion_of_bridge`:
  the tree-level interfaces of `S1373ZeroCriterionActual`, from the bridge for all points.
* `zsmul_fromAffine_eq_zero_iff_zsmul_eq_zero` and its `ℕ` form: TauCeti's transport of
  torsion between the affine and Jacobian point groups, unconditional.
* `rel_odd_normEDS`, `rel_even_normEDS`: the two recurrence-shaped elliptic-net relations
  of `normEDS`, which Mathlib v4.32.2 does provide.

## The exact first field

The bridge is TauCeti's `zsmul_point_eq_smulEval`. Its proof needs the elliptic-net theorem
`IsEllipticNet (normEDS b c d)` (Mathlib master's `IsEllipticNet.normEDS`), which is **not** in
Mathlib v4.32.2: `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` carries it as the
explicit TODO at line 70 ("prove that `normEDS` satisfies `IsEllipticDvdSequence`"). The same
Mathlib-master EDS file also supplies `IsEllipticNet.of_even_odd`, which TauCeti's
`.../Descent.lean` uses; `.../ReducedInvariant.lean` needs the net theorem to build the
bivariate `ωₙ` that is the second coordinate of `zsmul_point_eq_smulEval`. TauCeti itself
contains neither proof. The net proposition is recorded below as `NetEDSInput`, a
`Prop`-valued definition, not an axiom and not a hypothesis of any proved theorem.

## References

* J. Xu, D. K. Angdinata, `LutzNagell/ZSMul.lean`, AINTLIB, Apache-2.0, `main @ 1c1c7466`.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], Exercise 3.7.

## Tags

elliptic curve, division polynomial, torsion point, scalar multiplication
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1411ZSMulBridgeActual

open Polynomial WeierstrassCurve WeierstrassCurve.Jacobian
open scoped WeierstrassCurve.Jacobian

universe u

/-! ## 1. The bridge -/

/-- **The TauCeti point-evaluation bridge at `n`.** For a nonsingular affine point `(x, y)` on
`W`, the Jacobian class of `n • (x, y)` has a nonsingular representative whose third coordinate
is `ψₙ(x,y)`. This is the conclusion of TauCeti's `zsmul_point_eq_smulEval` with the middle
coordinate left existential. -/
def ZSMulEvalBridge {F : Type u} [Field F] (W : WeierstrassCurve.Affine F) {x y : F}
    (hns : W.Nonsingular x y) (n : ℤ) : Prop :=
  ∃ (X Y : F) (h : W.toJacobian.Nonsingular ![X, Y, W.evalDivisionPolynomial x y n]),
    (n • (WeierstrassCurve.Affine.Point.some x y hns).toJacobian).point =
      ⟦![X, Y, W.evalDivisionPolynomial x y n]⟧

/-- The bridge at `n = 0`. -/
theorem zsmulEvalBridge_zero {F : Type u} [Field F] (W : WeierstrassCurve.Affine F)
    {x y : F} (hns : W.Nonsingular x y) : ZSMulEvalBridge W hns 0 := by
  have hψ : W.evalDivisionPolynomial x y 0 = 0 := W.evalDivisionPolynomial_zero x y
  refine ⟨1, 1, ?_, ?_⟩
  · simpa [hψ] using WeierstrassCurve.Jacobian.nonsingular_zero
  · rw [hψ, zero_zsmul, WeierstrassCurve.Jacobian.Point.zero_point]

/-- The bridge at `n = 1`. -/
theorem zsmulEvalBridge_one {F : Type u} [Field F] (W : WeierstrassCurve.Affine F)
    {x y : F} (hns : W.Nonsingular x y) : ZSMulEvalBridge W hns 1 := by
  have hψ : W.evalDivisionPolynomial x y 1 = 1 := W.evalDivisionPolynomial_one x y
  refine ⟨x, y, ?_, ?_⟩
  · simpa [hψ] using (WeierstrassCurve.Jacobian.nonsingular_some x y).mpr hns
  · rw [hψ, one_zsmul]
    simp only [WeierstrassCurve.Affine.Point.toJacobian,
      WeierstrassCurve.Jacobian.Point.fromAffine_some]

/-- **The bridge is invariant under `n ↦ -n`.** Negating the index negates the point, and
rescaling the negated representative by the unit `-1` restores the third coordinate to
`ψ₋ₙ = -ψₙ`. This is the ported form of TauCeti's `smulPoly_neg` / `smulEval_neg` step. -/
theorem zsmulEvalBridge_neg {F : Type u} [Field F] {W : WeierstrassCurve.Affine F}
    {x y : F} {hns : W.Nonsingular x y} {n : ℤ} (hbridge : ZSMulEvalBridge W hns n) :
    ZSMulEvalBridge W hns (-n) := by
  obtain ⟨X, Y, hns', heq⟩ := hbridge
  set Z := W.evalDivisionPolynomial x y n with hZ
  have hψ : W.evalDivisionPolynomial x y (-n) = -Z := by
    rw [W.evalDivisionPolynomial_neg x y n, hZ]
  let P : W.toJacobian.Point := (WeierstrassCurve.Affine.Point.some x y hns).toJacobian
  have hres : (![X, -W.toJacobian.negY ![X, Y, Z], -Z] : Fin 3 → F) =
      (-1 : F) • W.toJacobian.neg (![X, Y, Z] : Fin 3 → F) := by
    funext i
    fin_cases i <;>
      simp [WeierstrassCurve.Jacobian.neg, WeierstrassCurve.Jacobian.negY,
        WeierstrassCurve.Jacobian.smul_fin3]
    all_goals ring
  refine ⟨X, -W.toJacobian.negY ![X, Y, Z], ?_, ?_⟩
  · rw [hψ, hres]
    exact (WeierstrassCurve.Jacobian.nonsingular_smul _ (isUnit_neg_one)).mpr
      (WeierstrassCurve.Jacobian.nonsingular_neg hns')
  · rw [hψ]
    have h2 : (n • P).point = ⟦![X, Y, Z]⟧ := by simpa [hZ] using heq
    calc ((-n) • P).point = (-(n • P)).point := by rw [neg_smul]
      _ = W.toJacobian.negMap (n • P).point := WeierstrassCurve.Jacobian.Point.neg_point _
      _ = W.toJacobian.negMap ⟦![X, Y, Z]⟧ := by rw [h2]
      _ = ⟦W.toJacobian.neg ![X, Y, Z]⟧ := WeierstrassCurve.Jacobian.negMap_eq _
      _ = ⟦![X, -W.toJacobian.negY ![X, Y, Z], -Z]⟧ := by
        rw [hres]
        exact (WeierstrassCurve.Jacobian.smul_eq _ (isUnit_neg_one)).symm

/-! ## 2. The two torsion criteria from the bridge -/

/-- **A root of `ψₙ` is annihilated by `n`** — the root half, from the bridge
(TauCeti's `zsmul_eq_zero_of_evalEval_ψ_eq_zero`). -/
theorem zsmul_eq_zero_of_evalDivisionPolynomial_eq_zero {F : Type u} [Field F]
    {W : WeierstrassCurve.Affine F} {x y : F} {hns : W.Nonsingular x y} {n : ℤ}
    (hbridge : ZSMulEvalBridge W hns n) (hψ : W.evalDivisionPolynomial x y n = 0) :
    n • (WeierstrassCurve.Affine.Point.some x y hns).toJacobian = 0 := by
  obtain ⟨X, Y, hns', heq⟩ := hbridge
  have hz : (![X, Y, W.evalDivisionPolynomial x y n] : Fin 3 → F) 2 = 0 := by
    simp [hψ]
  have hzero : (⟦![X, Y, W.evalDivisionPolynomial x y n]⟧ : PointClass F) =
      (0 : W.toJacobian.Point).point := by
    rw [WeierstrassCurve.Jacobian.Point.zero_point]
    exact Quotient.sound (WeierstrassCurve.Jacobian.equiv_zero_of_Z_eq_zero hns' hz)
  rw [WeierstrassCurve.Jacobian.Point.ext_iff, heq, hzero]

/-- **A torsion point is a root of its division polynomial** — the forward half, from the same
bridge (TauCeti's `evalEval_ψ_eq_zero_of_zsmul_eq_zero`). -/
theorem evalDivisionPolynomial_eq_zero_of_zsmul_eq_zero {F : Type u} [Field F]
    {W : WeierstrassCurve.Affine F} {x y : F} {hns : W.Nonsingular x y} {n : ℤ}
    (hbridge : ZSMulEvalBridge W hns n)
    (h : n • (WeierstrassCurve.Affine.Point.some x y hns).toJacobian = 0) :
    W.evalDivisionPolynomial x y n = 0 := by
  obtain ⟨X, Y, hns', heq⟩ := hbridge
  rw [WeierstrassCurve.Jacobian.Point.ext_iff] at h
  have heq' : (⟦![X, Y, W.evalDivisionPolynomial x y n]⟧ : PointClass F) = ⟦![1, 1, 0]⟧ := by
    calc (⟦![X, Y, W.evalDivisionPolynomial x y n]⟧ : PointClass F)
        = (n • (WeierstrassCurve.Affine.Point.some x y hns).toJacobian).point := heq.symm
      _ = (0 : W.toJacobian.Point).point := h
      _ = ⟦![1, 1, 0]⟧ := WeierstrassCurve.Jacobian.Point.zero_point
  have hz := (WeierstrassCurve.Jacobian.Z_eq_zero_of_equiv (Quotient.exact heq')).mpr rfl
  simpa using hz

/-! ## 3. Torsion transport between affine and Jacobian points -/

/-- **Torsion transports between the affine and Jacobian point groups** (TauCeti's
`zsmul_fromAffine_eq_zero_iff_zsmul_eq_zero`), unconditionally. -/
theorem zsmul_fromAffine_eq_zero_iff_zsmul_eq_zero {F : Type u} [Field F] [DecidableEq F]
    {E : WeierstrassCurve F} {P : E.toAffine.Point} {n : ℤ} :
    n • WeierstrassCurve.Jacobian.Point.fromAffine P = 0 ↔ n • P = 0 := by
  have h : (WeierstrassCurve.Jacobian.Point.toAffineAddEquiv E)
      (n • WeierstrassCurve.Jacobian.Point.fromAffine P) = n • P := by
    rw [map_zsmul]
    exact congrArg (fun Q => n • Q)
      ((WeierstrassCurve.Jacobian.Point.toAffineAddEquiv E).apply_symm_apply P)
  have hiff := (WeierstrassCurve.Jacobian.Point.toAffineAddEquiv E).map_eq_zero_iff
    (x := n • WeierstrassCurve.Jacobian.Point.fromAffine P)
  rw [h] at hiff
  exact hiff.symm

/-- The `ℕ`-scalar cast form of `zsmul_fromAffine_eq_zero_iff_zsmul_eq_zero`
(TauCeti's `zsmul_fromAffine_eq_zero_iff`). -/
theorem zsmul_fromAffine_eq_zero_iff {F : Type u} [Field F] [DecidableEq F]
    {E : WeierstrassCurve F} {P : E.toAffine.Point} {n : ℕ} :
    (n : ℤ) • WeierstrassCurve.Jacobian.Point.fromAffine P = 0 ↔ n • P = 0 := by
  rw [zsmul_fromAffine_eq_zero_iff_zsmul_eq_zero, natCast_zsmul]

/-! ## 4. The tree-level interfaces -/

/-- **The root criterion at `n`, from a pointwise bridge**:
`WeierstrassCurve.DivisionPolynomialRootsAreTorsion n` of `S1373ZeroCriterionActual`. -/
theorem divisionPolynomialRootsAreTorsion_of_bridge {F : Type u} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) {n : ℤ}
    (hbridge : ∀ (x y : F) (hns : W.toAffine.Nonsingular x y),
      ZSMulEvalBridge W.toAffine hns n) :
    W.DivisionPolynomialRootsAreTorsion n := by
  intro P hP
  cases P with
  | zero => exact zsmul_zero n
  | some x y hns =>
      rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_some] at hP
      exact (zsmul_fromAffine_eq_zero_iff_zsmul_eq_zero).mp
        (zsmul_eq_zero_of_evalDivisionPolynomial_eq_zero (hbridge x y hns) hP)

/-- **The full zero criterion at `n`, from a pointwise bridge**:
`WeierstrassCurve.DivisionPolynomialZeroCriterion n` of `S1373ZeroCriterionActual`. -/
theorem divisionPolynomialZeroCriterion_of_bridge {F : Type u} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) {n : ℤ}
    (hbridge : ∀ (x y : F) (hns : W.toAffine.Nonsingular x y),
      ZSMulEvalBridge W.toAffine hns n) :
    W.DivisionPolynomialZeroCriterion n := by
  intro P
  constructor
  · intro hP
    cases P with
    | zero => exact W.evalDivisionPolynomialAtPoint_zero n
    | some x y hns =>
        rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_some]
        exact evalDivisionPolynomial_eq_zero_of_zsmul_eq_zero (hbridge x y hns)
          ((zsmul_fromAffine_eq_zero_iff_zsmul_eq_zero).mpr hP)
  · intro hP
    cases P with
    | zero => exact zsmul_zero n
    | some x y hns =>
        rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_some] at hP
        exact (zsmul_fromAffine_eq_zero_iff_zsmul_eq_zero).mp
          (zsmul_eq_zero_of_evalDivisionPolynomial_eq_zero (hbridge x y hns) hP)

/-! ## 5. The elliptic-net seed of the TauCeti proof, and its first field -/

/-- The odd recurrence shape `ER(m+1, m, 1, 0)` of `normEDS`, unconditional in Mathlib
v4.32.2 as `normEDS_odd`. -/
theorem rel_odd_normEDS {R : Type u} [CommRing R] (b c d : R) (m : ℤ) :
    IsEllipticNet.rel (normEDS b c d) (m + 1) m 1 0 = 0 := by
  rw [IsEllipticNet.rel_odd, normEDS_one, normEDS_odd]
  ring

/-- The even recurrence shape `ER(m+1, m-1, 1, 0)` of `normEDS`, unconditional in Mathlib
v4.32.2 as `normEDS_even`. -/
theorem rel_even_normEDS {R : Type u} [CommRing R] (b c d : R) (m : ℤ) :
    IsEllipticNet.rel (normEDS b c d) (m + 1) (m - 1) 1 0 = 0 := by
  rw [IsEllipticNet.rel_even, normEDS_one]
  simp only [one_pow, mul_one]
  rw [normEDS_two, normEDS_even]
  ring

/-- **The exact first field of the port: the elliptic-net theorem for `normEDS`.**
Mathlib master proves `IsEllipticNet (normEDS b c d)`; Mathlib v4.32.2 leaves it as the TODO
at `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:70`. This is a `Prop`-valued
definition, not an axiom, and no proved theorem below depends on it. -/
def NetEDSInput (R : Type u) [CommRing R] : Prop :=
  ∀ (b c d : Polynomial (Polynomial R)), IsEllipticNet (normEDS b c d)

/-- The TauCeti `isEllipticNet_ψ` step, *from* the first field. -/
theorem isEllipticNet_ψ_of_netEDSInput {R : Type u} [CommRing R] (h : NetEDSInput R)
    (W : WeierstrassCurve R) : IsEllipticNet W.ψ := by
  have hψ : W.ψ = (normEDS W.ψ₂ (Polynomial.C W.Ψ₃) (Polynomial.C W.preΨ₄) :
      ℤ → Polynomial (Polynomial R)) := rfl
  rw [hψ]
  exact h W.ψ₂ (Polynomial.C W.Ψ₃) (Polynomial.C W.preΨ₄)

/-! ## 6. Status

* `statement_compiles`: yes; this file is checked by `lake env lean`, exit 0.
* `proof_body_checked`: yes for the bridge base cases, the negation step, both torsion
  criteria, the two tree-level interfaces, the affine/Jacobian torsion transport, and the
  two `normEDS` recurrence relations.
* `kernel_closed`: only for those declarations; `ZSMulEvalBridge` is the named unproved
  input (TauCeti's `zsmul_point_eq_smulEval`), and its own first field is `NetEDSInput`.
* `target_accepted`: no. The unconditional root criterion `ψₙ(P) = 0 → n • P = 0` is not
  claimed: it is proved from the bridge, and the bridge is not proved here.

-/

/-! ## 7. Axiom footprint -/

#print axioms zsmulEvalBridge_zero
#print axioms zsmulEvalBridge_one
#print axioms zsmulEvalBridge_neg
#print axioms zsmul_eq_zero_of_evalDivisionPolynomial_eq_zero
#print axioms evalDivisionPolynomial_eq_zero_of_zsmul_eq_zero
#print axioms divisionPolynomialRootsAreTorsion_of_bridge
#print axioms divisionPolynomialZeroCriterion_of_bridge
#print axioms zsmul_fromAffine_eq_zero_iff_zsmul_eq_zero
#print axioms zsmul_fromAffine_eq_zero_iff
#print axioms rel_odd_normEDS
#print axioms rel_even_normEDS
#print axioms isEllipticNet_ψ_of_netEDSInput

end LeanFormal.IUT.XiFPaper.S1411ZSMulBridgeActual
