import tmp.sheaf.xif.paper.S1373ZeroCriterionActual
import tmp.sheaf.xif.paper.S1372XCoordinateFormulaActual
import LeanFormal.IUT.ABCBridge.Galois.EllipticDivisionPolynomialEvaluation
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Module.Torsion.Basic

/-!
Copyright (c) 2026 The IUT/ABC formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT/ABC formalization project
-/

/-!
# S1394: TauCeti's PsiSq zero criterion adapted to Mathlib v4.32.2

TauCeti's division-polynomial torsion layer (Lean v4.36.0-rc1) proves, for a
Weierstrass curve over a field and a nonsingular affine point P = (x, y):

* eval_ΨSq_eq_zero_iff_zsmul_eq_zero :
    (W.ΨSq n).eval x = 0 ↔ n • P = 0,
* eval_ΨSq_ne_zero_of_zsmul_ne_zero :
    n • P ≠ 0 → (W.ΨSq n).eval x ≠ 0,
* zsmul_fromAffine_eq_zero_iff :
    (n : ℤ) • Jacobian.Point.fromAffine P = 0 ↔ n • P = 0,

together with the torsion-subgroup corollaries in
TauCeti/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Torsion/Roots.lean.
These are precisely the pointwise vanishing criteria consumed by the
separability argument for preΨ_n (and by the even-n exclusion of the Ψ₂Sq
factor).

This file ports those conclusions to the current Mathlib v4.32.2 tree.  It does
**not** vendor or import TauCeti's proof closure: the universal-curve and
smulEval development (DivisionPolynomial/ZSMul.lean, Universal.lean, ...) stays
out of the tree.  Instead, the pointwise criterion is identified with the
current tree's existing named interface DivisionPolynomialZeroCriterion from
S1373ZeroCriterionActual, whose n = 2 and n = 3 instances are already
unconditional.  The two non-trivial easy ingredients are proved here:

* zsmul_fromAffine_eq_zero_iff, by the additive equivalence between affine and
  Jacobian points (no group-law criterion needed);
* the square bridge ψ_n(P)^2 = ΨSq_n(x) on the curve, from the current tree's
  evaluation bridges.

## What is unconditional here

* zsmul_fromAffine_eq_zero_iff_zsmul_eq_zero and zsmul_fromAffine_eq_zero_iff.
* WeierstrassCurve.Affine.exists_point_on_curve: over an algebraically closed
  field every x is the abscissa of a point of the equation (ported with proof).
* S1394PsiSqZeroCriterion at n = 2 and n = 3, hence the exact iff at n = 2 and
  n = 3.
* The direction n • P = 0 → (W.ΨSq n).eval x = 0 from the x-coordinate formula
  S1372XCoordinateFormula (S1372XCoordinateFormulaActual): this is the
  "detection" half used by separability and does not need the converse.

## Exact first lemma

The exact first missing lemma is the general pointwise criterion

  S1394PsiSqZeroCriterion W n,

defined below to have exactly the TauCeti statement, equivalently the current
tree's DivisionPolynomialZeroCriterion W n.  For n ≠ 2, 3 it is not proved in
Mathlib v4.32.2 and is not assumed anywhere in this file.  The equivalence
S1394PsiSqZeroCriterion W n ↔ DivisionPolynomialZeroCriterion W n is proved, so
either formulation may be used as the named input.  The n = 2 and n = 3
instances are discharged from S1373ZeroCriterionActual.  The TauCeti ZSMul
closure (the universal curve, smulX/smulY and zsmul_point_eq_smulEval) is the
missing proof of the general case; it is deliberately not vendored here.

## References

* [J Silverman, The Arithmetic of Elliptic Curves][silverman2009], III.6.4(b).
* TauCeti, AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Torsion/Roots.lean
  and DivisionPolynomial/ZSMul.lean (Lean v4.36.0-rc1).
-/

set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

open Polynomial
open LeanFormal.IUT.XiFPaper.S1372XCoordinateFormulaActual

namespace WeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

/-- The exact first lemma: TauCeti's pointwise PsiSq zero criterion, in the
current tree's language.  This is the general statement for which only the
n = 2 and n = 3 instances are unconditional here. -/
def S1394PsiSqZeroCriterion (W : WeierstrassCurve F) (n : ℤ) : Prop :=
  ∀ {x y : F} (hns : W.toAffine.Nonsingular x y),
    (W.ΨSq n).eval x = 0 ↔
      n • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0

/-! ## 1. Torsion transport between affine and Jacobian points -/

/-- Port of TauCeti's zsmul_fromAffine_eq_zero_iff_zsmul_eq_zero.  The
affine-to-Jacobian map is the inverse of the additive equivalence
Jacobian.Point.toAffineAddEquiv, so integer multiples vanish together. -/
lemma zsmul_fromAffine_eq_zero_iff_zsmul_eq_zero {E : WeierstrassCurve F}
    {P : Affine.Point E.toAffine} {n : ℤ} :
    n • Jacobian.Point.fromAffine P = 0 ↔ n • P = 0 := by
  let e := Jacobian.Point.toAffineAddEquiv E
  have h : e (n • Jacobian.Point.fromAffine P) = n • P := by
    rw [map_zsmul]
    congr 1
    exact AddEquiv.apply_symm_apply e P
  rw [← h, AddEquiv.map_eq_zero_iff e]

/-- Port of TauCeti's zsmul_fromAffine_eq_zero_iff: the natural-number-cast
form of the previous lemma. -/
lemma zsmul_fromAffine_eq_zero_iff {E : WeierstrassCurve F}
    {P : Affine.Point E.toAffine} {n : ℕ} :
    (n : ℤ) • Jacobian.Point.fromAffine P = 0 ↔ n • P = 0 := by
  rw [zsmul_fromAffine_eq_zero_iff_zsmul_eq_zero, natCast_zsmul]

/-! ## 2. The square bridge on the curve -/

/-- On a nonsingular point, the square of the evaluated bivariate division
polynomial is the evaluation of ΨSq.  This is the current tree's two evaluation
bridges composed. -/
lemma eval_ΨSq_eq_zero_iff_evalDivisionPolynomial_eq_zero {x y : F}
    (hns : W.toAffine.Nonsingular x y) (n : ℤ) :
    (W.ΨSq n).eval x = 0 ↔ W.evalDivisionPolynomial x y n = 0 := by
  have hbridge : (W.evalDivisionPolynomial x y n) ^ 2 = (W.ΨSq n).eval x := by
    rw [W.evalDivisionPolynomial_eq_evalEval_Ψ hns.1 n]
    exact W.evalEval_Ψ_sq_eq_eval_ΨSq hns.1 n
  rw [← hbridge, pow_eq_zero_iff two_ne_zero]

/-! ## 3. The criterion and the zero criterion are the same interface -/

/-- The TauCeti PsiSq criterion is exactly the current tree's
DivisionPolynomialZeroCriterion, read through the square bridge and the
affine/Jacobian torsion transport.  This is the precise adaptation of the
TauCeti conclusion to Mathlib v4.32.2. -/
theorem s1394PsiSqZeroCriterion_iff_zeroCriterion (n : ℤ) :
    W.S1394PsiSqZeroCriterion n ↔ W.DivisionPolynomialZeroCriterion n := by
  constructor
  · intro h P
    cases P with
    | zero => exact ⟨fun _ => rfl, fun _ => zsmul_zero (α := W.toAffine.Point) n⟩
    | some x y hns =>
      have h1 : W.evalDivisionPolynomial x y n = 0 ↔
          n • (Affine.Point.some x y hns) = 0 := by
        rw [← eval_ΨSq_eq_zero_iff_evalDivisionPolynomial_eq_zero W hns n,
          h hns, zsmul_fromAffine_eq_zero_iff_zsmul_eq_zero]
      simpa only [evalDivisionPolynomialAtPoint_some] using h1.symm
  · intro h x y hns
    have hsome := h (Affine.Point.some x y hns)
    rw [evalDivisionPolynomialAtPoint_some] at hsome
    rw [eval_ΨSq_eq_zero_iff_evalDivisionPolynomial_eq_zero W hns n,
      ← hsome, zsmul_fromAffine_eq_zero_iff_zsmul_eq_zero]

/-! ## 4. The TauCeti conclusions, conditional on the exact first lemma -/

/-- Port of TauCeti's eval_ΨSq_eq_zero_iff_zsmul_eq_zero, from the pointwise
criterion (the current tree's zero criterion). -/
theorem eval_ΨSq_eq_zero_iff_zsmul_eq_zero
    (h : W.S1394PsiSqZeroCriterion n) {x y : F}
    (hns : W.toAffine.Nonsingular x y) :
    (W.ΨSq n).eval x = 0 ↔
      n • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0 :=
  h hns

/-- The same conclusion from the current tree's DivisionPolynomialZeroCriterion
interface. -/
theorem eval_ΨSq_eq_zero_iff_zsmul_eq_zero_of_zeroCriterion
    (h : W.DivisionPolynomialZeroCriterion n) {x y : F}
    (hns : W.toAffine.Nonsingular x y) :
    (W.ΨSq n).eval x = 0 ↔
      n • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0 :=
  eval_ΨSq_eq_zero_iff_zsmul_eq_zero W
    ((s1394PsiSqZeroCriterion_iff_zeroCriterion W n).mpr h) hns

/-- The same conclusion from the two one-sided interfaces: detection of
torsion by the division polynomial, and the root half. -/
theorem eval_ΨSq_eq_zero_iff_zsmul_eq_zero_of_detects_and_roots
    (hdet : DivisionPolynomialDetectsTorsion W n)
    (hroot : W.DivisionPolynomialRootsAreTorsion n) {x y : F}
    (hns : W.toAffine.Nonsingular x y) :
    (W.ΨSq n).eval x = 0 ↔
      n • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0 :=
  eval_ΨSq_eq_zero_iff_zsmul_eq_zero_of_zeroCriterion W
    ((W.divisionPolynomialZeroCriterion_iff_detects n).mpr ⟨hdet, hroot⟩) hns

/-- Port of TauCeti's eval_ΨSq_ne_zero_of_zsmul_ne_zero: a nonzero multiple of
the point makes ΨSq nonzero at its abscissa. -/
theorem eval_ΨSq_ne_zero_of_zsmul_ne_zero
    (h : W.S1394PsiSqZeroCriterion n) {x y : F}
    (hns : W.toAffine.Nonsingular x y)
    (hP : n • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) ≠ 0) :
    (W.ΨSq n).eval x ≠ 0 := by
  intro hsq
  exact hP ((eval_ΨSq_eq_zero_iff_zsmul_eq_zero W h hns).mp hsq)

/-- The exact name requested by the separability consumer, with the criterion
as an explicit input. -/
theorem eval_ΨSq_ne_zero
    (h : W.S1394PsiSqZeroCriterion n) {x y : F}
    (hns : W.toAffine.Nonsingular x y)
    (hP : n • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) ≠ 0) :
    (W.ΨSq n).eval x ≠ 0 :=
  eval_ΨSq_ne_zero_of_zsmul_ne_zero W h hns hP

/-- The nonzero companion from the current tree's zero criterion. -/
theorem eval_ΨSq_ne_zero_of_zsmul_ne_zero_of_zeroCriterion
    (h : W.DivisionPolynomialZeroCriterion n) {x y : F}
    (hns : W.toAffine.Nonsingular x y)
    (hP : n • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) ≠ 0) :
    (W.ΨSq n).eval x ≠ 0 :=
  eval_ΨSq_ne_zero_of_zsmul_ne_zero W
    ((s1394PsiSqZeroCriterion_iff_zeroCriterion W n).mpr h) hns hP

/-! ## 5. The unconditional instances n = 2 and n = 3 -/

/-- The exact first lemma at n = 2, from the current tree's n = 2 zero
criterion. -/
theorem s1394PsiSqZeroCriterion_two : W.S1394PsiSqZeroCriterion 2 :=
  (s1394PsiSqZeroCriterion_iff_zeroCriterion W 2).mpr W.divisionPolynomialZeroCriterion_two

/-- The exact first lemma at n = 3, from the current tree's n = 3 zero
criterion. -/
theorem s1394PsiSqZeroCriterion_three : W.S1394PsiSqZeroCriterion 3 :=
  (s1394PsiSqZeroCriterion_iff_zeroCriterion W 3).mpr W.divisionPolynomialZeroCriterion_three

/-- TauCeti's iff at n = 2, unconditionally. -/
theorem eval_ΨSq_eq_zero_iff_zsmul_eq_zero_two {x y : F}
    (hns : W.toAffine.Nonsingular x y) :
    (W.ΨSq 2).eval x = 0 ↔
      (2 : ℤ) • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0 :=
  eval_ΨSq_eq_zero_iff_zsmul_eq_zero W W.s1394PsiSqZeroCriterion_two hns

/-- TauCeti's iff at n = 3, unconditionally. -/
theorem eval_ΨSq_eq_zero_iff_zsmul_eq_zero_three {x y : F}
    (hns : W.toAffine.Nonsingular x y) :
    (W.ΨSq 3).eval x = 0 ↔
      (3 : ℤ) • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0 :=
  eval_ΨSq_eq_zero_iff_zsmul_eq_zero W W.s1394PsiSqZeroCriterion_three hns

/-- The nonzero companion at n = 2, unconditionally. -/
theorem eval_ΨSq_ne_zero_two {x y : F} (hns : W.toAffine.Nonsingular x y)
    (hP : (2 : ℤ) • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) ≠ 0) :
    (W.ΨSq 2).eval x ≠ 0 := by
  intro hsq
  exact hP ((eval_ΨSq_eq_zero_iff_zsmul_eq_zero_two W hns).mp hsq)

/-- The nonzero companion at n = 3, unconditionally. -/
theorem eval_ΨSq_ne_zero_three {x y : F} (hns : W.toAffine.Nonsingular x y)
    (hP : (3 : ℤ) • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) ≠ 0) :
    (W.ΨSq 3).eval x ≠ 0 := by
  intro hsq
  exact hP ((eval_ΨSq_eq_zero_iff_zsmul_eq_zero_three W hns).mp hsq)

/-! ## 6. The detection half from the x-coordinate formula -/

/-- The direction n • P = 0 → ΨSq_n(x) = 0, proved from S1372's x-coordinate
formula x(nP) = Φ_n(x)/ψ_n(x,y)^2.  This is the half needed by the
separability count; the converse (a root of ΨSq_n is torsion) is the root half
of the zero criterion and is not assumed. -/
theorem eval_ΨSq_eq_zero_of_zsmul_eq_zero_of_xCoordinateFormula
    {n : ℤ} (hx : S1372XCoordinateFormula W.toAffine n)
    {x y : F} (hns : W.toAffine.Nonsingular x y)
    (hP : n • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0) :
    (W.ΨSq n).eval x = 0 := by
  by_contra hsq
  have hψ : W.evalDivisionPolynomial x y n ≠ 0 := by
    intro h0
    exact hsq ((eval_ΨSq_eq_zero_iff_evalDivisionPolynomial_eq_zero W hns n).mpr h0)
  have hcoord := hx x y hns hψ
  have haff : n • (Affine.Point.some x y hns) = 0 :=
    (zsmul_fromAffine_eq_zero_iff_zsmul_eq_zero (E := W) (P := Affine.Point.some x y hns)
      (n := n)).mp hP
  rw [haff] at hcoord
  simpa [xCoord] using hcoord

/-! ## 7. Existence form and the trivial-torsion criterion -/

/-- Over an algebraically closed field every x-coordinate is realised by a
point of the Weierstrass equation.  Ported from TauCeti's
Affine/IsAlgClosed.lean. -/
theorem Affine.exists_point_on_curve [IsAlgClosed F] (V : WeierstrassCurve.Affine F) (a : F) :
    ∃ b : F, V.Equation a b := by
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_root
    (C 1 * X ^ 2 + C (V.a₁ * a + V.a₃) * X + C (-(a ^ 3 + V.a₂ * a ^ 2 + V.a₄ * a + V.a₆)))
    (by rw [degree_quadratic one_ne_zero]; simp)
  rw [IsRoot.def] at hb
  simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X, one_mul] at hb
  exact ⟨b, (V.equation_iff a b).mpr (by linear_combination hb)⟩

/-- Port of TauCeti's eval_ΨSq_eq_zero_iff_exists_zsmul_eq_zero, conditional
on the pointwise criterion.  Over an algebraically closed field the auxiliary
y always exists, so the pointwise form becomes an existential statement. -/
theorem eval_ΨSq_eq_zero_iff_exists_zsmul_eq_zero [IsAlgClosed F] [W.IsElliptic]
    (h : W.S1394PsiSqZeroCriterion n) {x : F} :
    (W.ΨSq n).eval x = 0 ↔ ∃ y, ∃ hns : W.toAffine.Nonsingular x y,
      n • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0 := by
  refine ⟨fun hx ↦ ?_, fun ⟨_, hns, hh⟩ ↦
    (eval_ΨSq_eq_zero_iff_zsmul_eq_zero W h hns).mpr hh⟩
  obtain ⟨y, hy⟩ := W.toAffine.exists_point_on_curve x
  have hns : W.toAffine.Nonsingular x y := Affine.equation_iff_nonsingular.mp hy
  exact ⟨y, hns, (eval_ΨSq_eq_zero_iff_zsmul_eq_zero W h hns).mp hx⟩

/-- The existence form from the current tree's zero criterion. -/
theorem eval_ΨSq_eq_zero_iff_exists_zsmul_eq_zero_of_zeroCriterion
    [IsAlgClosed F] [W.IsElliptic] (h : W.DivisionPolynomialZeroCriterion n) {x : F} :
    (W.ΨSq n).eval x = 0 ↔ ∃ y, ∃ hns : W.toAffine.Nonsingular x y,
      n • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0 :=
  eval_ΨSq_eq_zero_iff_exists_zsmul_eq_zero W
    ((s1394PsiSqZeroCriterion_iff_zeroCriterion W n).mpr h)

/-- Port of TauCeti's torsionBy_eq_bot_iff_forall_eval_ΨSq_ne_zero, conditional
on the pointwise criterion. -/
theorem torsionBy_eq_bot_iff_forall_eval_ΨSq_ne_zero [IsAlgClosed F] [W.IsElliptic]
    (h : W.S1394PsiSqZeroCriterion n) :
    AddSubgroup.torsionBy W.toAffine.Point n = ⊥ ↔ ∀ x, (W.ΨSq n).eval x ≠ 0 := by
  simp only [AddSubgroup.eq_bot_iff_forall, Submodule.mem_toAddSubgroup,
    Submodule.mem_torsionBy_iff]
  refine ⟨fun hbot x hx ↦ ?_, ?_⟩
  · obtain ⟨y, hns, htors⟩ :=
      (eval_ΨSq_eq_zero_iff_exists_zsmul_eq_zero W h).mp hx
    exact Affine.Point.some_ne_zero hns
      (hbot _ (zsmul_fromAffine_eq_zero_iff_zsmul_eq_zero.mp htors))
  · rintro hzero (_ | ⟨x, y, hns⟩) hP
    · rfl
    · exact absurd ((eval_ΨSq_eq_zero_iff_zsmul_eq_zero W h hns).mpr
        (zsmul_fromAffine_eq_zero_iff_zsmul_eq_zero.mpr hP)) (hzero x)

/-- The torsionBy form from the current tree's zero criterion. -/
theorem torsionBy_eq_bot_iff_forall_eval_ΨSq_ne_zero_of_zeroCriterion
    [IsAlgClosed F] [W.IsElliptic] (h : W.DivisionPolynomialZeroCriterion n) :
    AddSubgroup.torsionBy W.toAffine.Point n = ⊥ ↔ ∀ x, (W.ΨSq n).eval x ≠ 0 :=
  torsionBy_eq_bot_iff_forall_eval_ΨSq_ne_zero W
    ((s1394PsiSqZeroCriterion_iff_zeroCriterion W n).mpr h)

/-! ## 8. Axiom footprint -/

#print axioms zsmul_fromAffine_eq_zero_iff_zsmul_eq_zero
#print axioms s1394PsiSqZeroCriterion_iff_zeroCriterion
#print axioms eval_ΨSq_eq_zero_iff_zsmul_eq_zero_of_detects_and_roots
#print axioms eval_ΨSq_eq_zero_iff_zsmul_eq_zero_two
#print axioms eval_ΨSq_eq_zero_iff_zsmul_eq_zero_three
#print axioms eval_ΨSq_eq_zero_of_zsmul_eq_zero_of_xCoordinateFormula
#print axioms eval_ΨSq_eq_zero_iff_exists_zsmul_eq_zero
#print axioms torsionBy_eq_bot_iff_forall_eval_ΨSq_ne_zero
#print axioms eval_ΨSq_ne_zero_two
#print axioms eval_ΨSq_ne_zero_three
#print axioms eval_ΨSq_eq_zero_iff_exists_zsmul_eq_zero_of_zeroCriterion
#print axioms torsionBy_eq_bot_iff_forall_eval_ΨSq_ne_zero_of_zeroCriterion

end WeierstrassCurve