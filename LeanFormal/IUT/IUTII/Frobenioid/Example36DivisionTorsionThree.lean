/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal IUT/ABC contributors
-/
import LeanFormal.IUT.ABCBridge.Galois.EllipticDivisionPolynomialEvaluation
import LeanFormal.IUT.IUTII.Frobenioid.Example36EllipticCurveAnabelioid
import Mathlib.Tactic

set_option linter.unusedSectionVars false

/-!
# The concrete 3-torsion division-polynomial criterion for y^2 = x^3 - x

Foundation F4b (odd torsion criterion).  This module proves, from Mathlib's
division polynomial psi_3 and the affine group law, the concrete 3-torsion
criterion

  3 • P = 0  <->  psi_3(P) = 0

for the Weierstrass curve y^2 = x^3 - x over a field K of characteristic
different from 2, for affine points and for the point at infinity.  The
criterion is used to define the actual 3-torsion subgroup and to prove that it
is nontrivial over any algebraically closed field of characteristic zero.

## Mathematical content

* y2x3xCurve: the curve y^2 = x^3 - x over K.
* y2x3xCurve_eval_Ψ₃: psi_3 evaluated at the x-coordinate is
  3 x^4 - 6 x^2 - 1 (the explicit Mathlib polynomial Ψ₃).
* y2x3xCurve_Ψ₃_eval_eq_zero_iff: psi_3(x) = 0 iff (3x^2-1)^2 = 12 x y^2,
  under the curve equation y^2 = x^3 - x (this is the algebraic heart: the
  condition x(2P) = x).
* y2x3xCurve_addX_double_eq_iff: x(2P) = x iff psi_3(P) = 0, for an affine
  nonsingular point with y != -y (equivalently 2y != 0).
* three_nsmul_some_eq_zero_iff and three_nsmul_eq_zero_iff: the full
  criterion for affine points and the point at infinity, from the affine group
  law: 3P = P + 2P, and 3P = 0 iff 2P = -P, which holds iff x(2P) = x and P is
  not the identity; the same x-condition is psi_3(P) = 0.
* threeTorsionSubgroup and its membership criterion in terms of the actual
  group law and in terms of psi_3.
* exists_threeTorsionOfY2x3xCurve: over any algebraically closed field of
  characteristic zero, E[3] has a nonzero element: choose a root x of Ψ₃
  (proved nonconstant by two evaluations), a square root y of x^3-x, check
  nonsingularity, and apply the criterion.

## Generalization and boundary

The proof is stated for the family y^2 = x^3 - x over an arbitrary field with
2 != 0, not only over Q.  The concrete curve curveY2EqX3SubX of
Example36EllipticCurveAnabelioid.lean is definitionally this family at Q, and
the base-change comparison curveY2EqX3SubX_baseChange_eq rewrites its base
changes to the family.  The method is special to n = 3: it uses 3P = P + 2P and
the duplication formula, so the reduction to a condition on the x-coordinate of
2P.  Mathlib provides psi_n and prePsi_n for all n, but not the group-law
correspondence n • P = 0 <-> psi_n(P) = 0 for n >= 3; for odd n > 3 the
corresponding bridge is frozen as the card oddNsmulDivisionPolynomialCriterionCard
and is not proved here.  Finiteness of E[3] is frozen as
threeTorsionFinitenessCard: the available proof route (finitely many roots of
the quartic Ψ₃, at most two y-coordinates per root, plus the point at infinity)
is recorded but not formalized.  No inverse limit, Tate module, theta/q-pilot or
Anabelian claim is made here.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36
namespace DivisionTorsionThree

open Polynomial
open scoped Polynomial.Bivariate
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36

variable {K : Type*} [Field K]

/-- The curve y^2 = x^3 - x over a field K. -/
def y2x3xCurve : WeierstrassCurve K where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -1
  a₆ := 0

@[simp] lemma y2x3xCurve_a1 : (y2x3xCurve (K := K)).a₁ = 0 := rfl
@[simp] lemma y2x3xCurve_a2 : (y2x3xCurve (K := K)).a₂ = 0 := rfl
@[simp] lemma y2x3xCurve_a3 : (y2x3xCurve (K := K)).a₃ = 0 := rfl
@[simp] lemma y2x3xCurve_a4 : (y2x3xCurve (K := K)).a₄ = -1 := rfl
@[simp] lemma y2x3xCurve_a6 : (y2x3xCurve (K := K)).a₆ = 0 := rfl

lemma y2x3xCurve_negY (x y : K) :
    (y2x3xCurve (K := K)).toAffine.negY x y = -y := by
  simp [WeierstrassCurve.Affine.negY]

lemma y2x3xCurve_equation (x y : K) (h : (y2x3xCurve (K := K)).toAffine.Equation x y) :
    y ^ 2 = x ^ 3 - x := by
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [y2x3xCurve_a1, y2x3xCurve_a2, y2x3xCurve_a3, y2x3xCurve_a4, y2x3xCurve_a6] at h
  linear_combination h

lemma y2x3xCurve_eval_Ψ₃ (x : K) :
    (y2x3xCurve (K := K)).Ψ₃.eval x = 3 * x ^ 4 - 6 * x ^ 2 - 1 := by
  rw [WeierstrassCurve.Ψ₃]
  simp only [y2x3xCurve_a1, y2x3xCurve_a2, y2x3xCurve_a3, y2x3xCurve_a4, y2x3xCurve_a6,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  simp
  ring

section DecidableEq
variable [DecidableEq K]

lemma y2x3xCurve_slope_double (x y : K) (hy : y ≠ (y2x3xCurve (K := K)).toAffine.negY x y) :
    (y2x3xCurve (K := K)).toAffine.slope x x y y = (3 * x ^ 2 - 1) / (2 * y) := by
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
  simp only [y2x3xCurve_a1, y2x3xCurve_a2, y2x3xCurve_a4, y2x3xCurve_negY]
  rw [show y - (-y) = 2 * y from by ring]
  ring_nf

end DecidableEq

lemma y2x3xCurve_addX_double (x ℓ : K) :
    (y2x3xCurve (K := K)).toAffine.addX x x ℓ = ℓ ^ 2 - 2 * x := by
  simp [WeierstrassCurve.Affine.addX]
  ring

lemma y2x3xCurve_Ψ₃_eval_eq_zero_iff (x y : K) (h : y ^ 2 = x ^ 3 - x) :
    (y2x3xCurve (K := K)).Ψ₃.eval x = 0 ↔
      (3 * x ^ 2 - 1) ^ 2 = 12 * x * y ^ 2 := by
  rw [y2x3xCurve_eval_Ψ₃]
  have hident : (3 * x ^ 2 - 1) ^ 2 - 12 * x * y ^ 2 =
      -(3 * x ^ 4 - 6 * x ^ 2 - 1) := by
    linear_combination (-12 * x) * h
  constructor
  · intro hψ
    have h0 : (3 * x ^ 2 - 1) ^ 2 - 12 * x * y ^ 2 = 0 := by
      rw [hident, hψ]; ring
    exact sub_eq_zero.mp h0
  · intro heq
    have h0 : -(3 * x ^ 4 - 6 * x ^ 2 - 1) = 0 := by
      rw [← hident, heq]; ring
    exact neg_eq_zero.mp h0

lemma y2x3xCurve_two_mul_y_ne_zero (x y : K) (h2 : (2 : K) ≠ 0)
    (hy : y ≠ (y2x3xCurve (K := K)).toAffine.negY x y) :
    (2 : K) * y ≠ 0 := by
  have hy0 : y ≠ 0 := by
    intro h0
    apply hy
    simp [h0]
  exact mul_ne_zero h2 hy0

section Criterion
variable [DecidableEq K]

lemma y2x3xCurve_addX_double_eq_iff (x y : K)
    (h : (y2x3xCurve (K := K)).toAffine.Equation x y)
    (hy : y ≠ (y2x3xCurve (K := K)).toAffine.negY x y) (h2 : (2 : K) ≠ 0) :
    (y2x3xCurve (K := K)).toAffine.addX x x
        ((y2x3xCurve (K := K)).toAffine.slope x x y y) = x ↔
      (y2x3xCurve (K := K)).Ψ₃.eval x = 0 := by
  have h2y : (2 : K) * y ≠ 0 := y2x3xCurve_two_mul_y_ne_zero x y h2 hy
  have hy0 : y ≠ 0 := by
    intro h0
    apply hy
    simp [h0]
  have heq : y ^ 2 = x ^ 3 - x := y2x3xCurve_equation x y h
  rw [y2x3xCurve_addX_double, y2x3xCurve_slope_double x y hy,
    y2x3xCurve_Ψ₃_eval_eq_zero_iff x y heq]
  have h2ysq : ((2 : K) * y) ^ 2 ≠ 0 := pow_ne_zero 2 h2y
  constructor
  · intro hx
    have hx' : (3 * x ^ 2 - 1) ^ 2 / ((2 : K) * y) ^ 2 - 2 * x = x := by
      simpa [div_pow] using hx
    have h1 : (3 * x ^ 2 - 1) ^ 2 / ((2 : K) * y) ^ 2 = 3 * x := by
      linear_combination hx'
    have h1m := congrArg (fun t : K => t * ((2 : K) * y) ^ 2) h1
    have h2' : (3 * x ^ 2 - 1) ^ 2 = 3 * x * ((2 : K) * y) ^ 2 := by
      rwa [div_mul_cancel₀ _ h2ysq] at h1m
    have h4 : ((2 : K) * y) ^ 2 = 4 * y ^ 2 := by ring
    rw [h4] at h2'
    linear_combination h2'
  · intro heq2
    have h4 : ((2 : K) * y) ^ 2 = 4 * y ^ 2 := by ring
    have h1 : (3 * x ^ 2 - 1) ^ 2 = 3 * x * (4 * y ^ 2) := by
      rw [← h4]
      linear_combination heq2
    have h4y : (4 : K) * y ^ 2 ≠ 0 := by
      have h4' : (4 : K) ≠ 0 := by
        have : (4 : K) = 2 * 2 := by norm_num
        rw [this]
        exact mul_ne_zero h2 h2
      exact mul_ne_zero h4' (pow_ne_zero 2 hy0)
    rw [div_pow, h4, h1]
    rw [show (3 * x * (4 * y ^ 2)) / (4 * y ^ 2) = 3 * x from
      mul_div_cancel_right₀ (3 * x) h4y]
    ring

end Criterion


lemma y2x3xCurve_eval_Ψ₃_ne_zero_of_Y_eq_negY (x y : K) (h2 : (2 : K) ≠ 0)
    (heq : y ^ 2 = x ^ 3 - x)
    (hy : y = (y2x3xCurve (K := K)).toAffine.negY x y) :
    (y2x3xCurve (K := K)).Ψ₃.eval x ≠ 0 := by
  have hyneg : y = -y := by simpa [y2x3xCurve_negY] using hy
  have h2y : y + y = 0 := by linear_combination hyneg
  have h2y' : (2 : K) * y = 0 := by simpa [two_mul] using h2y
  have hy0 : y = 0 := (mul_eq_zero.mp h2y').resolve_left h2
  have hx3 : x ^ 3 - x = 0 := by
    rw [← heq, hy0]; ring
  have hfac : x * (x - 1) * (x + 1) = 0 := by
    have h : x * (x - 1) * (x + 1) = x ^ 3 - x := by ring
    rwa [h]
  have h4 : (4 : K) ≠ 0 := by
    have h : (4 : K) = 2 * 2 := by norm_num
    rw [h]
    exact mul_ne_zero h2 h2
  rw [y2x3xCurve_eval_Ψ₃]
  rcases mul_eq_zero.mp hfac with hx | hx
  · rcases mul_eq_zero.mp hx with hx0 | hx1
    · subst hx0
      intro hz
      norm_num at hz
    · have hxone : x = 1 := by linear_combination hx1
      subst hxone
      intro hz
      have hz' : (4 : K) = 0 := by linear_combination -hz
      exact h4 hz'
  · intro hz
    have hxneg : x = -1 := by linear_combination hx
    subst hxneg
    have hz' : (4 : K) = 0 := by linear_combination -hz
    exact h4 hz'

section MainCriterion
variable [DecidableEq K]

theorem three_nsmul_some_eq_zero_iff (h2 : (2 : K) ≠ 0) {x y : K}
    (h : (y2x3xCurve (K := K)).toAffine.Nonsingular x y) :
    (3 : ℕ) • (WeierstrassCurve.Affine.Point.some x y h) = 0 ↔
      (y2x3xCurve (K := K)).evalDivisionPolynomialAtPoint 3
        (WeierstrassCurve.Affine.Point.some x y h) = 0 := by
  classical
  by_cases hy : y = (y2x3xCurve (K := K)).toAffine.negY x y
  · have heq : y ^ 2 = x ^ 3 - x := y2x3xCurve_equation x y h.1
    have hψ : (y2x3xCurve (K := K)).evalDivisionPolynomialAtPoint 3
        (WeierstrassCurve.Affine.Point.some x y h) ≠ 0 := by
      rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_some,
        (y2x3xCurve (K := K)).evalDivisionPolynomial_eq_eval_preΨ_of_odd h.1
          (by decide : ¬ Even (3 : ℤ)),
        (y2x3xCurve (K := K)).preΨ_three]
      exact y2x3xCurve_eval_Ψ₃_ne_zero_of_Y_eq_negY x y h2 heq hy
    have hPP : WeierstrassCurve.Affine.Point.some x y h +
        WeierstrassCurve.Affine.Point.some x y h = 0 :=
      WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy
    have hL : (3 : ℕ) • WeierstrassCurve.Affine.Point.some x y h =
        WeierstrassCurve.Affine.Point.some x y h := by
      rw [three_nsmul, hPP, add_zero]
    constructor
    · intro hz
      rw [hL] at hz
      exact absurd hz (WeierstrassCurve.Affine.Point.some_ne_zero h)
    · intro hz
      exact absurd hz hψ
  · have hPP : WeierstrassCurve.Affine.Point.some x y h +
        WeierstrassCurve.Affine.Point.some x y h =
        WeierstrassCurve.Affine.Point.some
          ((y2x3xCurve (K := K)).toAffine.addX x x
            ((y2x3xCurve (K := K)).toAffine.slope x x y y))
          ((y2x3xCurve (K := K)).toAffine.addY x x y
            ((y2x3xCurve (K := K)).toAffine.slope x x y y))
          (WeierstrassCurve.Affine.nonsingular_add h h (fun hxy => hy hxy.2)) :=
      WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy
    have hPne : WeierstrassCurve.Affine.Point.some x y h ≠ 0 :=
      WeierstrassCurve.Affine.Point.some_ne_zero h
    constructor
    · intro hz
      rw [three_nsmul, add_comm, add_eq_zero_iff_eq_neg, hPP] at hz
      rw [WeierstrassCurve.Affine.Point.neg_some] at hz
      have hxeq : (y2x3xCurve (K := K)).toAffine.addX x x
          ((y2x3xCurve (K := K)).toAffine.slope x x y y) = x := by
        have hpair := (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mp hz
        exact hpair.1
      rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_some,
        (y2x3xCurve (K := K)).evalDivisionPolynomial_eq_eval_preΨ_of_odd h.1
          (by decide : ¬ Even (3 : ℤ)),
        (y2x3xCurve (K := K)).preΨ_three]
      exact (y2x3xCurve_addX_double_eq_iff x y h.1 hy h2).mp hxeq
    · intro hψ
      rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_some,
        (y2x3xCurve (K := K)).evalDivisionPolynomial_eq_eval_preΨ_of_odd h.1
          (by decide : ¬ Even (3 : ℤ)),
        (y2x3xCurve (K := K)).preΨ_three] at hψ
      have hxeq : (y2x3xCurve (K := K)).toAffine.addX x x
          ((y2x3xCurve (K := K)).toAffine.slope x x y y) = x :=
        (y2x3xCurve_addX_double_eq_iff x y h.1 hy h2).mpr hψ
      set Q : (y2x3xCurve (K := K)).toAffine.Point :=
        WeierstrassCurve.Affine.Point.some
          ((y2x3xCurve (K := K)).toAffine.addX x x
            ((y2x3xCurve (K := K)).toAffine.slope x x y y))
          ((y2x3xCurve (K := K)).toAffine.addY x x y
            ((y2x3xCurve (K := K)).toAffine.slope x x y y))
          (WeierstrassCurve.Affine.nonsingular_add h h (fun hxy => hy hxy.2)) with hQdef
      have hQ : Q = WeierstrassCurve.Affine.Point.some x y h +
          WeierstrassCurve.Affine.Point.some x y h := hPP.symm
      have hdisj : Q = WeierstrassCurve.Affine.Point.some x y h ∨
          Q = -WeierstrassCurve.Affine.Point.some x y h := by
        rw [hQdef]
        exact (WeierstrassCurve.Affine.Point.X_eq_iff
          (x₁ := (y2x3xCurve (K := K)).toAffine.addX x x
            ((y2x3xCurve (K := K)).toAffine.slope x x y y))
          (y₁ := (y2x3xCurve (K := K)).toAffine.addY x x y
            ((y2x3xCurve (K := K)).toAffine.slope x x y y))
          (x₂ := x) (y₂ := y)
          (h₁ := WeierstrassCurve.Affine.nonsingular_add h h (fun hxy => hy hxy.2))
          (h₂ := h)).mp hxeq
      rcases hdisj with hcase | hcase
      · exfalso
        have hP0 : WeierstrassCurve.Affine.Point.some x y h = 0 := by
          have hsame : WeierstrassCurve.Affine.Point.some x y h +
              WeierstrassCurve.Affine.Point.some x y h =
              WeierstrassCurve.Affine.Point.some x y h := by
            rw [← hQ, hcase]
          have hsame' : WeierstrassCurve.Affine.Point.some x y h +
              WeierstrassCurve.Affine.Point.some x y h =
              WeierstrassCurve.Affine.Point.some x y h + 0 := by
            simpa only [add_zero] using hsame
          exact add_left_cancel hsame'
        exact hPne hP0
      · rw [three_nsmul]
        rw [← hQ, hcase, add_neg_cancel]

theorem three_nsmul_eq_zero_iff (h2 : (2 : K) ≠ 0)
    (P : (y2x3xCurve (K := K)).toAffine.Point) :
    (3 : ℕ) • P = 0 ↔
      (y2x3xCurve (K := K)).evalDivisionPolynomialAtPoint 3 P = 0 := by
  cases P with
  | zero => exact iff_of_true (nsmul_zero 3) rfl
  | some x y h => exact three_nsmul_some_eq_zero_iff h2 h
end MainCriterion

/-! ## Nontriviality of E[3] over algebraically closed fields of characteristic zero -/

lemma y2x3xCurve_Ψ₃_degree_ne_zero (L : Type*) [Field L] [CharZero L] :
    (y2x3xCurve (K := L)).Ψ₃.degree ≠ 0 := by
  intro hdeg
  have hle : (y2x3xCurve (K := L)).Ψ₃.degree ≤ 0 := le_of_eq hdeg
  have hnat : (y2x3xCurve (K := L)).Ψ₃.natDegree = 0 :=
    Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr hle
  have hconst : (y2x3xCurve (K := L)).Ψ₃ =
      C ((y2x3xCurve (K := L)).Ψ₃.coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hnat
  have h0e : (y2x3xCurve (K := L)).Ψ₃.eval 0 = -1 := by
    rw [y2x3xCurve_eval_Ψ₃]; norm_num
  have h1e : (y2x3xCurve (K := L)).Ψ₃.eval 1 = -4 := by
    rw [y2x3xCurve_eval_Ψ₃]; norm_num
  rw [hconst] at h0e h1e
  simp only [Polynomial.eval_C] at h0e h1e
  have h3 : (3 : L) ≠ 0 := by norm_num
  have heq : (-1 : L) = -4 := h0e.symm.trans h1e
  have hzero : (3 : L) = 0 := by linear_combination heq
  exact h3 hzero

theorem exists_threeTorsionOfY2x3xCurve (L : Type*) [Field L] [DecidableEq L]
    [IsAlgClosed L] [CharZero L] :
    ∃ P : (y2x3xCurve (K := L)).toAffine.Point, (3 : ℕ) • P = 0 ∧ P ≠ 0 := by
  classical
  have hdeg : (y2x3xCurve (K := L)).Ψ₃.degree ≠ 0 :=
    y2x3xCurve_Ψ₃_degree_ne_zero L
  obtain ⟨x, hxroot⟩ := IsAlgClosed.exists_root (y2x3xCurve (K := L)).Ψ₃ hdeg
  have hxe : (y2x3xCurve (K := L)).Ψ₃.eval x = 0 := hxroot
  obtain ⟨y, hy2⟩ := IsAlgClosed.exists_pow_nat_eq (x ^ 3 - x) (by decide : 0 < 2)
  have hy2' : y ^ 2 = x ^ 3 - x := hy2
  have hEq : (y2x3xCurve (K := L)).toAffine.Equation x y := by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [y2x3xCurve_a1, y2x3xCurve_a2, y2x3xCurve_a3, y2x3xCurve_a4, y2x3xCurve_a6]
    linear_combination hy2'
  have hns : (y2x3xCurve (K := L)).toAffine.Nonsingular x y := by
    rw [WeierstrassCurve.Affine.nonsingular_iff]
    refine ⟨hEq, ?_⟩
    by_cases hy0 : y = 0
    · left
      have hx3 : x ^ 3 - x = 0 := by rw [← hy2', hy0]; ring
      have hfac : x * (x - 1) * (x + 1) = 0 := by
        have h : x * (x - 1) * (x + 1) = x ^ 3 - x := by ring
        rwa [h]
      simp only [y2x3xCurve_a1, y2x3xCurve_a2, y2x3xCurve_a4]
      rcases mul_eq_zero.mp hfac with hx | hx
      · rcases mul_eq_zero.mp hx with hx0 | hx1
        · subst hx0; norm_num
        · have hxone : x = 1 := by linear_combination hx1
          subst hxone; norm_num
      · have hxneg : x = -1 := by linear_combination hx
        subst hxneg; norm_num
    · right
      simp only [y2x3xCurve_a1, y2x3xCurve_a3]
      intro hneg
      apply hy0
      have h2y : (2 : L) * y = 0 := by linear_combination hneg
      exact (mul_eq_zero.mp h2y).resolve_left (by norm_num)
  let P : (y2x3xCurve (K := L)).toAffine.Point :=
    WeierstrassCurve.Affine.Point.some x y hns
  refine ⟨P, ?_, ?_⟩
  · exact (three_nsmul_eq_zero_iff (K := L) (by norm_num : (2 : L) ≠ 0) P).mpr (by
      rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_some,
        (y2x3xCurve (K := L)).evalDivisionPolynomial_eq_eval_preΨ_of_odd hEq
          (by decide : ¬ Even (3 : ℤ)),
        (y2x3xCurve (K := L)).preΨ_three]
      exact hxe)
  · exact WeierstrassCurve.Affine.Point.some_ne_zero hns



/-! ## Concrete curve and base change -/

/-- The concrete curve of Example36EllipticCurveAnabelioid.lean is the family
y^2 = x^3 - x at K = Q. -/
theorem curveY2EqX3SubX_eq : curveY2EqX3SubX = y2x3xCurve (K := ℚ) := rfl

/-- psi_3 evaluated at the x-coordinate of the concrete curve. -/
theorem curveY2EqX3SubX_eval_Ψ₃ (x : ℚ) :
    curveY2EqX3SubX.Ψ₃.eval x = 3 * x ^ 4 - 6 * x ^ 2 - 1 := by
  rw [curveY2EqX3SubX_eq]
  exact y2x3xCurve_eval_Ψ₃ x

/-- The 3-torsion criterion for the concrete curve over Q. -/
theorem three_nsmul_eq_zero_iff_curveY2EqX3SubX
    (P : curveY2EqX3SubX.toAffine.Point) :
    (3 : ℕ) • P = 0 ↔
      curveY2EqX3SubX.evalDivisionPolynomialAtPoint 3 P = 0 :=
  three_nsmul_eq_zero_iff (K := ℚ) (by norm_num) P

/-- Base change of the concrete curve to any field K is the family
y^2 = x^3 - x over K. -/
theorem curveY2EqX3SubX_baseChange_eq (K : Type*) [Field K] [Algebra ℚ K] :
    curveY2EqX3SubX.baseChange K = y2x3xCurve (K := K) := by
  ext <;> simp [WeierstrassCurve.baseChange, curveY2EqX3SubX, y2x3xCurve]

/-- The 3-torsion subgroup of the family y^2 = x^3 - x, as the actual kernel
of multiplication by 3 on the affine group. -/
noncomputable def threeTorsionSubgroup (K : Type*) [Field K] [DecidableEq K] :
    AddSubgroup (y2x3xCurve (K := K)).toAffine.Point :=
  AddSubgroup.torsionBy _ 3

/-- Membership in the actual 3-torsion subgroup is exactly the group-law
condition 3 • P = 0. -/
theorem threeTorsionSubgroup_mem_iff (K : Type*) [Field K] [DecidableEq K]
    (P : (y2x3xCurve (K := K)).toAffine.Point) :
    P ∈ threeTorsionSubgroup K ↔ (3 : ℕ) • P = 0 :=
  Iff.rfl

/-- Membership in the actual 3-torsion subgroup is exactly the vanishing of
the 3-division polynomial. -/
theorem threeTorsionSubgroup_mem_iff_eval (K : Type*) [Field K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) (P : (y2x3xCurve (K := K)).toAffine.Point) :
    P ∈ threeTorsionSubgroup K ↔
      (y2x3xCurve (K := K)).evalDivisionPolynomialAtPoint 3 P = 0 :=
  three_nsmul_eq_zero_iff h2 P

/-! ## Frozen cards: finiteness of E[3] and the general odd-n bridge -/

/-- **Frozen card: finiteness of the 3-torsion subgroup** of the family
y^2 = x^3 - x over a field K with 2 != 0 and 3 != 0.  The intended proof uses
the criterion: affine 3-torsion points have x among the roots of the quartic
Ψ₃ (finitely many) and at most two y-coordinates per root; the point at
infinity is the remaining point.  This proposition is a card, not a theorem,
and it is not consumed. -/
def threeTorsionFinitenessCard (K : Type*) [Field K] [DecidableEq K] : Prop :=
  (2 : K) ≠ 0 → (3 : K) ≠ 0 → Finite (threeTorsionSubgroup K)

/-- **Frozen card: the odd-n group-law to division-polynomial bridge.**  For
every odd n >= 3 and every field K with 2 != 0, an affine point is n-torsion
if and only if psi_n vanishes at it (with psi_n evaluated by
evalDivisionPolynomialAtPoint).  Mathlib has psi n and prePsi n for all n but
no nsmul correspondence for n >= 3; only n = 3 is proved in this file.  This is
a card, not a theorem, and it is not consumed. -/
def oddNsmulDivisionPolynomialCriterionCard : Prop :=
  ∀ (K : Type*) [Field K] [DecidableEq K], (2 : K) ≠ 0 →
    ∀ (n : ℕ), n ≠ 0 → Odd n →
      ∀ P : (y2x3xCurve (K := K)).toAffine.Point,
        (n : ℕ) • P = 0 ↔
          (y2x3xCurve (K := K)).evalDivisionPolynomialAtPoint (n : ℤ) P = 0

end DivisionTorsionThree
end Example36
end LeanFormal.IUT.IUTII.Frobenioid

namespace LeanFormal.IUT.Audit

/-- Audit record for Foundation F4b. -/
def example36DivisionTorsionThree : Obligation :=
  { id := "IUT-I-II.example36-division-torsion-three"
    source :=
      "IUT I, Definition 3.1(c) torsion data; Mathlib division polynomials psi_3"
    status := VerificationStatus.provedKernel
    note :=
      "Proved: the concrete 3-torsion criterion 3 • P = 0 <-> psi_3(P) = 0 for " ++
        "y^2 = x^3 - x over any field with 2 != 0, for affine points and the " ++
        "point at infinity, from Mathlib's psi_3 and the affine group law " ++
        "(3P = P + 2P, 3P = 0 <-> 2P = -P <-> x(2P) = x, and the algebraic " ++
        "identity psi_3(x) = 0 <-> (3x^2-1)^2 = 12 x y^2).  Also proved: the " ++
        "explicit psi_3 evaluation 3x^4 - 6x^2 - 1, the x(2P) = x criterion, " ++
        "definition of the actual 3-torsion subgroup with both membership " ++
        "forms, and nontriviality of E[3] over any algebraically closed field " ++
        "of characteristic zero.  Boundary: over Q the concrete curve is " ++
        "definitionally the family; base changes are compared by a proved " ++
        "equality.  Not proved (frozen cards): finiteness of E[3] " ++
        "(threeTorsionFinitenessCard) and the odd-n bridge for n > 3 " ++
        "(oddNsmulDivisionPolynomialCriterionCard).  No Tate module, inverse " ++
        "limit, theta/q-pilot or Anabelian claim."
    dependsOn :=
      [ "Foundations.Geometry.elliptic-torsion-galois",
        "IUT-I-II.example36-elliptic-curve-anabelioid" ] }

end LeanFormal.IUT.Audit
