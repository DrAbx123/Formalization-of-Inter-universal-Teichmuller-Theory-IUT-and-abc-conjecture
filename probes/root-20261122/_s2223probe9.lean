
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import LeanFormal.IUT.ABCBridge.Galois.EllipticDivisionPolynomialEvaluation

noncomputable section
open WeierstrassCurve
open Polynomial

namespace S2223Probe

variable {F : Type*} [Field F] [CharZero F]

noncomputable local instance decEqAlgClosure : DecidableEq (AlgebraicClosure F) := Classical.decEq _

theorem twoTorsionPolynomial_baseChange (W : WeierstrassCurve F) (L : Type*) [Field L] [Algebra F L] :
    (W.baseChange L).twoTorsionPolynomial =
      (W.twoTorsionPolynomial).map (algebraMap F L) := by
  ext <;>
    simp only [Cubic.map, WeierstrassCurve.twoTorsionPolynomial, WeierstrassCurve.baseChange,
      WeierstrassCurve.map, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      map_ofNat, map_add, map_mul, map_pow]
  all_goals ring

theorem twoTorsionPoint_of_root
    (W : WeierstrassCurve F) [W.IsElliptic]
    (L : Type*) [Field L] [CharZero L] [Algebra F L] [DecidableEq L] (x : L)
    (hx : (W.baseChange L).twoTorsionPolynomial.toPoly.eval x = 0) :
    ∃ (y : L) (h : (W.baseChange L).toAffine.Nonsingular x y),
      (2 : Nat) • (WeierstrassCurve.Affine.Point.some x y h) = 0 := by
  let y : L := -((W.baseChange L).a₁ * x + (W.baseChange L).a₃) / 2
  have heq : (W.baseChange L).toAffine.Equation x y := by
    rw [WeierstrassCurve.Affine.equation_iff]
    rw [WeierstrassCurve.twoTorsionPolynomial] at hx
    simp only [Cubic.toPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X] at hx
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆] at hx
    change y ^ 2 + (W.baseChange L).a₁ * x * y + (W.baseChange L).a₃ * y =
      x ^ 3 + (W.baseChange L).a₂ * x ^ 2 + (W.baseChange L).a₄ * x + (W.baseChange L).a₆
    subst y
    field_simp
    ring_nf at hx
    ring_nf
    linear_combination (-1 : L) * hx
  have hΔ : (W.baseChange L).Δ ≠ 0 := by
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ]
    exact (map_ne_zero (algebraMap F L)).mpr (W.isUnit_Δ.ne_zero)
  have hns : (W.baseChange L).toAffine.Nonsingular x y :=
    (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero (W := (W.baseChange L)) hΔ).mp heq
  refine ⟨y, hns, ?_⟩
  have hdiv : (W.baseChange L).evalDivisionPolynomial x y 2 = 0 := by
    rw [WeierstrassCurve.evalDivisionPolynomial_two]
    change 2 * y + (W.baseChange L).a₁ * x + (W.baseChange L).a₃ = 0
    subst y
    field_simp
    ring
  have hy : y = (W.baseChange L).toAffine.negY x y :=
    (WeierstrassCurve.evalDivisionPolynomial_two_eq_zero_iff_negY (W := (W.baseChange L))).mp hdiv
  rw [show (2 : Nat) • (WeierstrassCurve.Affine.Point.some x y hns) =
      WeierstrassCurve.Affine.Point.some x y hns + WeierstrassCurve.Affine.Point.some x y hns by
    rw [two_nsmul]]
  exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy

set_option maxHeartbeats 1000000 in
theorem exists_three_twoTorsionPoints
    (W : WeierstrassCurve F) [W.IsElliptic] :
    ∃ (x₁ x₂ x₃ : AlgebraicClosure F)
      (y₁ y₂ y₃ : AlgebraicClosure F)
      (h₁ : (W.baseChange (AlgebraicClosure F)).toAffine.Nonsingular x₁ y₁)
      (h₂ : (W.baseChange (AlgebraicClosure F)).toAffine.Nonsingular x₂ y₂)
      (h₃ : (W.baseChange (AlgebraicClosure F)).toAffine.Nonsingular x₃ y₃),
      x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₂ ≠ x₃ ∧
      (2 : Nat) • (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) = 0 ∧
      (2 : Nat) • (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) = 0 ∧
      (2 : Nat) • (WeierstrassCurve.Affine.Point.some x₃ y₃ h₃) = 0 := by
  let P := W.twoTorsionPolynomial
  have ha : P.a ≠ 0 := by
    simp [P, WeierstrassCurve.twoTorsionPolynomial]
  have hsplit : (P.toPoly.map (algebraMap F (AlgebraicClosure F))).Splits :=
    IsAlgClosed.splits _
  obtain ⟨x₁, x₂, x₃, hroots⟩ :=
    (Cubic.splits_iff_roots_eq_three (P := P) (φ := algebraMap F (AlgebraicClosure F)) ha).mp hsplit
  have hdiscr : P.discr ≠ 0 := by
    change W.twoTorsionPolynomial.discr ≠ 0
    rw [WeierstrassCurve.twoTorsionPolynomial_discr]
    exact mul_ne_zero (by norm_num) (W.isUnit_Δ.ne_zero)
  have hne := (Cubic.discr_ne_zero_iff_roots_ne (P := P) (φ := algebraMap F (AlgebraicClosure F)) ha hroots).mp hdiscr
  have hmap_poly : (P.map (algebraMap F (AlgebraicClosure F))).toPoly ≠ 0 :=
    Cubic.ne_zero_of_a_ne_zero (by
      have h4 : (P.map (algebraMap F (AlgebraicClosure F))).a = 4 := by
        simp only [P, Cubic.map, WeierstrassCurve.twoTorsionPolynomial]
        exact map_ofNat (algebraMap F (AlgebraicClosure F)) 4
      rw [h4]; norm_num)
  have root_eval (x : AlgebraicClosure F) (hxmem : x ∈ (P.map (algebraMap F (AlgebraicClosure F))).roots) :
      (W.baseChange (AlgebraicClosure F)).twoTorsionPolynomial.toPoly.eval x = 0 := by
    have hx0 : (P.map (algebraMap F (AlgebraicClosure F))).a * x ^ 3 +
        (P.map (algebraMap F (AlgebraicClosure F))).b * x ^ 2 +
        (P.map (algebraMap F (AlgebraicClosure F))).c * x +
        (P.map (algebraMap F (AlgebraicClosure F))).d = 0 :=
      (Cubic.mem_roots_iff (P := P.map (algebraMap F (AlgebraicClosure F))) hmap_poly x).mp hxmem
    simpa [twoTorsionPolynomial_baseChange W (AlgebraicClosure F), Cubic.toPoly,
      Cubic.map, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X] using hx0
  have hx₁mem : x₁ ∈ (P.map (algebraMap F (AlgebraicClosure F))).roots := by rw [hroots]; simp
  have hx₂mem : x₂ ∈ (P.map (algebraMap F (AlgebraicClosure F))).roots := by rw [hroots]; simp
  have hx₃mem : x₃ ∈ (P.map (algebraMap F (AlgebraicClosure F))).roots := by rw [hroots]; simp
  obtain ⟨y₁, h₁, hp₁⟩ := twoTorsionPoint_of_root W (AlgebraicClosure F) x₁ (root_eval x₁ hx₁mem)
  obtain ⟨y₂, h₂, hp₂⟩ := twoTorsionPoint_of_root W (AlgebraicClosure F) x₂ (root_eval x₂ hx₂mem)
  obtain ⟨y₃, h₃, hp₃⟩ := twoTorsionPoint_of_root W (AlgebraicClosure F) x₃ (root_eval x₃ hx₃mem)
  exact ⟨x₁, x₂, x₃, y₁, y₂, y₃, h₁, h₂, h₃,
    hne.1, hne.2.1, hne.2.2, hp₁, hp₂, hp₃⟩

end S2223Probe
end
