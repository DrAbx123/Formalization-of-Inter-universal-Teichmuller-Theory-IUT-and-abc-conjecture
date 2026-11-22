import tmp.sheaf.xif.paper.S2369ThreeTwoTorsionActual
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.FieldTheory.IsAlgClosed.Basic

-- S2376: three distinct roots of the 2-division cubic over the algebraic closure.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2376ThreeRootsActual

open WeierstrassCurve

universe u

variable {R : Type u} [Field R] [Nontrivial R]
variable (W : WeierstrassCurve R) [W.IsElliptic]

theorem S2376ThreeDistinctRoots (h2 : (2 : R) ≠ 0) :
    ∃ x y z : AlgebraicClosure R,
      x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      x ∈ (Cubic.map (algebraMap R (AlgebraicClosure R)) W.twoTorsionPolynomial).roots ∧
      y ∈ (Cubic.map (algebraMap R (AlgebraicClosure R)) W.twoTorsionPolynomial).roots ∧
      z ∈ (Cubic.map (algebraMap R (AlgebraicClosure R)) W.twoTorsionPolynomial).roots := by
  let K := AlgebraicClosure R
  let φ : R →+* K := algebraMap R K
  have h4 : (4 : R) ≠ 0 := by
    rw [show (4 : R) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have ha : W.twoTorsionPolynomial.a ≠ 0 := by
    simp [WeierstrassCurve.twoTorsionPolynomial, h4]
  have hP : (W.twoTorsionPolynomial.toPoly.map φ).Splits := IsAlgClosed.splits _
  obtain ⟨x, y, z, hxyz⟩ := (Cubic.splits_iff_roots_eq_three (P := W.twoTorsionPolynomial) (φ := φ) ha).mp hP
  have hd : W.twoTorsionPolynomial.discr ≠ 0 := by
    apply WeierstrassCurve.twoTorsionPolynomial_discr_ne_zero
    · exact isUnit_iff_ne_zero.mpr h2
    · exact W.isUnit_Δ
  have hne := (Cubic.discr_ne_zero_iff_roots_ne (P := W.twoTorsionPolynomial) (φ := φ) ha hxyz).mp hd
  refine ⟨x, y, z, hne.1, hne.2.1, hne.2.2, ?_, ?_, ?_⟩
  · rw [hxyz]; simp
  · rw [hxyz]; simp
  · rw [hxyz]; simp

#print axioms S2376ThreeDistinctRoots

end LeanFormal.IUT.XiFPaper.S2376ThreeRootsActual

end
