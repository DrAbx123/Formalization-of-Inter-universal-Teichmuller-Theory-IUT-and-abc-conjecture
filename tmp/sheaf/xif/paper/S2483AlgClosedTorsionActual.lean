import tmp.sheaf.xif.paper.S2376ThreeRootsActual
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.FieldTheory.IsAlgClosed.Basic

noncomputable section
set_option maxHeartbeats 4000000
open WeierstrassCurve Polynomial
namespace LeanFormal.IUT.XiFPaper.S2483AlgClosedTorsionActual

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

theorem S2483ThreeDistinctRoots (h2 : (2 : K) ≠ 0) :
    ∃ x y z : K, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      x ∈ W.twoTorsionPolynomial.roots ∧
      y ∈ W.twoTorsionPolynomial.roots ∧
      z ∈ W.twoTorsionPolynomial.roots := by
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have ha : W.twoTorsionPolynomial.a ≠ 0 := by
    simp [WeierstrassCurve.twoTorsionPolynomial, h4]
  have hP : W.twoTorsionPolynomial.toPoly.Splits := IsAlgClosed.splits _
  obtain ⟨x, y, z, hxyz⟩ := (Cubic.splits_iff_roots_eq_three (P := W.twoTorsionPolynomial) (φ := RingHom.id K) ha).mp (by simpa using hP)
  have hd : W.twoTorsionPolynomial.discr ≠ 0 := by
    apply WeierstrassCurve.twoTorsionPolynomial_discr_ne_zero
    · exact isUnit_iff_ne_zero.mpr h2
    · exact W.isUnit_Δ
  have hid : Cubic.map (RingHom.id K) W.twoTorsionPolynomial = W.twoTorsionPolynomial := by
    ext <;> simp [Cubic.map]
  rw [hid] at hxyz
  have hne := (Cubic.discr_ne_zero_iff_roots_ne (P := W.twoTorsionPolynomial) (φ := RingHom.id K) ha hxyz).mp hd
  refine ⟨x, y, z, hne.1, hne.2.1, hne.2.2, ?_, ?_, ?_⟩
  · rw [hxyz]; simp
  · rw [hxyz]; simp
  · rw [hxyz]; simp

#print axioms S2483ThreeDistinctRoots

end LeanFormal.IUT.XiFPaper.S2483AlgClosedTorsionActual
end