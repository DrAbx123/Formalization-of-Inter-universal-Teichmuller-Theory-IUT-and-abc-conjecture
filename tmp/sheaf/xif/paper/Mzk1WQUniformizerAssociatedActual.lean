import PadicField.PowIndexPadic
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1WQUniformizerAssociatedActual
open LeanFormal.IUT
open scoped Valued

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

noncomputable def unitOfNrmOne {u : ℚ_[5]}
    (h : PadicField.nrm 5 ℚ_[5] u = 1) :
    (PadicField.Integers 5 ℚ_[5])ˣ where
  val := PadicField.Integers.mk u (le_of_eq h)
  inv := PadicField.Integers.mk u⁻¹ (by
    rw [PadicField.nrm_inv, h]
    simp)
  val_inv := Subtype.ext (by
    change u * u⁻¹ = 1
    exact mul_inv_cancel₀ (by
      intro hu
      have h0 : PadicField.nrm 5 ℚ_[5] u = 0 :=
        PadicField.nrm_eq_zero_iff.mpr hu
      rw [h0] at h
      exact zero_ne_one h))
  inv_val := Subtype.ext (by
    change u⁻¹ * u = 1
    exact inv_mul_cancel₀ (by
      intro hu
      have h0 : PadicField.nrm 5 ℚ_[5] u = 0 :=
        PadicField.nrm_eq_zero_iff.mpr hu
      rw [h0] at h
      exact zero_ne_one h))

theorem associated_uniformizer_five :
    Associated (PadicField.Integers.ϖ 5 ℚ_[5])
      (5 : PadicField.Integers 5 ℚ_[5]) := by
  have hπ := PadicField.uniformizer_spec (p := 5) (K := ℚ_[5])
  have h5 : (5 : ℚ_[5]) ≠ 0 := by norm_num
  obtain ⟨u, hu_nrm, hu_eq⟩ := PadicField.eq_zpow_mul_unit (p := 5) (K := ℚ_[5]) hπ h5
  have hv : PadicField.v 5 (5 : ℚ_[5]) = 1 := PadicField.v_p_Qp
  rw [hv, zpow_one] at hu_eq
  let uu : (PadicField.Integers 5 ℚ_[5])ˣ := unitOfNrmOne hu_nrm
  have hmain : (5 : PadicField.Integers 5 ℚ_[5]) =
      PadicField.Integers.ϖ 5 ℚ_[5] * uu := by
    apply Subtype.ext
    change (5 : ℚ_[5]) = (PadicField.uniformizer 5 ℚ_[5]) * u
    simpa using hu_eq
  apply associated_of_dvd_dvd
  · exact ⟨uu, hmain⟩
  · refine ⟨(↑uu⁻¹ : PadicField.Integers 5 ℚ_[5]), ?_⟩
    rw [hmain]
    simp [mul_assoc]

#print axioms unitOfNrmOne
#print axioms associated_uniformizer_five
end LeanFormal.IUT.XiFPaper.Mzk1WQUniformizerAssociatedActual