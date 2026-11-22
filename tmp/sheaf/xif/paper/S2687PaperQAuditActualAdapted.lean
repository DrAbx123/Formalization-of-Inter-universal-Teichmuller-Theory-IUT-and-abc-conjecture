import LeanFormal.IUT.Foundations.PAdicAnalytic.TateDeltaIntegral
import LeanFormal.IUT.Foundations.PAdicAnalytic.TateEstimatesGeneral

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.PAdicAnalytic
open LeanFormal.IUT.PAdicAnalytic.General
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2687PaperQAuditActualAdapted

local instance s2687FivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

theorem S2687_padic_natCast_le_one (n : Nat) :
    ‖(n : ℚ_[5])‖ ≤ 1 := by
  by_cases h : (5 : Nat) ∣ n
  · exact le_of_lt ((Padic.norm_natCast_lt_one_iff (p := 5)).mpr h)
  · have hcop : Nat.Coprime n 5 := Nat.Coprime.symm
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr h)
    rw [(Padic.norm_natCast_eq_one_iff (p := 5)).mpr hcop.symm]

theorem S2687_padic_five_norm : ‖(5 : ℚ_[5])‖ = ((5 : Real)⁻¹) := by
  simpa using (Padic.norm_p (p := 5))

theorem S2687_tateJK_five_ne_concrete_j :
    tateJK (K := ℚ_[5]) 5 ≠ (-10805 : ℚ_[5])⁻¹ := by
  intro hJ
  have hint : ∀ n : Nat, ‖(n : ℚ_[5])‖ ≤ 1 := S2687_padic_natCast_le_one
  have hq5 : ‖(5 : ℚ_[5])‖ < 1 := by
    rw [S2687_padic_five_norm]
    norm_num
  have hHK : tateHK (K := ℚ_[5]) 5 = 5 + generalTateR (K := ℚ_[5]) 5 :=
    tateHK_eq_q_add_generalTateR_no1728 (K := ℚ_[5]) hint hq5
  have hRbound : ‖generalTateR (K := ℚ_[5]) 5‖ ≤ ‖(5 : ℚ_[5])‖ ^ 2 :=
    generalTateRemainder_norm_le (K := ℚ_[5])
      (h := fun n => (HK (K := ℚ_[5])).coeff n) (HK_coeff_norm_le_one_no1728 hint) 5
      (le_of_eq (S2687_padic_five_norm).symm) hq5
  have hRle : ‖generalTateR (K := ℚ_[5]) 5‖ ≤ ((5 : Real)⁻¹) ^ 2 := by
    simpa [S2687_padic_five_norm] using hRbound
  have hHKne : tateHK (K := ℚ_[5]) 5 ≠ 0 := by
    intro hzero
    have hfive : (5 : ℚ_[5]) = -generalTateR (K := ℚ_[5]) 5 := by
      rw [hHK] at hzero
      exact eq_neg_of_add_eq_zero_left hzero
    have hnorm : ‖(5 : ℚ_[5])‖ ≤ ((5 : Real)⁻¹) ^ 2 := by
      rw [hfive, norm_neg]
      exact hRle
    rw [S2687_padic_five_norm] at hnorm
    norm_num at hnorm
  have hc4 : (TateCurve.weierstrassCurve (K := ℚ_[5]) 5).c₄ ≠ 0 := by
    intro hc
    apply hHKne
    simp [tateHK, hc]
  have hDelta : (TateCurve.weierstrassCurve (K := ℚ_[5]) 5).Δ ≠ 0 := by
    intro hD
    apply hHKne
    simp [tateHK, hD]
  have hmul := tateHK_mul_tateJK (K := ℚ_[5]) 5 hc4 hDelta
  rw [hJ] at hmul
  have hHKval : tateHK (K := ℚ_[5]) 5 = -10805 := by
    have hneg : tateHK (K := ℚ_[5]) 5 * ((-10805 : ℚ_[5])⁻¹) = 1 := hmul
    have h10805 : ((-10805 : ℚ_[5])) ≠ 0 := by norm_num
    field_simp [h10805] at hneg
    exact neg_eq_iff_eq_neg.mp hneg
  have hr : generalTateR (K := ℚ_[5]) 5 = -10810 := by
    have hsub := congrArg (fun x => x - 5) hHKval
    rw [hHK] at hsub
    ring_nf at hsub
    exact hsub
  have hrnorm : ‖(10810 : ℚ_[5])‖ ≤ ((5 : Real)⁻¹) ^ 2 := by
    have h := hRle
    rw [hr, norm_neg] at h
    simpa using h
  have hintnorm : ‖((10810 : ℤ) : ℤ_[5])‖ ≤ ((5 : Real) ^ (-2 : ℤ)) := by
    rw [PadicInt.norm_intCast_eq_padic_norm]
    norm_num
    simpa [show ((5 : Real) ^ 2)⁻¹ = (25 : Real)⁻¹ by norm_num] using hrnorm
  have hdvd : ((5 ^ 2 : ℤ) ∣ (10810 : ℤ)) :=
    (PadicInt.norm_int_le_pow_iff_dvd (p := 5) (k := 10810) (n := 2)).mp hintnorm
  norm_num at hdvd

#check S2687_tateJK_five_ne_concrete_j
#print axioms S2687_tateJK_five_ne_concrete_j
end LeanFormal.IUT.XiFPaper.S2687PaperQAuditActualAdapted
end
