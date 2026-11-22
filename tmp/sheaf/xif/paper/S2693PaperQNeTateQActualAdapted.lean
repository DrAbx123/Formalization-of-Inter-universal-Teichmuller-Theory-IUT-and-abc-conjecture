import tmp.sheaf.xif.paper.S2690TateQExistsActual
import LeanFormal.IUT.Foundations.PAdicAnalytic.TateEstimatesGeneral
import LeanFormal.IUT.Foundations.PAdicAnalytic.TateJGeneralB

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.PAdicAnalytic
open LeanFormal.IUT.PAdicAnalytic.General
open LeanFormal.IUT.PAdicAnalytic.GeneralInverseJAssembly
open LeanFormal.IUT.XiFPaper.S2690TateQExistsActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S2693PaperQNeTateQActualAdapted

local instance fivePrimeFact2693 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

theorem S2693PaperQ_tateHK_eq :
    tateHK (K := ℚ_[5]) (5 : ℚ_[5]) =
      (5 : ℚ_[5]) + generalTateR (K := ℚ_[5]) (5 : ℚ_[5]) :=
  tateHK_eq_q_add_generalTateR S2690_hint S2690_h1728 (by
    rw [Padic.norm_p]
    norm_num)

theorem S2693PaperQ_remainder_bound :
    ‖generalTateR (K := ℚ_[5]) (5 : ℚ_[5])‖ ≤
      ((5 : ℝ)⁻¹) ^ 2 := by
  have hh : ∀ n : ℕ, ‖(HK (K := ℚ_[5])).coeff n‖ ≤ 1 :=
    HK_coeff_norm_le_one (K := ℚ_[5]) S2690_hint S2690_h1728
  have hR : generalTateR (K := ℚ_[5]) (5 : ℚ_[5]) =
      generalTateRemainder (fun n : ℕ => (HK (K := ℚ_[5])).coeff n)
        (5 : ℚ_[5]) := rfl
  rw [hR]
  exact generalTateRemainder_norm_le_c_sq
    (fun n : ℕ => (HK (K := ℚ_[5])).coeff n) hh
    (by norm_num : (0 : ℝ) ≤ (5 : ℝ)⁻¹)
    (by norm_num : (5 : ℝ)⁻¹ < 1)
    (by rw [Padic.norm_p])

theorem S2693PaperQ_tateHK_sub_bound :
    ‖tateHK (K := ℚ_[5]) (5 : ℚ_[5]) - (5 : ℚ_[5])‖ ≤
      ((5 : ℝ)⁻¹) ^ 2 := by
  rw [S2693PaperQ_tateHK_eq]
  have h : (5 : ℚ_[5]) + generalTateR (K := ℚ_[5]) (5 : ℚ_[5]) - 5 =
      generalTateR (K := ℚ_[5]) (5 : ℚ_[5]) := by ring
  rw [h]
  exact S2693PaperQ_remainder_bound

theorem S2693Norm10810 :
    ‖(-10805 : ℚ_[5]) - (5 : ℚ_[5])‖ = (5 : ℝ)⁻¹ := by
  have hnum : (-10805 : ℚ_[5]) - (5 : ℚ_[5]) = (-10810 : ℚ_[5]) := by norm_num
  rw [hnum]
  have h10810 : (-10810 : ℚ_[5]) = -((10810 : ℕ) : ℚ_[5]) := by norm_num
  rw [h10810, norm_neg]
  have h2162 : ‖(2162 : ℚ_[5])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]
    norm_num
  have h10810' : ((10810 : ℕ) : ℚ_[5]) =
      (5 : ℚ_[5]) * (2162 : ℚ_[5]) := by norm_num
  rw [h10810', norm_mul, Padic.norm_p, h2162, mul_one]

/-- The paper q = 5 cannot be the inverse-j Tate parameter: its tateHK value
is 5 plus a remainder of norm at most 1/25, hence cannot equal -10805. -/
theorem S2693PaperQ_tateHK_ne :
    tateHK (K := ℚ_[5]) (5 : ℚ_[5]) ≠ (-10805 : ℚ_[5]) := by
  intro h
  have hle := S2693PaperQ_tateHK_sub_bound
  rw [h, S2693Norm10810] at hle
  norm_num at hle

/-- Any q whose tateHK value is -10805 is not the paper q = 5. -/
theorem S2693PaperQ_ne_of_tateHK
    {q : ℚ_[5]} (hq : tateHK (K := ℚ_[5]) q = (-10805 : ℚ_[5])) :
    (5 : ℚ_[5]) ≠ q := by
  intro h
  exact S2693PaperQ_tateHK_ne (by rw [h, hq])

/-- The actual q_Tate constructed from the inverse-j theorem is not the paper
q = 5. -/
theorem S2693PaperQ_ne_TateQ :
    (5 : ℚ_[5]) ≠ Classical.choose S2690_TateQ_exists := by
  apply S2693PaperQ_ne_of_tateHK
  exact (Classical.choose_spec S2690_TateQ_exists).1

#print axioms S2693PaperQ_tateHK_ne
#print axioms S2693PaperQ_ne_TateQ

end LeanFormal.IUT.XiFPaper.S2693PaperQNeTateQActualAdapted
end
