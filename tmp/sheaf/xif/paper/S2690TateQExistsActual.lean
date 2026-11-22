import LeanFormal.IUT.Foundations.PAdicAnalytic.TateInverseJFinal
import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitCurvePadic

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.PAdicAnalytic
open LeanFormal.IUT.PAdicAnalytic.General
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S2690TateQExistsActual

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

theorem S2690_hint (n : ℕ) :
    ‖(n : ℚ_[5])‖ ≤ 1 :=
  IsUltrametricDist.norm_natCast_le_one ℚ_[5] n

theorem S2690_h1728 :
    ‖(1728 : ℚ_[5])‖ = 1 := by
  have h : ‖((1728 : ℕ) : ℚ_[5])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]
    norm_num
  simpa using h

theorem S2690_ht0 :
    (-10805 : ℚ_[5]) ≠ 0 := by
  norm_num

theorem S2690_ht1 :
    ‖(-10805 : ℚ_[5])‖ < 1 := by
  have h : ‖(10805 : ℚ_[5])‖ < 1 := by
    have h : ‖((10805 : ℕ) : ℚ_[5])‖ < 1 := by
      rw [Padic.norm_natCast_lt_one_iff]
      norm_num
    simpa using h
  simpa using h

theorem S2690_TateQ_exists :
    ∃ q : ℚ_[5],
      tateHK (K := ℚ_[5]) q = (-10805 : ℚ_[5]) ∧
      tateJK (K := ℚ_[5]) q = (-10805 : ℚ_[5])⁻¹ ∧
      ‖q‖ < 1 :=
  exists_tateHK_eq_and_tateJK_eq_inv
    (K := ℚ_[5]) S2690_hint S2690_h1728 S2690_ht0 S2690_ht1

#check S2690_TateQ_exists
#print axioms S2690_TateQ_exists

end LeanFormal.IUT.XiFPaper.S2690TateQExistsActual
end
