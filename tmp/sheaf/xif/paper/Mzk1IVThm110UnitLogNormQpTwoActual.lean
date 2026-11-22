import tmp.sheaf.xif.paper.Mzk1P2Log1pHalfActual
import tmp.sheaf.xif.paper.Mzk1IVThm110UnitLogNormBoundActual
import tmp.sheaf.xif.paper.Mzk1IVThm110CardExponentActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithm
import Mathlib.NumberTheory.Padics.PadicNumbers
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110UnitLogNormQpTwoActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110UnitLogNormBoundActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110CardExponentActual
/-- Q2 principal units are within 1/2 of 1. -/
theorem principalUnit_norm_sub_one_le_half_Q2
    (x : (Integers ℚ_[2])ˣ) (hx : x ∈ principalUnits (K := ℚ_[2])) :
    ‖(((x.val : Integers ℚ_[2]) : ℚ_[2]) - 1)‖ ≤ 1 / 2 := by
  have hlt : ‖(((x.val : Integers ℚ_[2]) : ℚ_[2]) - 1)‖ < 1 :=
    (mem_principalUnits_iff (K := ℚ_[2]) x).mp hx
  have h := (Padic.norm_lt_pow_iff_norm_le_pow_sub_one (p := 2)
    (((x.val : Integers ℚ_[2]) : ℚ_[2]) - 1) 0).mp (by simpa using hlt)
  simpa using h
/-- unitLog norm bound over Q2 with odd exponent. -/
theorem unitLog_norm_le_one_Q2
    (hcop : Nat.Coprime 2 (integralUnitExponent (K := ℚ_[2])))
    (u : (Integers ℚ_[2])ˣ) :
    ‖unitLog (K := ℚ_[2]) u‖ ≤ 1 := by
  rw [unitLog_eq_withExponent (K := ℚ_[2]) (p := 2) u
    (Nat.pos_iff_ne_zero.mp (integralUnitExponent_pos (K := ℚ_[2])))
    (pow_integralUnitExponent_mem (K := ℚ_[2]) u)]
  unfold unitLogWithExponent
  rw [norm_div, norm_integralUnitExponent_eq_one (K := ℚ_[2]) 2 hcop, div_one]
  have hlt : ‖(((u ^ integralUnitExponent (K := ℚ_[2])).val :
      Integers ℚ_[2]) : ℚ_[2]) - 1‖ < 1 :=
    (mem_principalUnits_iff (K := ℚ_[2]) _).mp
      (pow_integralUnitExponent_mem (K := ℚ_[2]) u)
  have hle : ‖(((u ^ integralUnitExponent (K := ℚ_[2])).val :
      Integers ℚ_[2]) : ℚ_[2]) - 1‖ ≤ 1 / 2 := by
    have h := (Padic.norm_lt_pow_iff_norm_le_pow_sub_one (p := 2)
      ((((u ^ integralUnitExponent (K := ℚ_[2])).val :
        Integers ℚ_[2]) : ℚ_[2]) - 1) 0).mp (by simpa using hlt)
    simpa using h
  exact (norm_log1p_le_half (K := ℚ_[2]) hle).trans (by norm_num)
#check principalUnit_norm_sub_one_le_half_Q2
#check unitLog_norm_le_one_Q2
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110UnitLogNormQpTwoActual
end