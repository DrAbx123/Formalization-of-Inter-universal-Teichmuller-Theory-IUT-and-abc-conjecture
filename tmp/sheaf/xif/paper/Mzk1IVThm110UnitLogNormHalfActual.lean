import tmp.sheaf.xif.paper.Mzk1P2Log1pHalfActual
import tmp.sheaf.xif.paper.Mzk1IVThm110UnitLogNormBoundActual
import tmp.sheaf.xif.paper.Mzk1IVThm110CardExponentActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithm
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110UnitLogNormHalfActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110UnitLogNormBoundActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110CardExponentActual
variable {K : Type*} [NormedField K] [IsUltrametricDist K]
variable [NormedAlgebra ℚ_[2] K] [CharZero K] [CompleteSpace K]
variable [NormOneClass K] [ProperSpace K]
/-- Generic p=2 unitLog norm bound from an explicit principal-unit radius bound. -/
theorem unitLog_norm_le_one_of_principal_bound_half
    (hbound : ∀ x : (Integers K)ˣ, x ∈ principalUnits (K := K) →
      ‖(((x.val : Integers K) : K) - 1)‖ ≤ 1 / 2)
    (hcop : Nat.Coprime 2 (integralUnitExponent (K := K)))
    (u : (Integers K)ˣ) : ‖unitLog (K := K) u‖ ≤ 1 := by
  rw [unitLog_eq_withExponent (K := K) (p := 2) u
    (Nat.pos_iff_ne_zero.mp (integralUnitExponent_pos (K := K)))
    (pow_integralUnitExponent_mem (K := K) u)]
  unfold unitLogWithExponent
  rw [norm_div, norm_integralUnitExponent_eq_one (K := K) 2 hcop, div_one]
  exact (norm_log1p_le_half (K := K)
    (hbound _ (pow_integralUnitExponent_mem (K := K) u))).trans (by norm_num)
#check unitLog_norm_le_one_of_principal_bound_half
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110UnitLogNormHalfActual
end