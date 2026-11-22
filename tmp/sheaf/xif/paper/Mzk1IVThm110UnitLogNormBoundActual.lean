import tmp.sheaf.xif.paper.Mzk1IVThm110UnitLogNormActual
import tmp.sheaf.xif.paper.Mzk1IVThm110CardExponentActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithm
import LeanFormal.IUT.Foundations.LocalFields.PadicExpLog
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110UnitLogNormBoundActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110UnitLogNormBoundActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110UnitLogNormActual
variable {K : Type*} [NormedField K] [IsUltrametricDist K]
variable [NormOneClass K]
variable [ProperSpace K]
/-- Conditional norm bound for unitLog, assuming the exponential bound and
unit norm of the exponent. -/
theorem unitLog_norm_le_one_of_exp_bound
    (p : Nat) [Fact p.Prime] [NormedAlgebra ℚ_[p] K]
    [CharZero K] [CompleteSpace K]
    (u : (Integers K)ˣ) (n : Nat) (hnpos : n ≠ 0)
    (hu : u ^ n ∈ principalUnits (K := K))
    (r : ℝ) (hr : r < 1 / 2)
    (hx : ‖(((u ^ n).val : Integers K) : K) - 1‖ ≤ r)
    (hnorm : ‖(n : K)‖ = 1) :
    ‖unitLog (K := K) u‖ ≤ 1 := by
  rw [unitLog_eq_withExponent (K := K) (p := p) u hnpos hu]
  unfold unitLogWithExponent
  rw [norm_div, hnorm, div_one]
  exact (norm_log1p_le (p := p) r (le_trans (norm_nonneg _) hx) hr hx).trans (by linarith)
/-- Exact missing source for the power/log1p estimate. -/
def missingPowerLogEstimate : List String :=
  [ "norm of (u ^ n - 1) ≤ r < 1/2 for n = integralUnitExponent",
    "p = 2 separate log1p radius (principal units have norm ≤ 1/2, not < 1/2)",
    "transport ‖(n:K)‖ = 1 from coprime via norm_natCast_eq_one_of_coprime" ]
theorem missingPowerLogEstimate_length : missingPowerLogEstimate.length = 3 := rfl
/-- Norm of the redefined exponent is one once it is coprime to p. -/
theorem norm_integralUnitExponent_eq_one
    (p : Nat) [Fact p.Prime] [NormedAlgebra ℚ_[p] K]
    (hcop : Nat.Coprime p (integralUnitExponent (K := K))) :
    ‖(integralUnitExponent (K := K) : K)‖ = 1 :=
  norm_natCast_eq_one_of_coprime (p := p) hcop

/-- Generic unitLog norm bound from an explicit principal-unit radius bound. -/
theorem unitLog_norm_le_one_of_principal_bound
    (p : Nat) [Fact p.Prime] [NormedAlgebra ℚ_[p] K]
    [CharZero K] [CompleteSpace K] [NormOneClass K] [ProperSpace K]
    (hbound : ∀ x : (Integers K)ˣ, x ∈ principalUnits (K := K) →
      ‖(((x.val : Integers K) : K) - 1)‖ ≤ 1 / 3)
    (hcop : Nat.Coprime p (integralUnitExponent (K := K)))
    (u : (Integers K)ˣ) : ‖unitLog (K := K) u‖ ≤ 1 := by
  exact unitLog_norm_le_one_of_exp_bound (K := K) p u
    (integralUnitExponent (K := K))
    (Nat.pos_iff_ne_zero.mp (integralUnitExponent_pos (K := K)))
    (pow_integralUnitExponent_mem (K := K) u)
    (1 / 3) (by norm_num)
    (hbound _ (pow_integralUnitExponent_mem (K := K) u))
    (norm_integralUnitExponent_eq_one p hcop)

#check unitLog_norm_le_one_of_principal_bound
#check unitLog_norm_le_one_of_exp_bound
#check norm_integralUnitExponent_eq_one
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110UnitLogNormBoundActual
end