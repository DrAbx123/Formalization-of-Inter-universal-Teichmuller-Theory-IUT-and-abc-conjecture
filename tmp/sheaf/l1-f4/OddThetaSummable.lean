import LeanFormal.IUT.Foundations.Theta.OddTheta
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1200000

noncomputable section

namespace LeanFormal.IUT.Foundations.Theta

open Filter

universe u

variable {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]

/-- The exponent of the negative-index odd theta term is the usual quadratic
exponent. -/
theorem oddThetaExponent_neg_nat (n : ℕ) :
    oddThetaExponent (-(n : ℤ) - 1) = n * (n + 1) / 2 := by
  apply Nat.cast_injective (R := ℤ)
  rw [oddThetaExponent_coe]
  push_cast
  ring

/-- Norm of the negative half of the odd theta series. -/
theorem norm_oddThetaTerm_neg_nat (q U : L) (hU : U ≠ 0) (n : ℕ) :
    ‖oddThetaTerm q U (-(n : ℤ) - 1)‖ =
      ‖U‖⁻¹ * (‖q‖ ^ (n * (n + 1) / 2) * ((‖U‖ ^ 2)⁻¹) ^ n) := by
  rw [norm_oddThetaTerm, oddThetaExponent_neg_nat]
  have hU0 : ‖U‖ ≠ 0 := norm_ne_zero_iff.mpr hU
  have hpow : (2 * (-(n : ℤ) - 1) + 1) = -(2 * (n : ℤ) + 1) := by ring
  rw [hpow, zpow_neg]
  have hnat : ((2 * n + 1 : ℕ) : ℤ) = 2 * (n : ℤ) + 1 := by push_cast; ring
  rw [← hnat, zpow_natCast]
  have hfactor : ‖U‖ ^ (2 * n + 1) = ‖U‖ * (‖U‖ ^ 2) ^ n := by
    rw [pow_succ, show 2 * n = n * 2 by ring, pow_mul]
    ring
  rw [hfactor, mul_inv, ← inv_pow]
  ring

/-- The negative half of the odd theta series is summable. -/
theorem summable_oddThetaTerm_neg_nat (q U : L) (hU : U ≠ 0) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => oddThetaTerm q U (-(n : ℤ) - 1)) := by
  have hUpos : 0 < ‖U‖ := norm_pos_iff.mpr hU
  have hb : 0 < (‖U‖ ^ 2)⁻¹ := inv_pos.mpr (pow_pos hUpos 2)
  have hdec := tendsto_quadraticExponential_mul_geometric
    (a := ‖q‖) (b := (‖U‖ ^ 2)⁻¹) (norm_nonneg q) hq hb
  have hdec' : Tendsto
      (fun n : ℕ => ‖U‖⁻¹ * (‖q‖ ^ (n * (n + 1) / 2) * ((‖U‖ ^ 2)⁻¹) ^ n))
      atTop (nhds 0) := by
    simpa using hdec.const_mul ‖U‖⁻¹
  have hnorm : (fun n : ℕ => ‖oddThetaTerm q U (-(n : ℤ) - 1)‖) =
      fun n : ℕ => ‖U‖⁻¹ * (‖q‖ ^ (n * (n + 1) / 2) * ((‖U‖ ^ 2)⁻¹) ^ n) := by
    funext n
    rw [norm_oddThetaTerm_neg_nat q U hU n]
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop]
  exact (tendsto_zero_iff_norm_tendsto_zero).mpr (by
    rw [hnorm]
    exact hdec')

end LeanFormal.IUT.Foundations.Theta