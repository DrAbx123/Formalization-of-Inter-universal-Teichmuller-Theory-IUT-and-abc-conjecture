import LeanFormal.IUT.Foundations.AlgebraicGeometry.LogShellVolumeConsumer
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellIndexResidueFormula
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellSharpBounds

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.Foundations.LocalFields.LogShellVolumeP2Boundary

universe u

open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm MeasureTheory
open LeanFormal.IUT.Foundations.LocalFields.LogShellVolume

variable {K : Type u} [NormedField K] [CharZero K] [CompleteSpace K]
  [IsUltrametricDist K] [ProperSpace K] [NormedAlgebra ℚ_[2] K]

local instance twoPrimeFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem logShellScale_two : logShellScale 2 = 4 := by
  unfold logShellScale
  norm_num

theorem logShellScaleExponentFactor_two : logShellScaleExponentFactor (p := 2) = 2 := by
  unfold logShellScaleExponentFactor
  norm_num

theorem logShellScale_two_eq_prime_pow_factor :
    logShellScale 2 = 2 ^ logShellScaleExponentFactor (p := 2) :=
  logShellScale_eq_prime_pow_factor (p := 2)

theorem logShellResidueCard_two_pow :
    ∃ f : ℕ, 1 ≤ f ∧ logShellResidueCard (K := K) = 2 ^ f :=
  logShellResidueCard_eq_prime_pow (K := K) (p := 2)

theorem logShellResidueCard_two_even :
    Even (logShellResidueCard (K := K)) := by
  obtain ⟨f, hf, hq⟩ := logShellResidueCard_two_pow (K := K)
  rw [hq]
  exact even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega : f ≠ 0))

theorem logShellResiduePowerCardHypothesis_two_iff_index_eq_pow {a : ℕ} :
    LogShellResiduePowerCardHypothesis (K := K) (p := 2) a ↔
      logShellIntegerIndex (K := K) (p := 2) =
        logShellResidueCard (K := K) ^ a := by
  constructor
  · exact logShellIntegerIndex_eq_residueCard_pow_of_powerCardHypothesis
  · intro h
    unfold LogShellResiduePowerCardHypothesis
    rw [logShellCongruenceQuotient_card_eq_torsion_mul_logShellIntegerIndex, h,
      Nat.mul_comm]

theorem logShellResiduePowerCardHypothesis_two_zero_iff_index_eq_one :
    LogShellResiduePowerCardHypothesis (K := K) (p := 2) 0 ↔
      logShellIntegerIndex (K := K) (p := 2) = 1 := by
  rw [logShellResiduePowerCardHypothesis_two_iff_index_eq_pow, pow_zero]

theorem logShellResiduePowerCardHypothesis_two_exponent_unique {a b : ℕ}
    (ha : LogShellResiduePowerCardHypothesis (K := K) (p := 2) a)
    (hb : LogShellResiduePowerCardHypothesis (K := K) (p := 2) b) :
    a = b := by
  have hqa : logShellIntegerIndex (K := K) (p := 2) =
      logShellResidueCard (K := K) ^ a :=
    (logShellResiduePowerCardHypothesis_two_iff_index_eq_pow.mp ha)
  have hqb : logShellIntegerIndex (K := K) (p := 2) =
      logShellResidueCard (K := K) ^ b :=
    (logShellResiduePowerCardHypothesis_two_iff_index_eq_pow.mp hb)
  have hpow : logShellResidueCard (K := K) ^ a =
      logShellResidueCard (K := K) ^ b := hqa.symm.trans hqb
  exact Nat.pow_right_injective
    (Nat.succ_le_of_lt (one_lt_logShellResidueCard (K := K) (p := 2))) hpow

/-- At p = 2 the residue-power hypothesis is never satisfied by all exponents:
at most one exponent can work.  This is an exact boundary, not a q^a claim. -/
theorem not_all_logShellResiduePowerCardHypothesis_two :
    ¬ ∀ a : ℕ, LogShellResiduePowerCardHypothesis (K := K) (p := 2) a := by
  intro h
  have h01 : (0 : ℕ) = 1 :=
    logShellResiduePowerCardHypothesis_two_exponent_unique (h 0) (h 1)
  exact Nat.zero_ne_one h01

theorem logShellVolumeConsumer_two_index_exact :
    (logShellVolumeConsumer (K := K) (p := 2)).index =
      logShellIntegerIndex (K := K) (p := 2) :=
  rfl

theorem logShellVolumeConsumer_two_index_pos :
    0 < (logShellVolumeConsumer (K := K) (p := 2)).index :=
  (logShellVolumeConsumer (K := K) (p := 2)).index_pos

theorem logShellVolume_two_eq_index_mul_integers
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [Measure.IsAddHaarMeasure μ] :
    μ (integralLogShell (K := K) (p := 2) : Set K) =
      ((logShellVolumeConsumer (K := K) (p := 2)).index : ENNReal) *
        μ (Integers K : Set K) :=
  logShellVolume_eq_index_mul_integers (K := K) (p := 2) μ

theorem logShellVolumeDiscrepancy_two_eq_relativeHaarLog
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [Measure.IsAddHaarMeasure μ] :
    integralLogShellDiscrepancy (K := K) (p := 2) =
      Real.log (μ (integralLogShell (K := K) (p := 2) : Set K)).toReal -
        Real.log (μ (Integers K : Set K)).toReal :=
  logShellVolumeDiscrepancy_eq_relativeHaarLog (K := K) (p := 2) μ

theorem logShellVolume_two_exact_residue_power {a : ℕ}
    (h : LogShellResiduePowerCardHypothesis (K := K) (p := 2) a) :
    (logShellVolumeConsumer (K := K) (p := 2)).index =
      logShellResidueCard (K := K) ^ a :=
  logShellVolume_exact_residue_power (K := K) (p := 2) h

end LeanFormal.IUT.Foundations.LocalFields.LogShellVolumeP2Boundary
end