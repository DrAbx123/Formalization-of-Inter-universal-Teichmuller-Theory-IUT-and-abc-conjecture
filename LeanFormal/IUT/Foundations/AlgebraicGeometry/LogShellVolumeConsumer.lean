import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellIndexArithmetic
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellHaarIndex
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellIndexResidueFormula

open scoped NNReal

set_option linter.unusedSectionVars false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.Foundations.LocalFields.LogShellVolume

universe u

open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm MeasureTheory

variable {K : Type u} [NormedField K] [CharZero K] [CompleteSpace K]
  [IsUltrametricDist K] [ProperSpace K] {p : ℕ} [Fact p.Prime]
  [NormedAlgebra ℚ_[p] K]

/-- Actual log-shell index/volume consumer data over a local base: the exact
integer quotient index, its positivity, the cardinal decomposition by the
congruence quotient and torsion-unit group, and the Haar-volume identity. -/
structure LogShellVolumeConsumer where
  index : ℕ
  index_eq_logShellIntegerIndex : index = logShellIntegerIndex (K := K) (p := p)
  index_pos : 0 < index
  congruenceCard_eq_torsion_mul_index :
    Nat.card ((Integers K)ˣ ⧸ logShellCongruenceUnits (K := K) (p := p)) =
      Nat.card (CommGroup.torsion (Integers K)ˣ) * index

/-- The actual consumer, built from the production index/cardinal arithmetic. -/
noncomputable def logShellVolumeConsumer : LogShellVolumeConsumer (K := K) (p := p) where
  index := logShellIntegerIndex (K := K) (p := p)
  index_eq_logShellIntegerIndex := rfl
  index_pos := logShellIntegerIndex_pos (K := K) (p := p)
  congruenceCard_eq_torsion_mul_index :=
    logShellCongruenceQuotient_card_eq_torsion_mul_logShellIntegerIndex (K := K) (p := p)

theorem logShellVolumeConsumer_index_pos :
    0 < (logShellVolumeConsumer (K := K) (p := p)).index :=
  (logShellVolumeConsumer (K := K) (p := p)).index_pos

theorem logShellVolumeConsumer_index_exact :
    (logShellVolumeConsumer (K := K) (p := p)).index =
      logShellIntegerIndex (K := K) (p := p) :=
  rfl

/-- Exact Haar-volume identity: the integral log-shell mass is the integer index
times the mass of the valuation integers.  This is the concrete volume relation
available in production. -/
theorem logShellVolume_eq_index_mul_integers
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [Measure.IsAddHaarMeasure μ] :
    μ (integralLogShell (K := K) (p := p) : Set K) =
      ((logShellVolumeConsumer (K := K) (p := p)).index : ENNReal) *
        μ (Integers K : Set K) :=
  measure_integralLogShell_eq_index_mul (K := K) (p := p) μ

/-- Log-volume discrepancy consumer: the logarithm of the integer quotient index
is the difference of the logarithms of the shell and integer Haar masses. -/
theorem logShellVolumeDiscrepancy_eq_relativeHaarLog
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [Measure.IsAddHaarMeasure μ] :
    integralLogShellDiscrepancy (K := K) (p := p) =
      Real.log (μ (integralLogShell (K := K) (p := p) : Set K)).toReal -
        Real.log (μ (Integers K : Set K)).toReal :=
  integralLogShellDiscrepancy_eq_relativeHaarLog (K := K) (p := p) μ

/-- Conditional residue-power consumer: under the named residue-power cardinal
hypothesis, the index is exactly the `a`-th power of the actual residue cardinal. -/
theorem logShellVolume_exact_residue_power {a : ℕ}
    (h : LogShellResiduePowerCardHypothesis (K := K) (p := p) a) :
    (logShellVolumeConsumer (K := K) (p := p)).index =
      logShellResidueCard (K := K) ^ a :=
  logShellIntegerIndex_eq_residueCard_pow_of_powerCardHypothesis (K := K) (p := p) h

end LeanFormal.IUT.Foundations.LocalFields.LogShellVolume
end