import LeanFormal.IUT.Foundations.AlgebraicGeometry.LogShellVolumeConsumer
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellIndexResidueFormula

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.Foundations.LocalFields.LogShellResiduePowerConsumer

universe u

open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.Foundations.LocalFields.LogShellVolume

variable {K : Type u} [NormedField K] [CharZero K] [CompleteSpace K]
  [IsUltrametricDist K] [ProperSpace K] {p : ℕ} [Fact p.Prime]
  [NormedAlgebra ℚ_[p] K]

/-- Exact hypothesis/index relation for downstream consumers. -/
theorem logShellResiduePowerCardHypothesis_iff_index_eq_pow {a : ℕ} :
    LogShellResiduePowerCardHypothesis (K := K) (p := p) a ↔
      logShellIntegerIndex (K := K) (p := p) =
        logShellResidueCard (K := K) ^ a := by
  constructor
  · exact logShellIntegerIndex_eq_residueCard_pow_of_powerCardHypothesis
  · intro h
    unfold LogShellResiduePowerCardHypothesis
    rw [logShellCongruenceQuotient_card_eq_torsion_mul_logShellIntegerIndex, h,
      Nat.mul_comm]

/-- The two actual conditional consumers of the residue-power hypothesis and the
exact hypothesis/index relation, packaged for downstream use. -/
structure LogShellResiduePowerConsumers where
  index : ℕ
  index_eq_logShellIntegerIndex : index = logShellIntegerIndex (K := K) (p := p)
  index_pos : 0 < index
  hypothesis_iff_index_eq_pow :
    ∀ {a : ℕ}, LogShellResiduePowerCardHypothesis (K := K) (p := p) a ↔
      index = logShellResidueCard (K := K) ^ a
  index_consumer :
    ∀ {a : ℕ}, LogShellResiduePowerCardHypothesis (K := K) (p := p) a →
      index = logShellResidueCard (K := K) ^ a
  volumeIndex_consumer :
    ∀ {a : ℕ}, LogShellResiduePowerCardHypothesis (K := K) (p := p) a →
      (logShellVolumeConsumer (K := K) (p := p)).index =
        logShellResidueCard (K := K) ^ a

noncomputable def logShellResiduePowerConsumers :
    LogShellResiduePowerConsumers (K := K) (p := p) where
  index := logShellIntegerIndex (K := K) (p := p)
  index_eq_logShellIntegerIndex := rfl
  index_pos := logShellIntegerIndex_pos (K := K) (p := p)
  hypothesis_iff_index_eq_pow := fun {a} =>
    logShellResiduePowerCardHypothesis_iff_index_eq_pow (K := K) (p := p)
  index_consumer := fun {a} h =>
    logShellIntegerIndex_eq_residueCard_pow_of_powerCardHypothesis (K := K) (p := p) h
  volumeIndex_consumer := fun {a} h =>
    logShellVolume_exact_residue_power (K := K) (p := p) h

theorem logShellResiduePowerConsumers_index_exact :
    (logShellResiduePowerConsumers (K := K) (p := p)).index =
      logShellIntegerIndex (K := K) (p := p) :=
  rfl

theorem logShellResiduePowerConsumers_index_pos :
    0 < (logShellResiduePowerConsumers (K := K) (p := p)).index :=
  (logShellResiduePowerConsumers (K := K) (p := p)).index_pos

theorem logShellResiduePowerConsumers_hypothesis_iff :
    ∀ {a : ℕ}, LogShellResiduePowerCardHypothesis (K := K) (p := p) a ↔
      (logShellResiduePowerConsumers (K := K) (p := p)).index =
        logShellResidueCard (K := K) ^ a :=
  (logShellResiduePowerConsumers (K := K) (p := p)).hypothesis_iff_index_eq_pow

theorem logShellResiduePowerConsumers_volume_consumer
    {a : ℕ} (h : LogShellResiduePowerCardHypothesis (K := K) (p := p) a) :
    (logShellVolumeConsumer (K := K) (p := p)).index =
      logShellResidueCard (K := K) ^ a :=
  (logShellResiduePowerConsumers (K := K) (p := p)).volumeIndex_consumer h

end LeanFormal.IUT.Foundations.LocalFields.LogShellResiduePowerConsumer
end