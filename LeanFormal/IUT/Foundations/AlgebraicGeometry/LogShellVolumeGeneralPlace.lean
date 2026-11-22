import LeanFormal.IUT.Foundations.AlgebraicGeometry.LogShellVolumeConsumer
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellIndexResidueFormula
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.Foundations.LocalFields.LogShellVolumeGeneralPlace

universe u

open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm MeasureTheory
open LeanFormal.IUT.Foundations.LocalFields.LogShellVolume
open LeanFormal.IUT.NumberFieldFinitePlace

variable {F : Type u} [Field F] [NumberField F] {p : ℕ} [Fact p.Prime]

/-- The actual normalized completion at a finite place over the fixed prime. -/
abbrev GeneralPlaceField (place : FinitePlaceAtPrime F p) : Type u :=
  CommonPrimeCompletion place

/-- The actual log-shell volume consumer at an arbitrary finite place over `p`. -/
noncomputable def generalPlaceVolumeConsumer (place : FinitePlaceAtPrime F p) :
    LogShellVolumeConsumer (K := GeneralPlaceField (F := F) place) (p := p) :=
  logShellVolumeConsumer (K := GeneralPlaceField (F := F) place) (p := p)

theorem generalPlaceVolumeConsumer_index_exact
    (place : FinitePlaceAtPrime F p) :
    (generalPlaceVolumeConsumer place).index =
      logShellIntegerIndex (K := GeneralPlaceField (F := F) place) (p := p) :=
  (generalPlaceVolumeConsumer place).index_eq_logShellIntegerIndex

theorem generalPlaceVolumeConsumer_index_pos
    (place : FinitePlaceAtPrime F p) :
    0 < (generalPlaceVolumeConsumer place).index :=
  (generalPlaceVolumeConsumer place).index_pos

/-- Exact log-shell scale at the arbitrary finite place. -/
noncomputable def generalPlaceLogShellScale (place : FinitePlaceAtPrime F p) : ℕ :=
  logShellScale p

theorem generalPlaceLogShellScale_eq (place : FinitePlaceAtPrime F p) :
    generalPlaceLogShellScale place =
      logShellScale (completionRationalPrime place.val).val :=
  congrArg logShellScale place.2.symm

theorem generalPlaceVolume_eq_index_mul_integers
    (place : FinitePlaceAtPrime F p)
    [MeasurableSpace (GeneralPlaceField (F := F) place)]
    [BorelSpace (GeneralPlaceField (F := F) place)]
    (μ : Measure (GeneralPlaceField (F := F) place)) [Measure.IsAddHaarMeasure μ] :
    μ (integralLogShell (K := GeneralPlaceField (F := F) place) (p := p) : Set _) =
      ((generalPlaceVolumeConsumer place).index : ENNReal) *
        μ (Integers (GeneralPlaceField (F := F) place) : Set _) :=
  logShellVolume_eq_index_mul_integers
    (K := GeneralPlaceField (F := F) place) (p := p) μ

theorem generalPlaceVolumeDiscrepancy_eq_relativeHaarLog
    (place : FinitePlaceAtPrime F p)
    [MeasurableSpace (GeneralPlaceField (F := F) place)]
    [BorelSpace (GeneralPlaceField (F := F) place)]
    (μ : Measure (GeneralPlaceField (F := F) place)) [Measure.IsAddHaarMeasure μ] :
    integralLogShellDiscrepancy (K := GeneralPlaceField (F := F) place) (p := p) =
      Real.log (μ (integralLogShell (K := GeneralPlaceField (F := F) place) (p := p) : Set _)).toReal -
        Real.log (μ (Integers (GeneralPlaceField (F := F) place) : Set _)).toReal :=
  logShellVolumeDiscrepancy_eq_relativeHaarLog
    (K := GeneralPlaceField (F := F) place) (p := p) μ

/-- Exact conditional residue-power boundary at the arbitrary finite place. -/
theorem generalPlaceVolume_hypothesis_iff_index_eq_pow
    (place : FinitePlaceAtPrime F p) {a : ℕ} :
    LogShellResiduePowerCardHypothesis (K := GeneralPlaceField (F := F) place) (p := p) a ↔
      (generalPlaceVolumeConsumer place).index =
        logShellResidueCard (K := GeneralPlaceField (F := F) place) ^ a := by
  constructor
  · intro h
    exact logShellVolume_exact_residue_power (K := GeneralPlaceField (F := F) place) (p := p) h
  · intro h
    have hi : logShellIntegerIndex (K := GeneralPlaceField (F := F) place) (p := p) =
        logShellResidueCard (K := GeneralPlaceField (F := F) place) ^ a := by
      rw [← (generalPlaceVolumeConsumer place).index_eq_logShellIntegerIndex]
      exact h
    rw [show LogShellResiduePowerCardHypothesis (K := GeneralPlaceField (F := F) place) (p := p) a ↔
        logShellIntegerIndex (K := GeneralPlaceField (F := F) place) (p := p) =
          logShellResidueCard (K := GeneralPlaceField (F := F) place) ^ a from ?_]
    · exact hi
    · constructor
      · exact logShellIntegerIndex_eq_residueCard_pow_of_powerCardHypothesis
      · intro hcard
        unfold LogShellResiduePowerCardHypothesis
        rw [logShellCongruenceQuotient_card_eq_torsion_mul_logShellIntegerIndex, hcard,
          Nat.mul_comm]

theorem generalPlaceVolume_exact_residue_power
    (place : FinitePlaceAtPrime F p) {a : ℕ}
    (h : LogShellResiduePowerCardHypothesis (K := GeneralPlaceField (F := F) place) (p := p) a) :
    (generalPlaceVolumeConsumer place).index =
      logShellResidueCard (K := GeneralPlaceField (F := F) place) ^ a :=
  logShellVolume_exact_residue_power (K := GeneralPlaceField (F := F) place) (p := p) h

end LeanFormal.IUT.Foundations.LocalFields.LogShellVolumeGeneralPlace
end