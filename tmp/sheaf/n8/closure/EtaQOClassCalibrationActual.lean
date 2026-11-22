import tmp.sheaf.n8.closure.EtaGlobalRegionAtFActual
import tmp.sheaf.n8.closure.EtaQHaarScalingCalibration

/-!
# Eta qO class calibration actual

Actual qOClassReadout is Real.log (mu(qORegion)).  Actual qORegionLogVolume is
Real.log ||q|| = qPilotSignedLog.  Therefore the class readout equals the native
q-pilot log exactly when the qO Haar mass is the actual norm,

  (mu (qORegion)).toReal = ||q||.

This is the exact Haar-normalization/scaling condition.  It is not assumed; the
unconditional equality remains the named gap.  No arbitrary normalization is
introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaQOClassCalibrationActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaRssNontrivialActual
open LeanFormal.IUT.N8Closure.EtaGlobalRegionAtFActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [MeasurableSpace (QCompletion X)]
variable [BorelSpace (QCompletion X)]
variable [ProperSpace (QCompletion X)]
variable [IsUltrametricDist (QCompletion X)]

/-- Exact mass-normalization condition for the qO region. -/
def QORegionMassEqNorm
    (μ : Measure (QCompletion X)) [Measure.IsAddHaarMeasure μ] : Prop :=
  (μ (qORegion X)).toReal = ‖(C9QPilotRegion.nativeQ X).q‖

/-- Conditional class-readout calibration from the mass-normalization condition. -/
theorem qOClassReadout_eq_qPilot_of_massNorm
    (μ : Measure (QCompletion X)) [Measure.IsAddHaarMeasure μ]
    (h : QORegionMassEqNorm X μ) :
    qOClassReadout X μ = qPilotSignedLog X := by
  rw [qOClassReadout_eq X μ]
  calc
    Real.log (μ (qORegion X)).toReal =
        Real.log ‖(C9QPilotRegion.nativeQ X).q‖ := by rw [h]
    _ = qORegionLogVolume X := rfl
    _ = qPilotKummerRelativeVolume X :=
      qORegionLogVolume_eq_qPilotKummer X
    _ = qPilotSignedLog X := qPilotKummerRelativeVolume_eq X

/-- Exact calibration target. -/
def QOClassReadoutCalibration
    (μ : Measure (QCompletion X)) [Measure.IsAddHaarMeasure μ] : Prop :=
  qOClassReadout X μ = qPilotSignedLog X

end LeanFormal.IUT.N8Closure.EtaQOClassCalibrationActual
