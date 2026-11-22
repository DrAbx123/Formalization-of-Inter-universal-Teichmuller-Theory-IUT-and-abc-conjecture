import tmp.sheaf.n8.closure.EtaGlobalQOReadoutDegreeActual
import tmp.sheaf.n8.closure.NativeC3
import tmp.sheaf.n8.closure.EtaVaryingCalibrationActual
import tmp.sheaf.n8.closure.EtaComparisonVaryingTarget
import Mathlib

/-!
# Eta consumer QO calibration actual

The actual corrected normalized global qO readout equals qPilotSignedLog under
QBaseImageCondition.  The consumer Q calibration is

  O.Q = logVolumeReadout (sourceOpenClass K muK).

This file records:
- the exact equivalence between the consumer open-class gap and the
  corrected-readout/open-class measure equality;
- a conditional Q calibration from O.Q = corrected readout and the exact
  open-class measure equality;
- the exact remaining carrier/measure gap (open-class vs qO corrected readout).

No arbitrary calibration is used.
-/

noncomputable section

set_option maxHeartbeats 800000

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.C9QThetaValuesNamed
open LeanFormal.IUT.N8Closure.C9PaperClosure
open LeanFormal.IUT.N8Closure.EtaComparisonVaryingTarget
open LeanFormal.IUT.N8Closure.EtaRssNontrivialActual
open LeanFormal.IUT.N8Closure.EtaRssSourceRegionBridge
open LeanFormal.IUT.N8Closure.EtaVaryingCalibrationActual
open LeanFormal.IUT.N8Closure.EtaGlobalQOReadoutDegreeActual
open LeanFormal.IUT.N8Closure.EtaQBaseImageCondition
open LeanFormal.IUT.N8Closure.EtaFPlaceNormAgreementActualAttempt
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.EtaQORegionMassNormFromScaling

namespace LeanFormal.IUT.N8Closure.EtaConsumerQOCalibrationActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
  [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
  [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
  (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
  [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

variable (K : Type u) [NormedField K] [MeasurableSpace K] [BorelSpace K]
  [IsUltrametricDist K] [ProperSpace K]
  (muK : Measure K) [Measure.IsAddHaarMeasure muK]

/-- Exact open-class measure equality needed by the consumer Q calibration: the
canonical open-class readout equals the actual corrected global qO readout. -/
def QOConsumerOpenMeasureGap (O : PaperC9Output (X := X) mu) : Prop :=
  logVolumeReadout (K := K) (mu := muK) (sourceOpenClass (K := K) (mu := muK)) =
    correctedNormalizedGlobalQOReadout X

/-- The consumer's open-class gap is equivalent to the corrected-readout/open
measure equality, given the exact corrected-readout qPilot identification. -/
theorem QOpenReadoutGap_iff_QOConsumerOpenMeasureGap
    (hcorr : correctedNormalizedGlobalQOReadout X = qPilotSignedLog X)
    (O : PaperC9Output (X := X) mu) :
    QOpenReadoutGap (X := X) (mu := mu) K muK O ↔
      QOConsumerOpenMeasureGap (X := X) (mu := mu) K muK O := by
  unfold QOpenReadoutGap QOConsumerOpenMeasureGap
  rw [hcorr]
  exact eq_comm

/-- Conditional Q calibration: O.Q equals the corrected actual readout and the
exact open-class measure gap gives the consumer calibration. -/
theorem etaVaryingQCalibration_of_correctedReadout
    (O : PaperC9Output (X := X) mu)
    (hQ : O.Q = correctedNormalizedGlobalQOReadout X)
    (hOpen : QOConsumerOpenMeasureGap (X := X) (mu := mu) K muK O) :
    EtaVaryingQCalibration (X := X) (mu := mu) K muK O := by
  unfold EtaVaryingQCalibration QOConsumerOpenMeasureGap at *
  rw [hQ, hOpen]

/-- Exact remaining gap: no production theorem identifies the canonical
open-class readout with the actual qO corrected readout.  This is exactly the
open-class measure equality above, not an arbitrary calibration. -/
def QOConsumerCarrierMeasureGap (O : PaperC9Output (X := X) mu) : Prop :=
  QOConsumerOpenMeasureGap (X := X) (mu := mu) K muK O

end LeanFormal.IUT.N8Closure.EtaConsumerQOCalibrationActual
