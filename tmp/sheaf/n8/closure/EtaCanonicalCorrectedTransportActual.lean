import tmp.sheaf.n8.closure.EtaCanonicalCorrectedReadoutActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36CompletionIsometry
import tmp.sheaf.n8.closure.EtaContinuousAddEquivRecordActual2
import tmp.sheaf.n8.closure.EtaGlobalQODegreeCorrectedAlignment
import Mathlib
import tmp.sheaf.n8.closure.EtaNormalizedHaarTransportActual

/-!
# Canonical corrected transport actual attempt

The actual function of qoContinuousAddEquiv is qoCompletionRingEquiv (identity
on underlying elements).  The production norm bridge
normalizedCompletion_norm_eq_spectralNorm identifies the normalized completion
norm with the spectral norm, but not the default QCompletion/Completion norm
with the Kf spectral norm for all elements.  The exact missing input is the
elementwise norm agreement (or the resulting carrier ball transport); without
it the image of correctedGlobalQOCarrier in QCompletion is not identified with
qORegion.  No arbitrary cast is used.
-/

noncomputable section

set_option maxHeartbeats 800000

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaGlobalRegionAtFActual
open LeanFormal.IUT.N8Closure.EtaGlobalQOReadoutDegreeActual
open LeanFormal.IUT.N8Closure.EtaGlobalQODegreeCorrectedAlignment
open LeanFormal.IUT.N8Closure.EtaCanonicalCorrectedReadoutActual
open LeanFormal.IUT.N8Closure.EtaContinuousAddEquivRecordActual2
open LeanFormal.IUT.N8Closure.EtaNormalizedHaarTransportActual
open LeanFormal.IUT.N8Closure.EtaQOAddHaarNormalizedCalibrationActual
open LeanFormal.IUT.N8Closure.EtaPStepNormLink
open LeanFormal.IUT.N8Closure.EtaQORegionMassNormFromScaling
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection

namespace LeanFormal.IUT.N8Closure.EtaCanonicalCorrectedTransportActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable [MeasurableSpace (QCompletion X)] [BorelSpace (QCompletion X)]
variable [ProperSpace (QCompletion X)] [IsUltrametricDist (QCompletion X)]
variable [LocallyCompactSpace (QCompletion X)]

local instance hKmeas : MeasurableSpace (EtaRssAdmissibleCorrection.K X) :=
  nativePMeasurableSpace X

local instance hKborel : BorelSpace (EtaRssAdmissibleCorrection.K X) :=
  nativePBorelSpace X

/-- Actual function of qoContinuousAddEquiv is the completion ring equivalence
(identity on underlying elements). -/
theorem qoContinuousAddEquiv_apply_eq_ringEquiv
    (x : EtaRssAdmissibleCorrection.K X) :
    qoContinuousAddEquiv X x = qoCompletionRingEquiv X x :=
  homeomorph_apply_eq_ringEquiv X x

/-- Exact elementwise norm agreement missing between the default QCompletion
norm and the Kf spectral norm. -/
def ElementwiseNormAgreement : Prop :=
  ∀ x : EtaRssAdmissibleCorrection.K X,
    ‖(qoContinuousAddEquiv X x : QCompletion X)‖ =
      ‖(x : EtaRssAdmissibleCorrection.K X)‖

/-- Exact carrier transport target. -/
def CorrectedCarrierTransportTarget : Prop :=
  (qoContinuousAddEquiv X) '' correctedGlobalQOCarrier X = qORegion X

/-- Exact no-go record: the image equality needs the elementwise norm agreement
between QCompletion's default norm and the Kf spectral norm; the available
normalized-vs-spectral bridge does not supply it.  No arbitrary cast. -/
def CanonicalCorrectedTransportNoGo : Prop :=
  ElementwiseNormAgreement X → CorrectedCarrierTransportTarget X

end LeanFormal.IUT.N8Closure.EtaCanonicalCorrectedTransportActual
