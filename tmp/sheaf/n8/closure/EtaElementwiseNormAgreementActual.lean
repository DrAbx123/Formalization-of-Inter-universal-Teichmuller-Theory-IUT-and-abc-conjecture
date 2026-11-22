import tmp.sheaf.n8.closure.EtaCanonicalCorrectedTransportActual
import tmp.sheaf.n8.closure.EtaFPlaceNormAgreementActualAttempt
import tmp.sheaf.n8.closure.EtaFPlaceLogNormAgreementActual
import Mathlib

/-!
# Elementwise norm agreement actual attempt

Production has:
- norm_commonPrime_eq_normalized (rfl): the CommonPrimeCompletion norm equals
  the NormalizedCompletion norm;
- normalizedCompletion_norm_eq_spectralNorm: the normalized completion norm is
  the spectral norm over the p-adic scalar field.

Neither compares the **default** QCompletion/Completion norm with the Kf
spectral norm.  The exact missing theorem is elementwise norm agreement between
QCompletion's default norm and Kf's norm (or at the native q radius).  This file
records that exact no-go; no arbitrary norm is assumed.
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
open LeanFormal.IUT.N8Closure.EtaCanonicalCorrectedTransportActual
open LeanFormal.IUT.N8Closure.EtaFPlaceNormAgreementActualAttempt
open LeanFormal.IUT.N8Closure.EtaFPlaceLogNormAgreementActual
open LeanFormal.IUT.N8Closure.EtaQOAddHaarNormalizedCalibrationActual
open LeanFormal.IUT.N8Closure.EtaContinuousAddEquivRecordActual2
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection

namespace LeanFormal.IUT.N8Closure.EtaElementwiseNormAgreementActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable [MeasurableSpace (QCompletion X)] [BorelSpace (QCompletion X)]
variable [ProperSpace (QCompletion X)] [IsUltrametricDist (QCompletion X)]
variable [LocallyCompactSpace (QCompletion X)]

local instance hKmeas : MeasurableSpace (EtaRssAdmissibleCorrection.K X) :=
  EtaPStepNormLink.nativePMeasurableSpace X

local instance hKborel : BorelSpace (EtaRssAdmissibleCorrection.K X) :=
  EtaPStepNormLink.nativePBorelSpace X

/-- Actual CommonPrimeCompletion/normalizedCompletion norm equality. -/
theorem norm_commonPrime_eq_normalized_actual
    (x : EtaRssAdmissibleCorrection.K X) :
    ‖x‖ = ‖(x : NormalizedCompletion (nativeFPlaceOverBad X))‖ :=
  rfl

/-- Exact missing elementwise norm agreement: the default QCompletion norm and
the Kf/CommonPrimeCompletion norm agree on every element. -/
def ElementwiseNormAgreement : Prop :=
  ∀ x : EtaRssAdmissibleCorrection.K X,
    ‖(qoContinuousAddEquiv X x : QCompletion X)‖ =
      ‖(x : EtaRssAdmissibleCorrection.K X)‖

/-- Exact carrier transport target that would close the corrected carrier gap. -/
def CorrectedCarrierTransportTarget : Prop :=
  (qoContinuousAddEquiv X) '' correctedGlobalQOCarrier X = qORegion X

/-- Exact no-go dependency: elementwise norm agreement plus the native q norm
agreement would give the carrier transport.  The first is not supplied by the
production normalized-vs-spectral bridge. -/
def ElementwiseNormAgreementNoGo : Prop :=
  ElementwiseNormAgreement X → FPlaceNormAgreement X →
    CorrectedCarrierTransportTarget X

/-- The goal remains exactly the elementwise norm agreement; the production
bridge is recorded separately and does not assert it. -/
def ElementwiseNormAgreementGap : Prop :=
  ElementwiseNormAgreement X

end LeanFormal.IUT.N8Closure.EtaElementwiseNormAgreementActual
