import tmp.sheaf.n8.closure.EtaCanonicalReadoutDegreeRelation
import tmp.sheaf.n8.closure.EtaQOAddHaarNormalizedCalibrationActual
import tmp.sheaf.n8.closure.EtaContinuousAddEquivRecordActual2
import tmp.sheaf.n8.closure.EtaNormalizedHaarBothActual
import tmp.sheaf.n8.closure.EtaGlobalQODegreeCorrectedAlignment
import Mathlib

/-!
# Canonical corrected readout actual attempt

The actual ingredients are:
- muQ = pushed on qORegion (normalized-Haar uniqueness closure);
- pushed = Measure.map qoContinuousAddEquiv muK;
- muK and kfNormalizedHaar are the same normalized Haar on the Kf carrier;
- correctedGlobalQOCarrier = qORegion in the Kf spectral carrier.

The missing step is the carrier transport under qoContinuousAddEquiv from the
Kf corrected carrier to the QCompletion qORegion.  This file records the exact
transport gap and the conditional readout equality.  No arbitrary measure or
cast is used.
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
open LeanFormal.IUT.N8Closure.EtaGlobalRssAtF
open LeanFormal.IUT.N8Closure.EtaQOClassGlobalActual
open LeanFormal.IUT.N8Closure.EtaGlobalQOReadoutCanonical
open LeanFormal.IUT.N8Closure.EtaGlobalQOReadoutDegreeActual
open LeanFormal.IUT.N8Closure.EtaGlobalQODegreeCorrectedAlignment
open LeanFormal.IUT.N8Closure.EtaContinuousAddEquivRecordActual2
open LeanFormal.IUT.N8Closure.EtaNormalizedHaarBothActual
open LeanFormal.IUT.N8Closure.EtaQOAddHaarNormalizedCalibrationActual
open LeanFormal.IUT.N8Closure.EtaCanonicalReadoutDegreeRelation
open LeanFormal.IUT.N8Closure.EtaQBaseImageCondition
open LeanFormal.IUT.N8Closure.EtaFPlaceNormAgreementActualAttempt
open LeanFormal.IUT.N8Closure.EtaPStepNormLink
open LeanFormal.IUT.N8Closure.EtaQORegionMassNormFromScaling
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection

namespace LeanFormal.IUT.N8Closure.EtaCanonicalCorrectedReadoutActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable [MeasurableSpace (QCompletion X)] [BorelSpace (QCompletion X)]
variable [ProperSpace (QCompletion X)] [IsUltrametricDist (QCompletion X)]
variable [LocallyCompactSpace (QCompletion X)]

local instance hKmeas : MeasurableSpace (EtaRssAdmissibleCorrection.K X) :=
  nativePMeasurableSpace X

local instance hKborel : BorelSpace (EtaRssAdmissibleCorrection.K X) :=
  nativePBorelSpace X

/-- Pushed is the actual map of μK along the actual ContinuousAddEquiv. -/
theorem pushed_eq_map_μK :
    pushed X = Measure.map (qoContinuousAddEquiv X) (EtaContinuousAddEquivRecordActual2.μK X) :=
  rfl

/-- The normalized Kf Haar and the normalized K Haar are the same actual
measure (both are inverse-mass smul of additive Haar). -/
theorem kfNormalizedHaar_eq_μK :
    (EtaQOAddHaarNormalizedCalibrationActual.kfNormalizedHaar X :
      Measure (EtaRssAdmissibleCorrection.K X)) = EtaContinuousAddEquivRecordActual2.μK X := by
  rfl

/-- Exact carrier transport gap: the actual ContinuousAddEquiv maps the Kf
corrected carrier onto the QCompletion qORegion. -/
def CanonicalCorrectedCarrierTransport : Prop :=
  (qoContinuousAddEquiv X) '' correctedGlobalQOCarrier X = qORegion X

/-- Exact missing measure uniqueness/transport input: the carrier transport
above plus equality of the two normalized Haar measures. -/
structure CanonicalCorrectedTransportData : Prop where
  carrierTransport : CanonicalCorrectedCarrierTransport X
  haar_eq : (EtaQOAddHaarNormalizedCalibrationActual.kfNormalizedHaar X :
      Measure (EtaRssAdmissibleCorrection.K X)) = EtaContinuousAddEquivRecordActual2.μK X

end LeanFormal.IUT.N8Closure.EtaCanonicalCorrectedReadoutActual
