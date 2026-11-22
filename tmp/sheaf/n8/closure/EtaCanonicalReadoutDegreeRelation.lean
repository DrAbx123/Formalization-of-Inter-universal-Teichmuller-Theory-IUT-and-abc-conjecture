import tmp.sheaf.n8.closure.EtaGlobalQOReadoutCanonical
import tmp.sheaf.n8.closure.EtaGlobalQOReadoutDegreeActual
import tmp.sheaf.n8.closure.NativeC3
import tmp.sheaf.n8.closure.C9QPilotRegion
import tmp.sheaf.n8.closure.EtaQORegionMassNormFromScaling
import Mathlib

/-!
# Canonical readout degree relation

canonicalGlobalQOReadout is qOClassReadout X μQ on QCompletion; the corrected
readout is log of kfNormalizedHaar on the Kf corrected carrier.  The corrected
carrier equality and normalized-Haar formula are actual at Kf, but no actual
measure/carrier transport identifies the QCompletion μQ readout with the Kf
kfNormalizedHaar readout.  This file records the exact gap and, conditionally on
that gap, derives the relDegree/d relation to qPilotSignedLog.  No arbitrary
measure or cast is used.
-/

noncomputable section

set_option maxHeartbeats 800000

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.C9QThetaValuesNamed
open LeanFormal.IUT.N8Closure.C9PaperClosure
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaGlobalRegionAtFActual
open LeanFormal.IUT.N8Closure.EtaGlobalQOReadoutCanonical
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQORegionMassNormFromScaling
open ABCBridge.N8.C3TensorTargetCorrection
open LeanFormal.IUT.N8Closure.EtaGlobalQOReadoutDegreeActual
open LeanFormal.IUT.N8Closure.EtaFPlaceNormAgreementActualAttempt
open LeanFormal.IUT.N8Closure.EtaQBaseImageCondition
open LeanFormal.IUT.N8Closure.EtaQOAddHaarNormalizedCalibrationActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace

namespace LeanFormal.IUT.N8Closure.EtaCanonicalReadoutDegreeRelation

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable [MeasurableSpace (QCompletion X)] [BorelSpace (QCompletion X)]
variable [ProperSpace (QCompletion X)] [IsUltrametricDist (QCompletion X)]
variable [LocallyCompactSpace (QCompletion X)]

variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
  [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
  [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
  (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
  [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- Exact gap: canonical QCompletion μQ readout equals the Kf corrected
kfNormalizedHaar readout. -/
def CanonicalCorrectedReadoutGap : Prop :=
  canonicalGlobalQOReadout X = correctedGlobalQOReadout X

/-- Conditional relDegree/d relation: if the canonical and corrected readouts
agree, then the corrected normalized readout (canonical * relDegree / d) equals
qPilotSignedLog under QBaseImageCondition. -/
theorem canonical_readout_relDegree_div_eq_qPilot_of_gap
    (B : QBaseImageCondition X)
    (hgap : CanonicalCorrectedReadoutGap X)
    (hrel : (relDegree X : ℝ) ≠ 0)
    (hd : (Module.finrank ℚ_[nativePrime X]
        (EtaQOAddHaarNormalizedCalibrationActual.Kf X) : ℝ) ≠ 0) :
    canonicalGlobalQOReadout X * (relDegree X : ℝ) /
        (Module.finrank ℚ_[nativePrime X]
          (EtaQOAddHaarNormalizedCalibrationActual.Kf X) : ℝ) =
      qPilotSignedLog X := by
  have h := correctedNormalizedGlobalQOReadout_eq_qPilot (X := X) B hrel hd
  unfold correctedNormalizedGlobalQOReadout at h
  rw [← hgap] at h
  exact h

/-- Exact direct relation: under the same gap, canonical equals the Kf corrected
readout, whose formula is d * log of the normalized q norm (conditional on the
norm power relation). -/
theorem canonical_eq_dim_mul_log_of_gap
    (hgap : CanonicalCorrectedReadoutGap X)
    (hpow : NativeNormPowerRelation X)
    (hrel : (relDegree X : ℝ) ≠ 0) :
    canonicalGlobalQOReadout X =
      (Module.finrank ℚ_[nativePrime X]
        (EtaQOAddHaarNormalizedCalibrationActual.Kf X) : ℝ) *
        Real.log ‖((nativeQUnitKf X) :
          EtaQOAddHaarNormalizedCalibrationActual.Kf X)‖ := by
  rw [hgap]
  exact correctedGlobalQOReadout_eq_dim_mul_log (X := X) hpow hrel

end LeanFormal.IUT.N8Closure.EtaCanonicalReadoutDegreeRelation
