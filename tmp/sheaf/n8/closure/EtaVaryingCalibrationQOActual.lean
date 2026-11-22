import tmp.sheaf.n8.closure.EtaQRegionRepresentation
import tmp.sheaf.n8.closure.EtaQRegionHaarCalibrationActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
import Mathlib

/-!
# Eta varying calibration QO actual attempt

The actual qO region of the native bad completion has log norm

  qORegionLogVolume X = qPilotKummerRelativeVolume X = qPilotSignedLog X.

If the actual additive Haar calibration of qO holds and the integral unit ball
has mass 1, then log of the qO Haar mass is exactly qPilotSignedLog X.  The
missing Haar scaling theorem and the unit-mass normalization are exact facts,
not arbitrary K/mu choices.  No arbitrary calibration is introduced.
-/

noncomputable section

open MeasureTheory BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits

namespace LeanFormal.IUT.N8Closure.EtaVaryingCalibrationQOActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Actual qO log norm equals the production q-pilot signed log. -/
theorem qORegionLogVolume_eq_qPilotSignedLog :
    qORegionLogVolume X = qPilotSignedLog X := by
  rw [qORegionLogVolume_eq_qPilotKummer, qPilotKummerRelativeVolume_eq]

/-- Conditional Q calibration: if the actual qO Haar scaling holds and the
integral unit ball has normalized mass 1, then the log of the qO Haar mass is
qPilotSignedLog. -/
theorem log_measure_qORegion_eq_qPilotSignedLog_of_calibration
    (mu : Measure (QCompletion X)) [Measure.IsAddHaarMeasure mu]
    (hcal : EtaQRegionHaarCalibration X mu)
    (hunit : mu (Integers (QCompletion X) : Set (QCompletion X)) = 1) :
    Real.log (mu (qORegion X)).toReal = qPilotSignedLog X := by
  rw [hcal, hunit, mul_one]
  rw [ENNReal.toReal_ofReal (Real.exp_pos (qORegionLogVolume X)).le, Real.log_exp]
  exact qORegionLogVolume_eq_qPilotSignedLog X

end LeanFormal.IUT.N8Closure.EtaVaryingCalibrationQOActual
