import tmp.sheaf.n8.closure.EtaVaryingCalibrationQOActual
import Mathlib

/-!
# Eta qO unit-ball mass-one actual normalization

For any actual additive Haar measure muO on the native q completion, scaling by
the inverse of the integral-unit-ball mass gives an actual additive Haar measure
with unit-ball mass 1.  The only inputs are the exact Haar mass facts
muO(Integers) != 0 and muO(Integers) != top; these are not arbitrary
normalization theorems.  The qO Haar scaling theorem remains separate.
-/

noncomputable section

open MeasureTheory BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaVaryingCalibrationQOActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped ENNReal

namespace LeanFormal.IUT.N8Closure.EtaQOUnitBallMassOneActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable (muO : Measure (QCompletion X)) [Measure.IsAddHaarMeasure muO]

/-- Actual integral-unit-ball mass of the supplied Haar measure. -/
noncomputable def qOAddHaarIntegersMass : ENNReal :=
  muO (Integers (QCompletion X) : Set (QCompletion X))

variable (hmass0 : qOAddHaarIntegersMass X muO ≠ 0)
  (hmassTop : qOAddHaarIntegersMass X muO ≠ ⊤)

/-- Normalized additive Haar measure: inverse unit-ball mass times muO. -/
noncomputable def qONormalizedHaar : Measure (QCompletion X) :=
  (qOAddHaarIntegersMass X muO)⁻¹ • muO

theorem qONormalizedHaar_isHaar
    (hmass0 : qOAddHaarIntegersMass X muO ≠ 0)
    (hmassTop : qOAddHaarIntegersMass X muO ≠ ⊤) :
    Measure.IsAddHaarMeasure (qONormalizedHaar X muO) :=
  Measure.IsAddHaarMeasure.smul muO (c := (qOAddHaarIntegersMass X muO)⁻¹)
    (ENNReal.inv_ne_zero.mpr hmassTop)
    (ENNReal.inv_ne_top.mpr hmass0)

/-- The normalized actual Haar measure has unit-ball mass 1. -/
theorem qONormalizedHaar_integers
    (hmass0 : qOAddHaarIntegersMass X muO ≠ 0)
    (hmassTop : qOAddHaarIntegersMass X muO ≠ ⊤) :
    qONormalizedHaar X muO
        (Integers (QCompletion X) : Set (QCompletion X)) = 1 := by
  rw [qONormalizedHaar, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hmass0 hmassTop

/-- Actual unit-ball mass-one fact for the normalized measure. -/
theorem qOUnitBallMassOne_actual
    (hmass0 : qOAddHaarIntegersMass X muO ≠ 0)
    (hmassTop : qOAddHaarIntegersMass X muO ≠ ⊤) :
    qONormalizedHaar X muO
        (Integers (QCompletion X) : Set (QCompletion X)) = 1 :=
  qONormalizedHaar_integers X muO hmass0 hmassTop

/-- Conditional qO log calibration with normalized Haar: only the raw qO
scaling equality remains. -/
theorem log_measure_qORegion_eq_qPilotSignedLog_of_scaling
    (hmass0 : qOAddHaarIntegersMass X muO ≠ 0)
    (hmassTop : qOAddHaarIntegersMass X muO ≠ ⊤)
    (hcal : (qONormalizedHaar X muO) (qORegion X) =
      ENNReal.ofReal (Real.exp (qORegionLogVolume X)) *
        (qONormalizedHaar X muO)
          (Integers (QCompletion X) : Set (QCompletion X))) :
    Real.log ((qONormalizedHaar X muO) (qORegion X)).toReal = qPilotSignedLog X := by
  letI : Measure.IsAddHaarMeasure (qONormalizedHaar X muO) :=
    qONormalizedHaar_isHaar X muO hmass0 hmassTop
  have hcal' : EtaQRegionHaarCalibration X (qONormalizedHaar X muO) := hcal
  exact log_measure_qORegion_eq_qPilotSignedLog_of_calibration (X := X)
    (qONormalizedHaar X muO) hcal'
    (qONormalizedHaar_integers X muO hmass0 hmassTop)

end LeanFormal.IUT.N8Closure.EtaQOUnitBallMassOneActual
