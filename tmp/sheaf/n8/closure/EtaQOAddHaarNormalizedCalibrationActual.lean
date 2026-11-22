import tmp.sheaf.n8.closure.EtaCharFormulaInstantiation
import tmp.sheaf.n8.closure.EtaQCompletionPropernessTransfer
import tmp.sheaf.n8.closure.EtaQRegionRepresentation
import Mathlib

/-!
# Eta qO additive-Haar normalized calibration (actual)

The qside actual theorem generalQHaarScalingTarget_actual gives the additive
Haar scaling for Measure.addHaar on Kf = CommonPrimeCompletion
(nativeFPlaceAtPrime X):

  addHaar (qO(q)) = ofReal (||q|| ^ d) * addHaar (Integers).

Normalizing addHaar by the inverse integral-ball mass gives muNorm(Integers)=1,
and direct ENNReal cancellation yields

  (muNorm (qO(q))).toReal = ||q|| ^ d.

No char-formula assumption is needed in this file; it consumes the actual
theorem.  The qPilot connection still needs the exact norm agreement between the
spectral Kf norm and QCompletion's default completion norm.
-/

noncomputable section

open MeasureTheory BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.EtaCharFormulaInstantiation
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open scoped NNReal ENNReal Pointwise NormedField

namespace LeanFormal.IUT.N8Closure.EtaQOAddHaarNormalizedCalibrationActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)

/-- Actual additive Haar on Kf. -/
noncomputable def kfAddHaar : Measure (Kf X) :=
  (Measure.addHaar : Measure (Kf X))

noncomputable instance kfAddHaar_isHaar : Measure.IsAddHaarMeasure (kfAddHaar X) :=
  Measure.isAddHaarMeasure_addHaarMeasure
    (Classical.arbitrary (TopologicalSpace.PositiveCompacts (Kf X)))

/-- Actual integral-ball mass. -/
noncomputable def kfAddHaarIntegersMass : ENNReal :=
  kfAddHaar X (Integers (Kf X) : Set (Kf X))

theorem kfAddHaarIntegersMass_ne_zero : kfAddHaarIntegersMass X ≠ 0 :=
  (measure_localIntegers_pos_lt_top (K := Kf X) (kfAddHaar X)).1.ne'

theorem kfAddHaarIntegersMass_ne_top : kfAddHaarIntegersMass X ≠ ⊤ :=
  (measure_localIntegers_pos_lt_top (K := Kf X) (kfAddHaar X)).2.ne

/-- Actual normalized additive Haar on Kf. -/
noncomputable def kfNormalizedHaar : Measure (Kf X) :=
  (kfAddHaarIntegersMass X)⁻¹ • kfAddHaar X

theorem kfNormalizedHaar_integers :
    kfNormalizedHaar X (Integers (Kf X) : Set (Kf X)) = 1 := by
  rw [kfNormalizedHaar, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (kfAddHaarIntegersMass_ne_zero X)
    (kfAddHaarIntegersMass_ne_top X)

/-- Actual qO mass formula for the normalized Haar, from the actual scaling
theorem (no char-formula assumption). -/
theorem kfNormalizedHaar_qORegion_toReal (q : (Kf X)ˣ) :
    (kfNormalizedHaar X (qORegion X (q : Kf X))).toReal =
      ‖(q : Kf X)‖ ^ Module.finrank ℚ_[nativePrime X] (Kf X) := by
  letI : Measure.IsAddHaarMeasure (kfNormalizedHaar X) :=
    Measure.IsAddHaarMeasure.smul (kfAddHaar X)
      (c := (kfAddHaarIntegersMass X)⁻¹)
      (ENNReal.inv_ne_zero.mpr (kfAddHaarIntegersMass_ne_top X))
      (ENNReal.inv_ne_top.mpr (kfAddHaarIntegersMass_ne_zero X))
  haveI : (kfNormalizedHaar X).Regular :=
    MeasureTheory.Measure.Regular.smul (μ := kfAddHaar X)
      (ENNReal.inv_ne_top.mpr (kfAddHaarIntegersMass_ne_zero X))
  have hscale := EtaGeneralQHaarScalingClosure.generalQHaarScalingTarget_of_charFormula
    (X := X) (distribHaarCharNormFormula_actual X) (kfNormalizedHaar X)
    (by rw [kfNormalizedHaar_integers]; exact one_ne_zero)
    (by rw [kfNormalizedHaar_integers]; exact ENNReal.one_ne_top) q
  rw [hscale, kfNormalizedHaar_integers, mul_one,
    ENNReal.toReal_ofReal (pow_nonneg (norm_nonneg _) _)]

/-- Log form of the actual normalized qO readout. -/
theorem kfNormalizedHaar_qORegion_log (q : (Kf X)ˣ) :
    Real.log (kfNormalizedHaar X (qORegion X (q : Kf X))).toReal =
      (Module.finrank ℚ_[nativePrime X] (Kf X) : ℝ) * Real.log ‖(q : Kf X)‖ := by
  rw [kfNormalizedHaar_qORegion_toReal (X := X) q]
  rw [Real.log_pow]

end LeanFormal.IUT.N8Closure.EtaQOAddHaarNormalizedCalibrationActual
