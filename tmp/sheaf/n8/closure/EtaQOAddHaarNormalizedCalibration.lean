import tmp.sheaf.n8.closure.EtaGeneralQHaarScalingClosure
import tmp.sheaf.n8.closure.EtaQCompletionPropernessTransfer
import tmp.sheaf.n8.closure.EtaQRegionRepresentation
import Mathlib

/-!
# Eta qO additive-Haar normalized calibration

On the spectral-norm Kf = CommonPrimeCompletion (nativeFPlaceAtPrime X), the
actual additive Haar measure is normalized to unit integral-ball mass.  From the
char formula reduction

  generalQHaarScalingTarget_of_charFormula

the normalized measure satisfies

  (muNorm (qO(q))).toReal = ||q|| ^ d,   d = finrank_Qp Kf,

and its log is d * log ||q||.  The char formula remains the exact source gap.

The qPilot connection additionally needs the norm agreement between Kf's
spectral norm and QCompletion's default completion norm; that exact gap is
recorded as QKfNormAgreement.
-/

noncomputable section

open MeasureTheory BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingClosure
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open scoped NNReal ENNReal Pointwise NormedField

namespace LeanFormal.IUT.N8Closure.EtaQOAddHaarNormalizedCalibration

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

/-- The spectral-norm completion carrier. -/
abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)

/-- Actual additive Haar measure on Kf. -/
noncomputable def kfAddHaar : Measure (Kf X) :=
  Measure.addHaar

noncomputable instance kfAddHaar_isHaar : Measure.IsAddHaarMeasure (kfAddHaar X) :=
  Measure.isAddHaarMeasure_addHaarMeasure
    (Classical.arbitrary (TopologicalSpace.PositiveCompacts (Kf X)))

/-- Integral-unit-ball mass of the actual additive Haar. -/
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

/-- Conditional qO mass formula from the char formula. -/
theorem kfNormalizedHaar_qORegion_toReal
    (hchar : DistribHaarCharNormFormula X) (q : (Kf X)ˣ) :
    (kfNormalizedHaar X (qORegion X (q : Kf X))).toReal =
      ‖(q : Kf X)‖ ^ Module.finrank ℚ_[nativePrime X] (Kf X) := by
  letI : Measure.IsAddHaarMeasure (kfNormalizedHaar X) :=
    Measure.IsAddHaarMeasure.smul (kfAddHaar X)
      (c := (kfAddHaarIntegersMass X)⁻¹)
      (ENNReal.inv_ne_zero.mpr (kfAddHaarIntegersMass_ne_top X))
      (ENNReal.inv_ne_top.mpr (kfAddHaarIntegersMass_ne_zero X))
  haveI : (kfNormalizedHaar X).Regular :=
    MeasureTheory.Measure.Regular.smul (kfAddHaar X) (ENNReal.inv_ne_top.mpr (kfAddHaarIntegersMass_ne_zero X))
  have hscale := generalQHaarScalingTarget_of_charFormula (X := X) hchar
    (kfNormalizedHaar X)
    (by rw [kfNormalizedHaar_integers]; exact one_ne_zero)
    (by rw [kfNormalizedHaar_integers]; exact ENNReal.one_ne_top) q
  rw [hscale, kfNormalizedHaar_integers, mul_one,
    ENNReal.toReal_ofReal (pow_nonneg (norm_nonneg _) _)]

/-- Log form: the normalized qO readout is d * log ||q||. -/
theorem kfNormalizedHaar_qORegion_log
    (hchar : DistribHaarCharNormFormula X) (q : (Kf X)ˣ) :
    Real.log (kfNormalizedHaar X (qORegion X (q : Kf X))).toReal =
      (Module.finrank ℚ_[nativePrime X] (Kf X) : ℝ) * Real.log ‖(q : Kf X)‖ := by
  rw [kfNormalizedHaar_qORegion_toReal (X := X) hchar q]
  rw [Real.log_pow]

/-- Exact norm agreement needed to identify the Kf spectral-norm qO readout with
the QCompletion default-norm qPilotSignedLog. -/
def QKfNormAgreement : Prop :=
  ‖((C9QPilotRegion.nativeQ X).q : QCompletion X)‖ =
    ‖((C9QPilotRegion.nativeQ X).q : Kf X)‖

/-- Conditional qPilot connection: with the norm agreement, the normalized qO
log readout is d * qPilotSignedLog. -/
theorem kfNormalizedHaar_qORegion_log_nativeQ
    (hchar : DistribHaarCharNormFormula X)
    (hagree : QKfNormAgreement X) :
    Real.log (kfNormalizedHaar X
      (qORegion X ((C9QPilotRegion.nativeQ X).q : Kf X))).toReal =
      (Module.finrank ℚ_[nativePrime X] (Kf X) : ℝ) * qPilotSignedLog X := by
  rw [kfNormalizedHaar_qORegion_log (X := X) hchar
    (Units.mk0 ((C9QPilotRegion.nativeQ X).q) (C9QPilotRegion.nativeQ X).q_ne_zero)]
  rw [qPilotSignedLog_eq_localSignedLog]
  simp only [ArithmeticQPilotLogVolume.localSignedLog, Units.val_mk0]
  rw [← hagree]

end LeanFormal.IUT.N8Closure.EtaQOAddHaarNormalizedCalibration
