import tmp.sheaf.n8.closure.EtaFPlaceNormAgreementActualAttempt

/-!
# Eta qO class readout degree-corrected actual

Given the native/normalized norm power relation

  ||native q|| = ||normalized q|| ^ relDegree,

the raw qO readout is

  qOClassReadout = d * log ||normalized q|| = d * qPilot / relDegree.

Hence the degree-corrected normalized readout is

  qOClassReadout * relDegree / d,

and equals qPilotSignedLog for d != 0 and relDegree != 0.  The degree
relDegree is never dropped.  No arbitrary normalization is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaQOClassReadoutDegreeCorrected

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaQOClassReadoutNormalizedActual
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.EtaQORegionMassNormFromScaling
open LeanFormal.IUT.N8Closure.EtaFPlaceNormAgreementActualAttempt
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open ABCBridge.N8.C3TensorTargetCorrection

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Corrected normalized qO readout: multiply by relDegree before dividing by d. -/
noncomputable def correctedQOClassReadoutAtF
    (μ : Measure (KfX X)) [μ.IsAddHaarMeasure] : ℝ :=
  qOClassReadoutAtF X μ * (relDegree X : ℝ) / (Module.finrank ℚ_[nativePrime X] (KfX X) : ℝ)

local notation "dF" => Module.finrank ℚ_[nativePrime X] (KfX X)

/-- Actual qPilot = log of the native q norm. -/
theorem qPilot_eq_log_native :
    qPilotSignedLog X = Real.log ‖nativeQVal X‖ := by
  calc
    qPilotSignedLog X = qPilotKummerRelativeVolume X :=
      (qPilotKummerRelativeVolume_eq X).symm
    _ = qORegionLogVolume X := (qORegionLogVolume_eq_qPilotKummer X).symm
    _ = Real.log ‖(C9QPilotRegion.nativeQ X).q‖ := rfl
    _ = Real.log ‖nativeQVal X‖ := rfl

/-- Actual raw readout = d * log of the normalized norm. -/
theorem qOClassReadoutAtF_eq_dim_mul_logNormalized
    (μ : Measure (KfX X)) [μ.IsAddHaarMeasure]
    (hscale : GeneralQHaarScalingTarget X μ)
    (hO : HaarNormalizedAtO X μ) :
    qOClassReadoutAtF X μ =
      (dF : ℝ) * Real.log ‖normalizedQVal X‖ := by
  have hpow : (μ (qORegionAtF X)).toReal =
      ‖normalizedQVal X‖ ^ dF := by
    simpa [QORegionMassNormPower, normalizedQVal, qORegionAtF] using
      qORegionMassNormPower_of_scaling X μ hscale hO
  unfold qOClassReadoutAtF
  rw [hpow, Real.log_pow]

/-- From the norm power relation, log normalized = qPilot / relDegree. -/
theorem log_normalized_eq_qPilot_div_relDegree
    (hpow : NativeNormPowerRelation X)
    (hrel : (relDegree X : ℝ) ≠ 0) :
    Real.log ‖normalizedQVal X‖ = qPilotSignedLog X / (relDegree X : ℝ) := by
  have hnative : ‖nativeQVal X‖ = ‖normalizedQVal X‖ ^ relDegree X := hpow
  have hlog : Real.log ‖nativeQVal X‖ =
      (relDegree X : ℝ) * Real.log ‖normalizedQVal X‖ := by
    rw [hnative, Real.log_pow]
  have hqp : qPilotSignedLog X = Real.log ‖nativeQVal X‖ := qPilot_eq_log_native X
  rw [hqp, hlog]
  field_simp [hrel]

/-- Actual degree-corrected calibration: readout * relDegree / d = qPilot. -/
theorem correctedQOClassReadoutAtF_eq_qPilot
    (μ : Measure (KfX X)) [μ.IsAddHaarMeasure]
    (hscale : GeneralQHaarScalingTarget X μ)
    (hO : HaarNormalizedAtO X μ)
    (hpow : NativeNormPowerRelation X)
    (hd : (dF : ℝ) ≠ 0)
    (hrel : (relDegree X : ℝ) ≠ 0) :
    correctedQOClassReadoutAtF X μ = qPilotSignedLog X := by
  have hraw := qOClassReadoutAtF_eq_dim_mul_logNormalized X μ hscale hO
  have hlog := log_normalized_eq_qPilot_div_relDegree X hpow hrel
  unfold correctedQOClassReadoutAtF
  rw [hraw, hlog]
  field_simp [hd]

/-- Exact corrected calibration target. -/
def CorrectedQOClassReadoutCalibration
    (μ : Measure (KfX X)) [μ.IsAddHaarMeasure] : Prop :=
  correctedQOClassReadoutAtF X μ = qPilotSignedLog X

end LeanFormal.IUT.N8Closure.EtaQOClassReadoutDegreeCorrected
