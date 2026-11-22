import tmp.sheaf.n8.closure.EtaQORegionMassNormFromScaling
import tmp.sheaf.n8.closure.C9QPilotRegion

/-!
# Eta qO class readout normalized actual

General q Haar mass gives mu(qO).toReal = ||q||^d.  Hence the raw qO class
readout is d * log||q||, and after division by d the normalized readout is
log||q||.  The final identification log||q|| = qPilotSignedLog is the actual
F-place/native norm agreement (qORegionLogVolume = qPilotSignedLog); it is
recorded as an exact dependency, not assumed silently and not an arbitrary
normalization.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaQOClassReadoutNormalizedActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.EtaQORegionMassNormFromScaling
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open ABCBridge.N8.C3TensorTargetCorrection

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

local instance : MeasurableSpace (CommonPrimeCompletion (nativeFPlaceAtPrime X)) :=
  EtaPStepNormLink.nativePMeasurableSpace X

abbrev KfX : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)

local notation "dF" => Module.finrank ℚ_[nativePrime X] (KfX X)

/-- Actual qO region at the F-place. -/
def qORegionAtF : Set (KfX X) :=
  EtaGeneralQHaarScalingActual.qORegion X (nativeQUnitKf X)

/-- Raw qO class readout: log of the actual qO Haar mass. -/
noncomputable def qOClassReadoutAtF
    (μ : Measure (KfX X)) [μ.IsAddHaarMeasure] : ℝ :=
  Real.log (μ (qORegionAtF X)).toReal

/-- Normalized qO class readout; keeps the dimension d. -/
noncomputable def normalizedQOClassReadoutAtF
    (μ : Measure (KfX X)) [μ.IsAddHaarMeasure] : ℝ :=
  qOClassReadoutAtF X μ / (dF : ℝ)

/-- Exact F-place norm agreement: log of the transported native q norm is the
native q-pilot signed log.  This is the qORegionLogVolume = qPilotSignedLog
identification on the F completion. -/
def FPlaceLogNormAgreement : Prop :=
  Real.log ‖((nativeQUnitKf X) : KfX X)‖ = qPilotSignedLog X

/-- Conditional raw readout: qOClassReadoutAtF = d * qPilotSignedLog. -/
theorem qOClassReadoutAtF_eq_dim_mul
    (μ : Measure (KfX X)) [μ.IsAddHaarMeasure]
    (hscale : GeneralQHaarScalingTarget X μ)
    (hO : HaarNormalizedAtO X μ)
    (hlog : FPlaceLogNormAgreement X) :
    qOClassReadoutAtF X μ = (dF : ℝ) * qPilotSignedLog X := by
  have hpow : (μ (qORegionAtF X)).toReal =
      ‖((nativeQUnitKf X) : KfX X)‖ ^ dF :=
    qORegionMassNormPower_of_scaling X μ hscale hO
  unfold qOClassReadoutAtF
  rw [hpow, Real.log_pow, hlog]

/-- Conditional normalized readout equals qPilotSignedLog, provided d != 0. -/
theorem normalizedQOClassReadoutAtF_eq_qPilot
    (μ : Measure (KfX X)) [μ.IsAddHaarMeasure]
    (hscale : GeneralQHaarScalingTarget X μ)
    (hO : HaarNormalizedAtO X μ)
    (hlog : FPlaceLogNormAgreement X)
    (hd : (dF : ℝ) ≠ 0) :
    normalizedQOClassReadoutAtF X μ = qPilotSignedLog X := by
  unfold normalizedQOClassReadoutAtF
  rw [qOClassReadoutAtF_eq_dim_mul X μ hscale hO hlog]
  field_simp [hd]

/-- Exact normalized calibration target. -/
def NormalizedQOClassReadoutCalibration
    (μ : Measure (KfX X)) [μ.IsAddHaarMeasure] : Prop :=
  normalizedQOClassReadoutAtF X μ = qPilotSignedLog X

end LeanFormal.IUT.N8Closure.EtaQOClassReadoutNormalizedActual
