import tmp.sheaf.n8.closure.EtaGeneralQHaarScalingActual
import tmp.sheaf.n8.closure.EtaGlobalRegionAtFActual

/-!
# Eta qO mass norm from general q scaling

Production general-q Haar scaling has the form

  mu(qO) = ofReal (||q||^d) * mu(O),   d = finrank_Qp (F-completion).

If mu(O)=1 then mu(qO).toReal = ||q||^d, not ||q||.  Therefore the
QORegionMassEqNorm identity mu(qO).toReal = ||q|| holds only in the
dimension-one case d=1.  For d!=1, the correct calibrated readout is

  log mu(qO) = d * qPilotSignedLog.

This file proves the power formula from general scaling + normalization and
records the exact dependency.  No arbitrary normalization is used.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaQORegionMassNormFromScaling

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.N8Closure.EtaPStepNormLink
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open ABCBridge.N8.C3TensorTargetCorrection

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : MeasurableSpace (CommonPrimeCompletion (nativeFPlaceAtPrime X)) :=
  nativePMeasurableSpace X

local notation "Kf" => CommonPrimeCompletion (nativeFPlaceAtPrime X)
local notation "dF" => Module.finrank ℚ_[nativePrime X] (Kf)

/-- Actual native q-unit at the F place. -/
noncomputable def nativeQUnitKf : (Kf)ˣ :=
  Units.mk0 (C9QPilotRegion.nativeQ X).q (C9QPilotRegion.nativeQ X).q_ne_zero

/-- Exact Haar normalization μ(O)=1. -/
def HaarNormalizedAtO
    (μ : Measure (Kf)) [μ.IsAddHaarMeasure] : Prop :=
  μ (Integers (Kf) : Set (Kf)) = 1

/-- Corrected qO mass target with the dimension power. -/
def QORegionMassNormPower
    (μ : Measure (Kf)) [μ.IsAddHaarMeasure] : Prop :=
  (μ (EtaGeneralQHaarScalingActual.qORegion X (nativeQUnitKf X))).toReal =
    ‖((nativeQUnitKf X) : Kf)‖ ^ dF

/-- Actual power formula from general q scaling + μ(O)=1. -/
theorem qORegionMassNormPower_of_scaling
    (μ : Measure (Kf)) [μ.IsAddHaarMeasure]
    (hscale : GeneralQHaarScalingTarget X μ)
    (hO : HaarNormalizedAtO X μ) :
    QORegionMassNormPower X μ := by
  have h := hscale (nativeQUnitKf X)
  rw [hO, mul_one] at h
  dsimp [QORegionMassNormPower]
  rw [h, ENNReal.toReal_ofReal (pow_nonneg (norm_nonneg _) _)]

/-- Dimension-one special case: the power formula reduces to the actual norm. -/
theorem qORegionMassNorm_of_scaling_dim_one
    (μ : Measure (Kf)) [μ.IsAddHaarMeasure]
    (hscale : GeneralQHaarScalingTarget X μ)
    (hO : HaarNormalizedAtO X μ)
    (hd : dF = 1) :
    (μ (EtaGeneralQHaarScalingActual.qORegion X (nativeQUnitKf X))).toReal =
      ‖((nativeQUnitKf X) : Kf)‖ := by
  have hpow := qORegionMassNormPower_of_scaling X μ hscale hO
  dsimp [QORegionMassNormPower] at hpow
  simpa [hd] using hpow

/-- Exact dependency record: the naive mass-norm identity is a dimension-one
statement; the general formula carries the d-th power. -/
def QORegionMassNormDimensionDependency
    (μ : Measure (Kf)) [μ.IsAddHaarMeasure] : Prop :=
  QORegionMassNormPower X μ

end LeanFormal.IUT.N8Closure.EtaQORegionMassNormFromScaling
