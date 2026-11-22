/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.Geometry.FinitePlaceDegreeSumBound
import tmp.sheaf.xif.paper.Mzk1B5CountLocalValuationBridgeActual
import Mathlib.Tactic

/-! # B5/count: residue norm = p^{f}, absolute-dimension normalization -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace LeanFormal.IUT.XiFPaper.Mzk1B5ResidueNormPowActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
open LeanFormal.IUT.XiFPaper.Mzk1B5CountLocalValuationBridgeActual
variable {K : Type} [Field K] [NumberField K]
theorem residueNormBase_eq_pow_inertiaDeg' (place : NumberField.FinitePlace K) :
    residueNormBase place =
      ((residueCharacteristic place : ℕ) : ℝ) ^
        (Ideal.span {(residueCharacteristic place : ℤ)}).inertiaDeg'
          place.maximalIdeal.asIdeal := by
  unfold residueNormBase
  letI : place.maximalIdeal.asIdeal.LiesOver
      (Ideal.span {(residueCharacteristic place : ℤ)}) :=
    ⟨(under_eq_span_residueCharacteristic place).symm⟩
  rw [Ideal.absNorm_eq_pow_inertiaDeg' (R := NumberField.RingOfIntegers K)
    place.maximalIdeal.asIdeal (p := residueCharacteristic place)
    (residueCharacteristic_prime place)]
  push_cast
  rfl
theorem log_residueNormBase_eq_inertiaDeg_mul_log_residueCharacteristic
    (place : NumberField.FinitePlace K) :
    Real.log (residueNormBase place) =
      ((Ideal.span {(residueCharacteristic place : ℤ)}).inertiaDeg'
        place.maximalIdeal.asIdeal : ℝ) *
        Real.log (residueCharacteristic place : ℝ) := by
  rw [residueNormBase_eq_pow_inertiaDeg', Real.log_pow]
theorem placeLogVolume_eq_neg_localValuation_mul_inertiaDeg_mul_log_char
    {I : LineBundle (k := K)} {v : NumberField.FinitePlace K}
    (d : LocalGeneratorData (k := K) I v)
    (hnorm : LocalNormGeneratorBridge (k := K) d) :
    placeLogVolume d =
      - (localValuation v d.generator : ℝ) *
        ((Ideal.span {(residueCharacteristic v : ℤ)}).inertiaDeg'
          v.maximalIdeal.asIdeal : ℝ) *
          Real.log (residueCharacteristic v : ℝ) := by
  unfold placeLogVolume
  unfold LocalNormGeneratorBridge at hnorm
  rw [hnorm, log_residueNormBase_eq_inertiaDeg_mul_log_residueCharacteristic]
  ring
theorem placeLogVolume_eq_neg_log_norm_of_normBridge
    {I : LineBundle (k := K)} {v : NumberField.FinitePlace K}
    (d : LocalGeneratorData (k := K) I v) :
    placeLogVolume d = - Real.log ‖d.generator‖ := rfl
end LeanFormal.IUT.XiFPaper.Mzk1B5ResidueNormPowActual
