/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1B5ResidueNormPowActual
import LeanFormal.IUT.Foundations.Geometry.FinitePlaceDegreeSumBound
import Mathlib.Tactic

/-! # B5: absolute-dimension normalization of place log-volume -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace LeanFormal.IUT.XiFPaper.Mzk1B5AbsoluteDimensionNormalizationActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
open LeanFormal.IUT.XiFPaper.Mzk1B5CountLocalValuationBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1B5ResidueNormPowActual
variable {K : Type} [Field K] [NumberField K]
theorem placeLogVolume_mul_ramificationIndex_eq
    {I : LineBundle (k := K)} {v : NumberField.FinitePlace K}
    (d : LocalGeneratorData (k := K) I v) :
    placeLogVolume d * (residueRamificationIndex v : ℝ) =
      - (localValuation v d.generator : ℝ) *
        (residueLocalDegree v : ℝ) * Real.log (residueCharacteristic v : ℝ) := by
  rw [placeLogVolume_eq_neg_localValuation_mul_inertiaDeg_mul_log_char]
  unfold residueLocalDegree
  push_cast
  ring
theorem placeLogVolume_div_residueLocalDegree_eq
    {I : LineBundle (k := K)} {v : NumberField.FinitePlace K}
    (d : LocalGeneratorData (k := K) I v)
    (he : (residueRamificationIndex v : ℝ) ≠ 0) :
    placeLogVolume d / (residueLocalDegree v : ℝ) =
      - (localValuation v d.generator : ℝ) /
          (residueRamificationIndex v : ℝ) * Real.log (residueCharacteristic v : ℝ) := by
  have h := placeLogVolume_mul_ramificationIndex_eq d
  unfold residueLocalDegree at h ⊢
  push_cast at h ⊢
  field_simp [he]
  linarith
end LeanFormal.IUT.XiFPaper.Mzk1B5AbsoluteDimensionNormalizationActual
