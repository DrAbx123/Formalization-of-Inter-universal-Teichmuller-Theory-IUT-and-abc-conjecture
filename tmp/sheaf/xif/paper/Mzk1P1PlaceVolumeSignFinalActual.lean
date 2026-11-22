/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace LeanFormal.IUT.XiFPaper.Mzk1P1PlaceVolumeSignFinalActual
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
open LeanFormal.IUT.XiFPaper.Mzk1P1PlaceVolumeSignActual
variable {k : Type} [Field k] [NumberField k]
theorem placeLogVolume_nonneg_of_norm_le_one
    {I : LineBundle (k := k)} {v : NumberField.FinitePlace k}
    (d : LocalGeneratorData (k := k) I v)
    (hzero : d.generator ≠ 0) (hle : ‖d.generator‖ ≤ 1) :
    0 ≤ placeLogVolume d := by
  unfold placeLogVolume
  have hpos : 0 < ‖d.generator‖ := norm_pos_iff.mpr hzero
  have hlog : Real.log ‖d.generator‖ ≤ 0 := Real.log_nonpos hpos.le hle
  linarith
theorem placeLogVolume_nonpos_of_one_le_norm
    {I : LineBundle (k := k)} {v : NumberField.FinitePlace k}
    (d : LocalGeneratorData (k := k) I v) (hle : 1 ≤ ‖d.generator‖) :
    placeLogVolume d ≤ 0 := by
  unfold placeLogVolume
  have hlog : 0 ≤ Real.log ‖d.generator‖ := Real.log_nonneg hle
  linarith
end LeanFormal.IUT.XiFPaper.Mzk1P1PlaceVolumeSignFinalActual
