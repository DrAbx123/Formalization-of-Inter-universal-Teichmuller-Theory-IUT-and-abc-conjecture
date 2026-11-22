/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual

/-! # P1: place log-volume sign from residueNormBase > 1 -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1PlaceVolumeSignActual

open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual

variable {k : Type} [Field k] [NumberField k]

theorem log_residueNormBase_pos (v : NumberField.FinitePlace k) :
    0 < Real.log (residueNormBase v) := by
  exact Real.log_pos (residueNormBase_gt_one v)

theorem placeLogVolume_pos_of_norm_lt_one
    {I : LineBundle (k := k)} {v : NumberField.FinitePlace k}
    (d : LocalGeneratorData (k := k) I v)
    (hzero : d.generator ≠ 0) (hlt : ‖d.generator‖ < 1) :
    0 < placeLogVolume d := by
  unfold placeLogVolume
  have hpos : 0 < ‖d.generator‖ := norm_pos_iff.mpr hzero
  have hlog : Real.log ‖d.generator‖ < 0 := Real.log_neg hpos hlt
  linarith

theorem placeLogVolume_neg_of_one_lt_norm
    {I : LineBundle (k := k)} {v : NumberField.FinitePlace k}
    (d : LocalGeneratorData (k := k) I v)
    (hone : 1 < ‖d.generator‖) :
    placeLogVolume d < 0 := by
  unfold placeLogVolume
  have hlog : 0 < Real.log ‖d.generator‖ := Real.log_pos hone
  linarith

def placeVolumeSignRows : List (String × String × String) :=
  [ ("log_residueNormBase_pos", "residueNormBase > 1 => log > 0", "PROVED"),
    ("placeLogVolume_pos_of_norm_lt_one", "norm < 1 => placeLogVolume > 0", "PROVED"),
    ("placeLogVolume_neg_of_one_lt_norm", "1 < norm => placeLogVolume < 0", "PROVED") ]

theorem placeVolumeSignRows_length : placeVolumeSignRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1PlaceVolumeSignActual
