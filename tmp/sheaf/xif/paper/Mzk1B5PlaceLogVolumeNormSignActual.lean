/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1B5ResidueNormPowActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1B5PlaceLogVolumeNormSignActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
open LeanFormal.IUT.XiFPaper.Mzk1B5ResidueNormPowActual
variable {K : Type} [Field K] [NumberField K]
theorem placeLogVolume_pos_iff_norm_lt_one
    {I : LineBundle (k := K)} {v : NumberField.FinitePlace K}
    (d : LocalGeneratorData (k := K) I v) (hzero : d.generator ≠ 0) :
    0 < placeLogVolume d ↔ ‖d.generator‖ < 1 := by
  rw [placeLogVolume_eq_neg_log_norm_of_normBridge]
  have hpos : 0 < ‖d.generator‖ := norm_pos_iff.mpr hzero
  rw [neg_pos, Real.log_neg_iff hpos]
theorem placeLogVolume_neg_iff_one_lt_norm
    {I : LineBundle (k := K)} {v : NumberField.FinitePlace K}
    (d : LocalGeneratorData (k := K) I v) (hzero : d.generator ≠ 0) :
    placeLogVolume d < 0 ↔ 1 < ‖d.generator‖ := by
  rw [placeLogVolume_eq_neg_log_norm_of_normBridge]
  have hpos : 0 < ‖d.generator‖ := norm_pos_iff.mpr hzero
  rw [neg_lt_zero, Real.log_pos_iff]


end LeanFormal.IUT.XiFPaper.Mzk1B5PlaceLogVolumeNormSignActual
