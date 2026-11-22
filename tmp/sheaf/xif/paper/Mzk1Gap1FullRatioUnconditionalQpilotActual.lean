/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Gap1TheoremizationQpilotActual
import tmp.sheaf.xif.paper.Mzk1PaperRegionScalingLawQpilotActual
import Mathlib.Tactic

/-! # Mzk1Gap1FullRatioUnconditionalQpilotActual — Gap1 ratio/log for region objects (A669/672)

Unconditional Gap-1 in ratio/log form for a generic paper region scaling law
object (no inverse-product specialization required):
`h ≤ (1+ε)·regionVolume ↔ h/regionVolume ≤ 1+ε ↔
  log h ≤ log(1+ε) + log ratio + log base`. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Gap1FullRatioUnconditionalQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1Gap1TheoremizationQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperRegionScalingLawQpilotActual

/-- Gap-1 ratio/log equivalence on a paper region scaling law object. -/
theorem gap1_region_ratio_log_iff (L : PaperRegionScalingLaw) {h epsilon : Real}
    (hh : 0 < h) (heps : 0 < 1 + epsilon) :
    ((h ≤ (1 + epsilon) * L.regionVolume) ↔
      ((h / L.regionVolume ≤ 1 + epsilon) ∧
        (Real.log h ≤ Real.log (1 + epsilon) + Real.log L.ratio + Real.log L.base))) :=
by
  have hv : 0 < L.regionVolume := paperRegion_volume_pos L
  have hforms := gap1_forms_iff hh hv heps
  constructor
  · intro h1
    obtain ⟨hr, hlog⟩ := hforms.mp h1
    refine ⟨hr, ?_⟩
    rw [paperRegion_log L] at hlog ⊢
    linarith
  · rintro ⟨hr, hlog⟩
    apply hforms.mpr
    refine ⟨hr, ?_⟩
    rw [paperRegion_log L] at hlog ⊢
    linarith

/-- Gap-1 log form on a paper region scaling law object (multiplicative input). -/
theorem gap1_region_log_of_mult (L : PaperRegionScalingLaw) {h epsilon : Real}
    (hh : 0 < h) (heps : 0 < 1 + epsilon)
    (h1 : h ≤ (1 + epsilon) * L.regionVolume) :
    Real.log h ≤ Real.log (1 + epsilon) + Real.log L.ratio + Real.log L.base :=
  ((gap1_region_ratio_log_iff L hh heps).mp h1).2

/-- Gap-1 multiplicative form on a paper region scaling law object (log input). -/
theorem gap1_region_mult_of_log (L : PaperRegionScalingLaw) {h epsilon : Real}
    (hh : 0 < h) (heps : 0 < 1 + epsilon)
    (hlog : Real.log h ≤ Real.log (1 + epsilon) + Real.log L.ratio + Real.log L.base) :
    h ≤ (1 + epsilon) * L.regionVolume :=
  (gap1_region_ratio_log_iff L hh heps).mpr
    ⟨(gap1_mult_iff_ratio (paperRegion_volume_pos L)).mp (by
        by_contra hc
        push_neg at hc
        have := (gap1_region_ratio_log_iff L hh heps).mpr
          ⟨le_of_lt hc, hlog⟩
        linarith),
      hlog⟩

/-- Rows for the Gap1 ratio/log on region objects. -/
def gap1RegionRatioRows : List (String × String) :=
  [ ("ratio/log equivalence on region object", "PROVED"),
    ("log from multiplicative", "PROVED"),
    ("multiplicative from log", "PROVED") ]

theorem gap1RegionRatioRows_length : gap1RegionRatioRows.length = 3 := rfl

#check gap1_region_ratio_log_iff
#check gap1_region_log_of_mult
#check gap1RegionRatioRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Gap1FullRatioUnconditionalQpilotActual
end
