/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1CarrierScalingLogLawQpilotActual
import Mathlib.Tactic

/-! # Mzk1PaperRegionScalingLawQpilotActual — paper region scaling law (A664)

A paper comparison-region scaling law object: the region volume is a ratio times a
base volume, with the ratio the inverse product of prime powers; its logarithm is
`log base − ∑ e_i·log f_i` (the real-level paper region scaling law). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperRegionScalingLawQpilotActual

universe u

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1CarrierScalingLogLawQpilotActual
open scoped BigOperators

/-- The paper region scaling law: `regionVolume = ratio * base`. -/
structure PaperRegionScalingLaw where
  base : Real
  ratio : Real
  regionVolume : Real
  base_pos : 0 < base
  ratio_pos : 0 < ratio
  volume_eq : regionVolume = ratio * base

/-- Log form of the paper region scaling law. -/
theorem paperRegion_log (L : PaperRegionScalingLaw) :
    Real.log L.regionVolume = Real.log L.ratio + Real.log L.base := by
  rw [L.volume_eq, Real.log_mul (ne_of_gt L.ratio_pos) (ne_of_gt L.base_pos)]

/-- Log form when the ratio is an inverse product of prime powers. -/
theorem paperRegion_log_ratio_prod {ι : Type u} [Fintype ι]
    (L : PaperRegionScalingLaw) (f : ι → Real) (e : ι → Nat)
    (hf : ∀ i, 0 < f i)
    (hratio : L.ratio = ∏ i, (f i ^ e i)⁻¹) :
    Real.log L.regionVolume =
      Real.log L.base - ∑ i, (e i : Real) * Real.log (f i) := by
  rw [paperRegion_log L, hratio, log_prod_inv_pow f e hf]
  ring

/-- The region volume is positive. -/
theorem paperRegion_volume_pos (L : PaperRegionScalingLaw) :
    0 < L.regionVolume := by
  rw [L.volume_eq]
  exact mul_pos L.ratio_pos L.base_pos

/-- Rows for the paper region scaling law. -/
def paperRegionScalingRows : List (String × String) :=
  [ ("regionVolume = ratio * base", "DEFINED"),
    ("log form", "PROVED"),
    ("inverse-product ratio log form", "PROVED"),
    ("region volume positive", "PROVED") ]

theorem paperRegionScalingRows_length : paperRegionScalingRows.length = 4 := rfl

#check paperRegion_log
#check paperRegion_log_ratio_prod
#check paperRegion_volume_pos
#check paperRegionScalingRows_length

end LeanFormal.IUT.XiFPaper.Mzk1PaperRegionScalingLawQpilotActual
end
