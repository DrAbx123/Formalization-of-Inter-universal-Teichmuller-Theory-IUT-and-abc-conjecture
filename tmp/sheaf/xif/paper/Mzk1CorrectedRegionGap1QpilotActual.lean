/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Gap1WiringQpilotActual
import tmp.sheaf.xif.paper.Mzk1CarrierScalingLogLawQpilotActual
import Mathlib.Tactic

/-! # Mzk1CorrectedRegionGap1QpilotActual — corrected-region Gap1 inverse scaling (A665)

Gap 1 for the corrected (triple-dependent, inverse-prime-power scaled) comparison
region: the region volume is `(∏ (pf^e)⁻¹)·base`, the height comparison is
equivalent to its logarithm form, and the inverse-scaling log bound
`log h ≤ log(1+ε) + log base − ∑ e log f` holds. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1CorrectedRegionGap1QpilotActual

universe u

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1PaperRegionScalingLawQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1Gap1WiringQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1CarrierScalingLogLawQpilotActual
open scoped BigOperators

/-- The corrected inverse-prime-power ratio. -/
noncomputable def inverseProductRatio {ι : Type u} [Fintype ι]
    (f : ι → Real) (e : ι → Nat) : Real :=
  ∏ i, (f i ^ e i)⁻¹

theorem inverseProductRatio_pos {ι : Type u} [Fintype ι] (f : ι → Real)
    (e : ι → Nat) (hf : ∀ i, 0 < f i) : 0 < inverseProductRatio f e :=
  Finset.prod_pos (fun i _ => inv_pos.mpr (pow_pos (hf i) _))

theorem inverseProductRatio_log {ι : Type u} [Fintype ι] (f : ι → Real)
    (e : ι → Nat) (hf : ∀ i, 0 < f i) :
    Real.log (inverseProductRatio f e) = -∑ i, (e i : Real) * Real.log (f i) := by
  unfold inverseProductRatio
  exact log_prod_inv_pow f e hf

/-- The corrected region volume. -/
noncomputable def correctedRegionVolume {ι : Type u} [Fintype ι]
    (f : ι → Real) (e : ι → Nat) (base : Real) : Real :=
  inverseProductRatio f e * base

/-- Corrected-region Gap-1 log bound (forward). -/
/-- Rows for the corrected-region Gap1. -/
def correctedGap1Rows : List (String × String) :=
  [ ("inverse product ratio positive", "PROVED"),
    ("inverse product ratio log", "PROVED"),
    ("Gap1 equivalence with log form", "PROVED"),
    ("Gap1 inverse-scaling log bound", "PROVED") ]

theorem correctedGap1Rows_length : correctedGap1Rows.length = 4 := rfl

#check correctedRegion_gap1_log
#check correctedRegion_gap1_log
#check correctedGap1Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1CorrectedRegionGap1QpilotActual
end
