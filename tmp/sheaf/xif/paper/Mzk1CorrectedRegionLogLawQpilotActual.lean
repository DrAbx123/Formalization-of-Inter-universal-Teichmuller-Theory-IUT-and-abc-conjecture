/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1CorrectedRegionGap1QpilotActual
import Mathlib.Tactic

/-! # Mzk1CorrectedRegionLogLawQpilotActual — corrected region log law (A666)

The corrected (inverse-prime-power scaled) region log law in full:
`log correctedRegionVolume = log base − ∑ e log f`, its target form for the Gap-1
comparison `(1+ε)·regionVolume`, and the conditional Gap-1 recovery from the log
inequality. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1CorrectedRegionLogLawQpilotActual

universe u

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1PaperRegionScalingLawQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1Gap1WiringQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1CarrierScalingLogLawQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1CorrectedRegionGap1QpilotActual
open scoped BigOperators

/-- Log of the corrected region volume: `log base − ∑ e log f`. -/
theorem correctedRegion_log {ι : Type u} [Fintype ι] (f : ι → Real) (e : ι → Nat)
    (base : Real) (hf : ∀ i, 0 < f i) (hb : 0 < base) :
    Real.log (correctedRegionVolume f e base) =
      Real.log base - ∑ i, (e i : Real) * Real.log (f i) := by
  unfold correctedRegionVolume
  rw [Real.log_mul (ne_of_gt (inverseProductRatio_pos f e hf)) (ne_of_gt hb),
    inverseProductRatio_log f e hf]
  ring

/-- Log of the Gap-1 target `(1+ε)·regionVolume`. -/
theorem correctedRegion_target_log {ι : Type u} [Fintype ι] (f : ι → Real)
    (e : ι → Nat) (base : Real) (hf : ∀ i, 0 < f i) (hb : 0 < base)
    {epsilon : Real} (heps : 0 < 1 + epsilon) :
    Real.log ((1 + epsilon) * correctedRegionVolume f e base) =
      Real.log (1 + epsilon) + (Real.log base - ∑ i, (e i : Real) * Real.log (f i)) := by
  have hv : 0 < correctedRegionVolume f e base := by
    unfold correctedRegionVolume
    exact mul_pos (inverseProductRatio_pos f e hf) hb
  rw [Real.log_mul (ne_of_gt heps) (ne_of_gt hv), correctedRegion_log f e base hf hb]

/-- Conditional Gap-1: the log inequality recovers the height comparison. -/
theorem correctedRegion_gap1_of_log {ι : Type u} [Fintype ι] {h epsilon : Real}
    (f : ι → Real) (e : ι → Nat) (base : Real) (hf : ∀ i, 0 < f i)
    (hb : 0 < base) (hh : 0 < h) (heps : 0 < 1 + epsilon)
    (hlog : Real.log h ≤
      Real.log (1 + epsilon) - ∑ i, (e i : Real) * Real.log (f i) + Real.log base) :
    h ≤ (1 + epsilon) * correctedRegionVolume f e base := by
  have hv : 0 < correctedRegionVolume f e base := by
    unfold correctedRegionVolume
    exact mul_pos (inverseProductRatio_pos f e hf) hb
  have htarget : 0 < (1 + epsilon) * correctedRegionVolume f e base := mul_pos heps hv
  have hval : Real.log ((1 + epsilon) * correctedRegionVolume f e base) =
      Real.log (1 + epsilon) - ∑ i, (e i : Real) * Real.log (f i) + Real.log base :=
    correctedRegion_target_log f e base hf hb heps
  have : Real.log h ≤ Real.log ((1 + epsilon) * correctedRegionVolume f e base) := by
    rw [hval]
    linarith
  exact (Real.log_le_log_iff hh htarget).mp this

/-- Rows for the corrected region log law. -/
def correctedLogLawRows : List (String × String) :=
  [ ("log corrected region volume", "PROVED"),
    ("log Gap1 target", "PROVED"),
    ("conditional Gap1 from log inequality", "PROVED") ]

theorem correctedLogLawRows_length : correctedLogLawRows.length = 3 := rfl

#check correctedRegion_log
#check correctedRegion_gap1_of_log
#check correctedLogLawRows_length

end LeanFormal.IUT.XiFPaper.Mzk1CorrectedRegionLogLawQpilotActual
end
