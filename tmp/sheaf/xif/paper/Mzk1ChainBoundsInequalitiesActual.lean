import tmp.sheaf.xif.paper.Mzk1Cor312BoundsActual
import tmp.sheaf.xif.paper.Mzk1TargetABCInterfaceActual
import tmp.sheaf.xif.paper.Mzk1HeightVolumeComparisonActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1ChainBoundsInequalitiesActual — derived bound inequalities chain

Genuine derived inequalities combining EXIT0 bound interfaces:
* target height <= weight + bound, strengthened under a weight upper bound;
* target height <= combined + slack, from the combined bound;
* height <= explicit bound b from volume <= b via height <= volume.
No new paper input; no closure; gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ChainBoundsInequalitiesActual

open LeanFormal.IUT.XiFPaper.Mzk1Cor312BoundsActual
open LeanFormal.IUT.XiFPaper.Mzk1TargetABCInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1HeightVolumeComparisonActual

/-- Target height under a weight upper bound. -/
theorem target_height_le_of_weight_le {X : Type*} (d : ABCTargetData X) (x : X)
    {w : ℚ} (hw : d.weight x ≤ w) : d.height x ≤ w + d.bound := by
  have h := d.height_le x
  linarith

/-- Target height under a combined Cor312 bound, with slack. -/
theorem target_height_le_combined_add_slack {X : Type*} (d : ABCTargetData X)
    (c : Cor312Bounds) (x : X) (h : d.height x ≤ c.combined) :
    d.height x ≤ c.combined + c.slack :=
  c.combined_le_slack_add h

/-- Height under an explicit bound via the volume comparison. -/
theorem height_le_of_volume_le {X : Type*} (d : HeightVolumeComparison X) (x : X)
    {b : ℚ} (h : d.volume x ≤ b) : d.height x ≤ b :=
  d.height_le_of_volume_le x h

end LeanFormal.IUT.XiFPaper.Mzk1ChainBoundsInequalitiesActual

end
