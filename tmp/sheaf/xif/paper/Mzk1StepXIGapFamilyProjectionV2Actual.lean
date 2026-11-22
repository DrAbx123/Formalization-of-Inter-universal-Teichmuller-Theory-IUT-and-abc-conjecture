import tmp.sheaf.xif.paper.Mzk1StepXIGap1Gap2AssemblyV2Actual
import tmp.sheaf.xif.paper.Mzk1StepXIGap1Gap2BridgeHeightActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi Gap1/Gap2 family components

Projection lemmas extracting the Gap1 input and Gap2 named input from a family. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGapFamilyProjectionV2Actual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeHeightRegionActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeGap1ConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1Gap2AssemblyV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGap1Gap2BridgeHeightActual

universe u

theorem stepxi_gap_family_ABC (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    (I : StepXIGapFamily X W logShellPoint) : ABCConjecture :=
  stepxi_gap_bridge_ABC X W logShellPoint I

theorem stepxi_gap_family_gap1 (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    (I : StepXIGapFamily X W logShellPoint)
    (ε : Real) (hε : 0 < ε) : StepXIGap1Input X W logShellPoint ε :=
  I.gap1 ε hε

theorem stepxi_gap_family_gap2 (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    (I : StepXIGapFamily X W logShellPoint)
    (ε : Real) (hε : 0 < ε) : Gap2NamedInput W logShellPoint ε :=
  I.gap2 ε hε

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGapFamilyProjectionV2Actual

end
