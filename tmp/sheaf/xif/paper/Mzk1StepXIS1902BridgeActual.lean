import tmp.sheaf.xif.paper.Mzk1ABCEntryQpilotActual
import tmp.sheaf.xif.paper.Mzk1ABCBridgeGap1ConsumerActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi S1902 concrete bridge consumer

Consumes the green ABC bridge interfaces from the qpilot/gap1 owners. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIS1902BridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCEntryQpilotActual

structure StepXIBridgeInput where
  bridge : Cor312ToABCBridgeInterface

theorem stepxi_bridge_heightBound (I : StepXIBridgeInput) :
    forall epsilon : Real, 0 < epsilon -> exists A : Real,
      forall a b c : Nat, IsABCTriple a b c ->
        Height.logHeight₁ (abcRationalPoint a c) <=
          (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A :=
  abcEntry_heightBound I.bridge

theorem stepxi_bridge_ABC (I : StepXIBridgeInput) : ABCConjecture :=
  abcEntry_abcConjecture I.bridge

end LeanFormal.IUT.XiFPaper.Mzk1StepXIS1902BridgeActual

end
