import tmp.sheaf.xif.paper.Mzk1StepXIS1902BridgeActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi LANA bridge audit with explicit Fintype instance

Audit of the stepxi concrete bridge in the S1902/Fintype setting; no LANA olean
dependency. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXILanaBridgeAuditFintypeActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCEntryQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIS1902BridgeActual

theorem stepxi_lana_bridge_heightBound (I : StepXIBridgeInput) :
    ∀ ε : Real, 0 < ε → ∃ A : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) <=
          (1 + ε) * arithmeticWeight (abcRationalPoint a c) + A :=
  stepxi_bridge_heightBound I

theorem stepxi_lana_bridge_ABC (I : StepXIBridgeInput) : ABCConjecture :=
  stepxi_bridge_ABC I

end LeanFormal.IUT.XiFPaper.Mzk1StepXILanaBridgeAuditFintypeActual

end
