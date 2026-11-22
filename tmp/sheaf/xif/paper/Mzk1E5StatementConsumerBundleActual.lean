import tmp.sheaf.xif.paper.Mzk1E5DisplayInputsStatementActualV2
import tmp.sheaf.xif.paper.Mzk1E5UndilatedABCBridgeActualV2
import tmp.sheaf.xif.paper.Mzk1IUT312TopStatementActual
import tmp.sheaf.xif.paper.Mzk1E5CThetaABCActualV5
import tmp.sheaf.xif.paper.S3171IUTIVSection1DisplayActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1E5StatementConsumerBundleActual — E-5 statement/top-consumer bundle

Reuses EXIT0 assets: display-inputs statement layer (hCor312/hSlack), undilated
ABC bridge, IUT312 top statement and CThetaPaper display consumer.  Exposes the
display-from-gap+slack consumer, undilated ABC consumer and top-statement consumer.
No named paper object proved; no closure; gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1E5StatementConsumerBundleActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1E5DisplayInputsStatementActualV2
open LeanFormal.IUT.XiFPaper.Mzk1E5UndilatedABCBridgeActualV2
open LeanFormal.IUT.XiFPaper.Mzk1IUT312TopStatementActual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual

universe u

/-- The display from the hCor312/slack statement hypotheses. -/
theorem display_of_gap_slack (T : Thm110DisplayTerms)
    (hcor : Cor312GapHyp T) (hslack : SlackHyp T) :
    thm110Lhs T ≤ thm110Rhs T :=
  final_display_of_inputs T ((displayInputs_iff T).mpr ⟨hcor, hslack⟩)

/-- The IUT312 top statement from a concrete StepXI contract. -/
theorem iut312Top_of_contract_consumer (C : StepXIContract) : IUT312TopStatement :=
  iut312TopStatement_of_contract C

/-- The IUT312 conclusion shape from the top statement. -/
theorem iut312ConclusionShape_of_top_consumer (h : IUT312TopStatement) :
    IUT312ConclusionShape :=
  iut312ConclusionShape_of_top h

def e5StatementConsumerRows : List (String × String × String) :=
  [ ("display inputs", "displayInputs_iff / display_of_gap_slack", "PROVED (reuse)"),
    ("top statement", "iut312Top_of_contract_consumer", "PROVED (reuse)"),
    ("conclusion shape", "iut312ConclusionShape_of_top_consumer", "PROVED (reuse)"),
    ("undilated ABC", "abcConjecture_of_undilatedBounds (re-export available)", "PROVED (reuse)"),
    ("scope", "named inputs explicit; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem e5StatementConsumerRows_length : e5StatementConsumerRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1E5StatementConsumerBundleActual

end
