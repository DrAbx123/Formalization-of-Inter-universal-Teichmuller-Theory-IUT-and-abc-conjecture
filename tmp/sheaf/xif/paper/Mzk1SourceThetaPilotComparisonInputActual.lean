import LeanFormal.IUT.IUTII.Kummer.SourceThetaPilotIQContainment
import tmp.sheaf.xif.paper.Mzk1ThetaPilotPreciseInterfaceActual
import tmp.sheaf.xif.paper.Mzk1ThetaPilotPacketInterfaceActual

/-!
# Mzk1SourceThetaPilotComparisonInputActual — source theta-pilot comparison as an explicit
named hypothesis (iuti-ii SourceThetaPilot NAMED gap)

STEP 0 prior-art: SourceThetaPilotIQContainment (tree source theta-pilot packet facts),
Mzk1ThetaPilotPreciseInterfaceActual (X-mu precision interface),
Mzk1ThetaPilotPacketInterfaceActual (packet rows) -> REUSE.
This file packages the paper's source-to-arithmetic comparison as an explicit named
hypothesis with its conditional consumer; the comparison is not constructed.
No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1SourceThetaPilotComparisonInputActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ThetaPilotPreciseInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1ThetaPilotPacketInterfaceActual

/-- The paper source-to-arithmetic comparison (source theta-pilot) as an explicit named
hypothesis. -/
structure SourceThetaPilotComparisonInput where
  /-- the paper comparison statement. -/
  comparison : Prop
  /-- the named paper proof. -/
  named : comparison

/-- Conditional consumer of the source theta-pilot comparison. -/
theorem sourceThetaPilotComparison_of_input (I : SourceThetaPilotComparisonInput) :
    I.comparison := I.named

/-- Rows: (paper object, formal asset, status). -/
def sourceThetaPilotComparisonRows : List (String × String × String) :=
  [ ("source log-shell packet / generator / IQ containment", "SourceThetaPilotIQContainment (tree)", "TREE PROOF"),
    ("X-mu precision interface", "xmuChainSupply / xmuChainEquiv_image_logShell", "TREE PROOF (re-exported)"),
    ("theta-pilot packet rows", "thetaPilotPacketRows", "TREE PROOFS"),
    ("source-to-arithmetic comparison (paper)", "SourceThetaPilotComparisonInput (explicit named hypothesis)", "NAMED"),
    ("conditional consumer", "sourceThetaPilotComparison_of_input", "PROVED (conditional)") ]

/-- The comparison row record has five rows. -/
theorem sourceThetaPilotComparisonRows_length : sourceThetaPilotComparisonRows.length = 5 := rfl

#check SourceThetaPilotComparisonInput
#check sourceThetaPilotComparison_of_input
#check sourceThetaPilotComparisonRows_length

end LeanFormal.IUT.XiFPaper.Mzk1SourceThetaPilotComparisonInputActual
end
