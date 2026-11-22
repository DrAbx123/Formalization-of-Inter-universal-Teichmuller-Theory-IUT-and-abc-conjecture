import tmp.sheaf.xif.paper.Mzk1IUTIVSec1Sec2GapActual

/-!
# Mzk1IUTIVStepXINamedInputsActual — IUT IV §1/§2 paper inputs routed through the EXISTING
Sec1Sec2 gap asset (Lead A475 reuse rule)

STEP 0 prior-art (EXISTING repo asset, not duplicated): tmp/sheaf/xif/paper/
Mzk1IUTIVSec1Sec2GapActual.lean (Sec1DisplayObligation, Sec2EstimateObligation,
Sec1ToSec2Bridge, IUTIVSec1Sec2Gap, IUTIVSec1Sec2Gap.bridge_of; olean/EXIT0 present).

WHAT THIS FILE DOES: routes the iut-pre-stepxi IUT IV §1->§2 paper inputs through the existing
gap bundle and gives the conditional projections; the paper propositions remain explicit
named hypotheses (inside the existing bundle), not newly assumed here.
No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1IUTIVStepXINamedInputsActual

open LeanFormal.IUT.XiFPaper.Mzk1IUTIVSec1Sec2GapActual

/-- IUT IV §1/§2 inputs routed through the existing gap bundle. -/
structure StepXISec1Sec2Input (d e b : Prop) where
  gap : IUTIVSec1Sec2Gap d e b

/-- Projection: Section 1 display obligation (existing asset). -/
theorem stepxi_sec1_display {d e b : Prop} (I : StepXISec1Sec2Input d e b) :
    Sec1DisplayObligation d := I.gap.display

/-- Projection: Section 2 estimate obligation (existing asset). -/
theorem stepxi_sec2_estimate {d e b : Prop} (I : StepXISec1Sec2Input d e b) :
    Sec2EstimateObligation e := I.gap.estimate

/-- Projection: Section 1 -> Section 2 bridge (existing asset). -/
theorem stepxi_sec1_to_sec2 {d e b : Prop} (I : StepXISec1Sec2Input d e b) :
    Sec1ToSec2Bridge b := IUTIVSec1Sec2Gap.bridge_of I.gap

/-- StepXI input rows: (stepxi DAG node, existing asset anchor, status). -/
def stepXINamedInputRows : List (String × String × String) :=
  [ ("S1.prop11 (tensor-packet ring structure)", "IUTIVSec1Sec2Gap display/estimate fields (existing asset)", "NAMED (via existing bundle)"),
    ("S1.prop12 (arithmetic estimate)", "IUTIVSec1Sec2Gap estimate field", "NAMED (via existing bundle)"),
    ("S1.prop14", "IUTIVSec1Sec2Gap fields", "NAMED (via existing bundle)"),
    ("S1.prop15", "IUTIVSec1Sec2Gap fields", "NAMED (via existing bundle)"),
    ("S1.prop18", "IUTIVSec1Sec2Gap fields", "NAMED (via existing bundle)"),
    ("S1.thm110actual (display)", "IUTIVSec1Sec2Gap display field", "NAMED (via existing bundle)"),
    ("S2.pnt", "IUTIVSec1Sec2Gap estimate field", "NAMED (via existing bundle)"),
    ("S2.arithmeticTransition / GAP.sec1_to_sec2", "IUTIVSec1Sec2Gap bridge field", "NAMED (via existing bundle)"),
    ("S1b.heightInput", "IUTIVSec1Sec2Gap estimate field (anchor)", "NAMED (via existing bundle)"),
    ("S1c.undilatedInput", "IUTIVSec1Sec2Gap estimate field (anchor)", "NAMED (via existing bundle)") ]

/-- The StepXI named-input row record has ten rows. -/
theorem stepXINamedInputRows_length : stepXINamedInputRows.length = 10 := rfl

#check StepXISec1Sec2Input
#check stepxi_sec1_display
#check stepxi_sec2_estimate
#check stepxi_sec1_to_sec2
#check stepXINamedInputRows_length

end LeanFormal.IUT.XiFPaper.Mzk1IUTIVStepXINamedInputsActual
end
