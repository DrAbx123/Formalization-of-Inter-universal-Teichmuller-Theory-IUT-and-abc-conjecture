import tmp.sheaf.xif.paper.Mzk1IUTIVSec1Sec2GapActual
import LeanFormal.IUT.IUTIV.Estimates.ArithmeticDivisorDegree

/-!
# Mzk1IUTIVReuseIndexActual — cross-region reuse index built on EXISTING repo assets
(Lead A475: exhaustive-search reuse; no duplicated theory, no gap described as a
mathematical breakthrough)

EXISTING assets found by exhaustive search (see coord/SURVEY-qpilot.md §3):
* tmp/sheaf/xif/paper/Mzk1IUTIVSec1Sec2GapActual.lean — IUT IV §1->§2 gap bundle with
  olean/EXIT0 (imported here, declarations re-used);
* tmp/sheaf/xif/paper/Mzk1IUT4Sec2InterfaceActual.lean, Mzk1SchemeSideMapsActual.lean,
  Mzk1R9AuditConsumerBundleActual.lean, Mzk1H7Ob9InterfaceActual.lean,
  Mzk1ProblemDApplicabilityActual.lean — existing interfaces for the same target nodes
  (not re-imported here because their oleans are not present at this revision; they are
  recorded as reuse anchors, not duplicated).

WHAT THIS FILE DOES: re-uses the existing IUT IV §1->§2 gap declarations and records the
cross-region reuse table (stepxi/stage4/iutiii target node -> existing asset). No paper
statement is proved or newly assumed.
No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1IUTIVReuseIndexActual

open LeanFormal.IUT.XiFPaper.Mzk1IUTIVSec1Sec2GapActual

/-- Re-export of the existing IUT IV §1->§2 gap bundle (reuse, not redefinition). -/
abbrev IUTIVGapBundle := IUTIVSec1Sec2Gap

/-- Re-export of the existing projection lemma. -/
theorem iutivGap_bridge_of {d e b : Prop} (g : IUTIVGapBundle d e b) :
    Sec1ToSec2Bridge b :=
  IUTIVSec1Sec2Gap.bridge_of g

/-- Cross-region reuse table: (target DAG node, existing repo asset, status). -/
def crossRegionReuseRows : List (String × String × String) :=
  [ ("iutiv:GAP.sec1_to_sec2 / iut-pre-stepxi:GAP.sec1_to_sec2", "Mzk1IUTIVSec1Sec2GapActual (EXIT0; imported/aliased here)", "REUSE (olean present)"),
    ("iutiv:Sec2 interface", "Mzk1IUT4Sec2InterfaceActual.lean (existing asset)", "REUSE (anchor; olean absent at this revision)"),
    ("iut-pre-stage4:D.gap.schemeSideMaps", "Mzk1SchemeSideMapsActual.lean (existing asset)", "REUSE (anchor; olean absent)"),
    ("iutiii:IUTIII.HULL.R9.AUDIT_CONSUMER", "Mzk1R9AuditConsumerBundleActual.lean (existing asset)", "REUSE (anchor; olean absent)"),
    ("iutiii:IUTIII.HULL.H7.OB9.BUNDLE", "Mzk1H7Ob9InterfaceActual.lean / Mzk1H7Ob9BundleStubConsumerActual.lean", "REUSE (anchor; olean absent)"),
    ("iut-pre-stage4:D.gap.problemDApplicability", "Mzk1ProblemDApplicabilityActual.lean (existing asset, currently EXIT1)", "REUSE-MINIMALLY (existing red file; not duplicated here)") ]

/-- The reuse table has six rows. -/
theorem crossRegionReuseRows_length : crossRegionReuseRows.length = 6 := rfl

#check IUTIVGapBundle
#check iutivGap_bridge_of
#check crossRegionReuseRows_length

end LeanFormal.IUT.XiFPaper.Mzk1IUTIVReuseIndexActual
end
