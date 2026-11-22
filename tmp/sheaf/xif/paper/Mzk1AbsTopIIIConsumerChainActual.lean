import tmp.sheaf.xif.paper.Mzk1AbsTopIII05DeepInputsRefinedActual
import tmp.sheaf.xif.paper.Mzk1Prop58iTargetActual
import tmp.sheaf.xif.paper.Mzk1Prop58iiDiagramActual

/-!
# Mzk1AbsTopIIIConsumerChainActual — consumer theorems for AbsTopIII05 concrete/refined
assets (A3R/P58IT/P58, all EXIT0). Composed projections only; no axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1AbsTopIIIConsumerChainActual

open LeanFormal.IUT
open LeanFormal.IUT.SourceLogShellDatum
open LeanFormal.IUT.XiFPaper.Mzk1AbsTopIII05DeepInputsRefinedActual
open LeanFormal.IUT.XiFPaper.Mzk1Prop58iTargetActual
open LeanFormal.IUT.XiFPaper.Mzk1Prop58iiDiagramActual

universe u

/-- Consumer: refinement anchors have four rows (A3R). -/
theorem consumer_refined_anchors_length : refinedAnchors.length = 4 :=
  refinedAnchors_length

/-- Consumer: the four deep-input kinds are exactly the refinement kinds (A3R). -/
theorem consumer_kinds_eq :
    absTopIIIDeepInputs.map (fun d => d.kind) =
      [.prop58i, .prop58ii, .cor55, .orientedGraph] :=
  absTopIIIDeepInputs_kinds_eq_refined

/-- Consumer: target implies the log-shell identification (P58IT). -/
theorem consumer_target_logShell (D : SourceLogShellDatum.{u})
    (h : prop58iReconstructionTarget D) : D.logShell = D.invScaledUnitLayer :=
  target_implies_logShell_eq D h

/-- Consumer: the concrete diagram model is inhabited (P58). -/
theorem consumer_diagramModel (D : SourceLogShellDatum.{u}) :
    Nonempty (NonDiagramModel D) :=
  nonDiagramModel_nonempty D

#check consumer_refined_anchors_length
#check consumer_kinds_eq
#check consumer_target_logShell
#check consumer_diagramModel

end LeanFormal.IUT.XiFPaper.Mzk1AbsTopIIIConsumerChainActual
end
