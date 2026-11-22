import tmp.sheaf.xif.paper.Mzk1Prop58iiDiagramActual
import tmp.sheaf.xif.paper.Mzk1P58iiDiagramRowsActual
import tmp.sheaf.xif.paper.Mzk1P58iiVertexArrowsActual
import tmp.sheaf.xif.paper.Mzk1P58iiBridgeRowsActual
import tmp.sheaf.xif.paper.Mzk1P58iiCMLFActual
import tmp.sheaf.xif.paper.Mzk1LogShellThetaCarrierCompatActualAdapted

/-!
# Mzk1Prop58iiPhaseAggregationActualAdapted (adapted copy, A475 reuse) — Prop 5.8(ii) phase aggregation over the concrete
Gamma^x_non model assets

STEP 0 prior-art: Mzk1Prop58iiDiagramActual, Mzk1P58iiDiagramRowsActual, 
Mzk1P58iiVertexArrowsActual, Mzk1P58iiBridgeRowsActual, Mzk1P58iiCMLFActual,
Mzk1LogShellThetaCarrierCompatActualAdapted -> REUSE; this file aggregates the phase rows and
counts/linkage; the paper Gamma^x_non diagram and CMLF categories remain NAMED.
No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Prop58iiPhaseAggregationActualAdapted

open LeanFormal.IUT.XiFPaper.Mzk1Prop58iiDiagramActual
open LeanFormal.IUT.XiFPaper.Mzk1P58iiDiagramRowsActual
open LeanFormal.IUT.XiFPaper.Mzk1P58iiVertexArrowsActual
open LeanFormal.IUT.XiFPaper.Mzk1P58iiBridgeRowsActual
open LeanFormal.IUT.XiFPaper.Mzk1P58iiCMLFActual
open LeanFormal.IUT.XiFPaper.Mzk1LogShellThetaCarrierCompatActualAdapted

/-- Prop 5.8(ii) phase rows: (phase, formal asset, status). -/
def prop58iiPhaseRows : List (String × String × String) :=
  [ ("diagram skeleton / model vertices", "NonDiagramModel/Prop58iiDiagramObject (P58)", "CONSTRUCTED"),
    ("vertex image descriptions", "diagramVertexRows (P58IDR)", "PROVED"),
    ("vertex/arrow typed model", "vertexArrowRows (P58VA)", "PROVED"),
    ("bridge consequence edges", "bridgeDiagramRows (P58BR)", "PROVED under bridge h"),
    ("concrete CMLF model morphisms", "CMLFHom id/comp (CMLF)", "CONSTRUCTED"),
    ("log-shell/theta carrier compatibility", "CMLFCarrierHom image theorems (CMLF2)", "PROVED (model level)"),
    ("Gamma^x_non diagram (paper)", "Prop58iiDiagramInput (explicit named hypothesis)", "NAMED"),
    ("paper CMLF_TS categories", "not constructed", "NAMED") ]

/-- The phase row record has eight rows. -/
theorem prop58iiPhaseRows_length : prop58iiPhaseRows.length = 8 := rfl

/-- The diagram-vertex row count is five (re-exported). -/
theorem prop58iiPhaseRows_vertex_count : diagramVertexRows.length = 5 :=
  diagramVertexRows_length

/-- The vertex/arrow row count is six (re-exported). -/
theorem prop58iiPhaseRows_arrow_count : vertexArrowRows.length = 6 :=
  vertexArrowRows_length

/-- The bridge row count is five (re-exported). -/
theorem prop58iiPhaseRows_bridge_count : bridgeDiagramRows.length = 5 :=
  bridgeDiagramRows_length

#check prop58iiPhaseRows
#check prop58iiPhaseRows_length
#check prop58iiPhaseRows_vertex_count
#check prop58iiPhaseRows_arrow_count
#check prop58iiPhaseRows_bridge_count

end LeanFormal.IUT.XiFPaper.Mzk1Prop58iiPhaseAggregationActualAdapted
end
