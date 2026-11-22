import tmp.sheaf.xif.paper.Mzk1Prop58iiDiagramActual
import tmp.sheaf.xif.paper.Mzk1P58iiVertexArrowsActual

/-!
# Mzk1Prop58iiDiagramInputActual — Gamma^x_non diagram as an explicit named hypothesis,
with the concrete NonDiagramModel anchors

STEP 0 prior-art: Mzk1Prop58iiDiagramActual (CMLFCarrier/NonDiagramModel/Prop58iiNamedInput),
Mzk1P58iiVertexArrowsActual (vertex/arrow model) -> REUSE.
This file packages the paper's Gamma^x_non diagram as an explicit named hypothesis and gives
its conditional consumer, together with the concrete model nonemptiness; the diagram itself
is not constructed.
No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Prop58iiDiagramInputActual

open LeanFormal.IUT
open LeanFormal.IUT.SourceLogShellDatum
open LeanFormal.IUT.XiFPaper.Mzk1Prop58iiDiagramActual
open LeanFormal.IUT.XiFPaper.Mzk1P58iiVertexArrowsActual

universe u

/-- The Gamma^x_non diagram (Prop 5.8(ii)) as an explicit named hypothesis. -/
structure Prop58iiDiagramInput where
  /-- the paper Gamma^x_non diagram statement. -/
  gammaXNon : Prop
  /-- the named paper proof. -/
  named : gammaXNon

/-- Conditional consumer of the Gamma^x_non diagram input. -/
theorem prop58iiDiagram_of_input (I : Prop58iiDiagramInput) : I.gammaXNon := I.named

/-- The concrete NonDiagramModel is inhabited for every source log-shell datum. -/
theorem nonDiagramModel_nonempty (D : SourceLogShellDatum.{u}) :
    Nonempty (NonDiagramModel D) :=
  ⟨nonDiagramModel D⟩

/-- Rows: (item, formal asset, status). -/
def prop58iiDiagramInputRows : List (String × String × String) :=
  [ ("Gamma^x_non diagram (paper)", "Prop58iiDiagramInput (explicit named hypothesis)", "NAMED"),
    ("concrete NonDiagramModel", "nonDiagramModel; nonDiagramModel_nonempty", "CONSTRUCTED/INHABITED"),
    ("diagram vertices/arrows model", "NonDiagramVertex/vertexSet + arrow theorems", "CONSTRUCTED/PROVED"),
    ("paper CMLF_TS categories", "not constructed", "NAMED") ]

/-- The diagram-input row record has four rows. -/
theorem prop58iiDiagramInputRows_length : prop58iiDiagramInputRows.length = 4 := rfl

#check Prop58iiDiagramInput
#check prop58iiDiagram_of_input
#check nonDiagramModel_nonempty
#check prop58iiDiagramInputRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Prop58iiDiagramInputActual
end
