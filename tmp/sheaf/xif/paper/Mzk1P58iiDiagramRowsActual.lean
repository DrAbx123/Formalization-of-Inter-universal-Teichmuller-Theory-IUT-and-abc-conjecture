import tmp.sheaf.xif.paper.Mzk1Prop58iiDiagramActual
import tmp.sheaf.xif.paper.Mzk1Prop58iImagesActual

/-!
# Mzk1P58iiDiagramRowsActual — exact image descriptions of the Gamma^x_non diagram model
vertices

STEP 0 prior-art: Mzk1Prop58iiDiagramActual (CMLFCarrier/NonDiagramModel/Prop58iiDiagramObject),
Mzk1Prop58iImagesActual (exact set descriptions of preLogShell/unitLayer/logShell) -> REUSE;
this file identifies the concrete NonDiagramModel vertex sets with those exact image
descriptions.

No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1P58iiDiagramRowsActual

open LeanFormal.IUT
open LeanFormal.IUT.SourceLogShellDatum
open LeanFormal.IUT.XiFPaper.Mzk1Prop58iiDiagramActual
open LeanFormal.IUT.XiFPaper.Mzk1Prop58iImagesActual

universe u

/-- The diagram model's invariant-image vertex is exactly the log-image of the invariant
submonoid. -/
theorem nonDiagramModel_invariantImage (D : SourceLogShellDatum.{u}) :
    (nonDiagramModel D).invariantImage =
      (fun u : D.Units => (D.logMap u).toAdd) '' (D.invariants : Set D.Units) :=
  preLogShell_eq_image_invariants D

/-- The diagram model's unit-image vertex is exactly the log-image of all units. -/
theorem nonDiagramModel_unitImage (D : SourceLogShellDatum.{u}) :
    (nonDiagramModel D).unitImage =
      (fun u : D.Units => (D.logMap u).toAdd) '' (Set.univ : Set D.Units) :=
  unitLayer_eq_image_units D

/-- The diagram model's log-shell vertex is exactly the p*-inverse-scaled invariant image. -/
theorem nonDiagramModel_logShell (D : SourceLogShellDatum.{u}) :
    (nonDiagramModel D).logShellSet =
      {a : D.K | (D.pStar : D.K) * a ∈ D.preLogShell} :=
  logShell_eq_pStar_invScaled_preLogShell D

/-- The inclusion edge of the diagram model is the proved preLogShell ⊆ unitLayer. -/
theorem nonDiagramModel_inclusion (D : SourceLogShellDatum.{u}) :
    (nonDiagramModel D).invariantImage ⊆ (nonDiagramModel D).unitImage :=
  (nonDiagramModel D).preLogShell_le_unitLayer

/-- Diagram-vertex identification rows: (vertex, exact description, status). -/
def diagramVertexRows : List (String × String × String) :=
  [ ("invariant image vertex", "logMap '' invariants", "PROVED (nonDiagramModel_invariantImage)"),
    ("unit image vertex", "logMap '' univ", "PROVED (nonDiagramModel_unitImage)"),
    ("log-shell vertex", "{a | p* · a ∈ preLogShell}", "PROVED (nonDiagramModel_logShell)"),
    ("inclusion edge", "invariantImage ⊆ unitImage", "PROVED (nonDiagramModel_inclusion)"),
    ("Gamma^x_non diagram (paper)", "not constructed", "NAMED") ]

/-- The diagram-vertex row record has five rows. -/
theorem diagramVertexRows_length : diagramVertexRows.length = 5 := rfl

#check nonDiagramModel_invariantImage
#check nonDiagramModel_unitImage
#check nonDiagramModel_logShell
#check nonDiagramModel_inclusion
#check diagramVertexRows_length

end LeanFormal.IUT.XiFPaper.Mzk1P58iiDiagramRowsActual
end
