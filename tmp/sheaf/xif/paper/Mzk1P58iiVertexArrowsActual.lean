import tmp.sheaf.xif.paper.Mzk1Prop58iiDiagramActual
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellAbsTopIIIBridge

/-!
# Mzk1P58iiVertexArrowsActual — the Gamma^x_non diagram model vertices and their arrows,
typed

STEP 0 prior-art: Mzk1Prop58iiDiagramActual (NonDiagramModel vertices),
SourceLogShellAbsTopIIIBridge (bridge consequences) -> REUSE; this file gives the vertex
type, the vertex-set assignment and the diagram arrows as named propositions.

No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1P58iiVertexArrowsActual

open LeanFormal.IUT
open LeanFormal.IUT.SourceLogShellDatum
open LeanFormal.IUT.XiFPaper.Mzk1Prop58iiDiagramActual

universe u

/-- The four modeled vertices of the Gamma^x_non diagram: unit image, invariant image,
log-shell, and the concrete (p*)^-1-scaled unit image. -/
inductive NonDiagramVertex
  | unitImage
  | invariantImage
  | logShell
  | invScaledUnitImage
  deriving DecidableEq, Fintype

/-- The vertex-set assignment of the diagram model. -/
def vertexSet (D : SourceLogShellDatum.{u}) : NonDiagramVertex → Set D.K
  | .unitImage => D.unitLayer
  | .invariantImage => D.preLogShell
  | .logShell => D.logShell
  | .invScaledUnitImage => D.invScaledUnitLayer

/-- Arrow: the invariant image is contained in the unit image. -/
theorem arrow_invariant_le_unit (D : SourceLogShellDatum.{u}) :
    vertexSet D .invariantImage ⊆ vertexSet D .unitImage :=
  (nonDiagramModel D).preLogShell_le_unitLayer

/-- Arrow: the unit image is contained in the log-shell, under the bridge hypothesis. -/
theorem arrow_unit_le_logShell (D : SourceLogShellDatum.{u})
    (h : SourceLogShellInvariantImageIdentification D) :
    vertexSet D .unitImage ⊆ vertexSet D .logShell :=
  D.codomainKummerContained_of_invariantImageIdentification h

/-- Arrow: the log-shell equals the concrete (p*)^-1-scaled unit image, under the bridge
hypothesis. -/
theorem arrow_logShell_eq_invScaled (D : SourceLogShellDatum.{u})
    (h : SourceLogShellInvariantImageIdentification D) :
    vertexSet D .logShell = vertexSet D .invScaledUnitImage :=
  D.logShell_eq_invScaledUnitLayer_of_invariantImageIdentification h

/-- The vertex type has exactly four vertices. -/
theorem nonDiagramVertex_card :
    Fintype.card NonDiagramVertex = 4 := by
  decide

/-- Vertex/arrow rows: (item, declaration, status). -/
def vertexArrowRows : List (String × String × String) :=
  [ ("four modeled vertices", "NonDiagramVertex + vertexSet", "CONSTRUCTED"),
    ("invariant image -> unit image arrow", "arrow_invariant_le_unit", "PROVED"),
    ("unit image -> log-shell arrow (bridge h)", "arrow_unit_le_logShell", "PROVED under h"),
    ("log-shell = (p*)^-1 unit image (bridge h)", "arrow_logShell_eq_invScaled", "PROVED under h"),
    ("vertex count", "nonDiagramVertex_card", "PROVED"),
    ("Gamma^x_non diagram in CMLF (paper)", "not constructed", "NAMED") ]

/-- The vertex/arrow row record has six rows. -/
theorem vertexArrowRows_length : vertexArrowRows.length = 6 := rfl

#check NonDiagramVertex
#check vertexSet
#check arrow_invariant_le_unit
#check arrow_unit_le_logShell
#check arrow_logShell_eq_invScaled
#check nonDiagramVertex_card
#check vertexArrowRows_length

end LeanFormal.IUT.XiFPaper.Mzk1P58iiVertexArrowsActual
end
