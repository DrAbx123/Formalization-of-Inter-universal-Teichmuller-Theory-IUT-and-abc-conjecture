import tmp.sheaf.xif.paper.Mzk1P58iiVertexArrowsActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1P58iiVertexArrowsConsumerActual — P58ii vertex/arrow consumer

Reuses the EXIT0 P58ii vertex-arrow model (four vertices, three containment/equality
arrows, vertex count) as a named bundle with projections.  No new math; no closure;
gate NOT PASSED; registry 14041; no registry edits. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1P58iiVertexArrowsConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1P58iiVertexArrowsActual

universe u

theorem p58ii_invariant_le_unit_consumer (D : SourceLogShellDatum.{u}) :
    vertexSet D .invariantImage ⊆ vertexSet D .unitImage :=
  arrow_invariant_le_unit D

theorem p58ii_unit_le_logShell_consumer (D : SourceLogShellDatum.{u})
    (h : SourceLogShellInvariantImageIdentification D) :
    vertexSet D .unitImage ⊆ vertexSet D .logShell :=
  arrow_unit_le_logShell D h

theorem p58ii_logShell_eq_invScaled_consumer (D : SourceLogShellDatum.{u})
    (h : SourceLogShellInvariantImageIdentification D) :
    vertexSet D .logShell = vertexSet D .invScaledUnitImage :=
  arrow_logShell_eq_invScaled D h

theorem p58ii_vertex_card_consumer : Fintype.card NonDiagramVertex = 4 :=
  nonDiagramVertex_card

def p58iiVertexConsumerRows : List (String × String × String) :=
  [ ("invariant->unit arrow", "p58ii_invariant_le_unit_consumer", "PROVED (reuse)"),
    ("unit->logShell arrow", "p58ii_unit_le_logShell_consumer", "PROVED under bridge h"),
    ("logShell=invScaled", "p58ii_logShell_eq_invScaled_consumer", "PROVED under bridge h"),
    ("vertex count", "p58ii_vertex_card_consumer", "PROVED (reuse)"),
    ("scope", "no new math; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem p58iiVertexConsumerRows_length : p58iiVertexConsumerRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P58iiVertexArrowsConsumerActual

end
