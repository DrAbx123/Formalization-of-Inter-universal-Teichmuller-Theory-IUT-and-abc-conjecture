import tmp.sheaf.xif.paper.Mzk1Prop58iiDiagramDerivedActual
import tmp.sheaf.xif.paper.Mzk1P58iiVertexArrowsActual

/-!
# Mzk1P58iiDiagramChainActual — derived inclusion chain of the Gamma^x_non diagram vertices
under the invariant-image bridge (new theorems; no copies/bookkeeping). No axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1P58iiDiagramChainActual

open LeanFormal.IUT
open LeanFormal.IUT.SourceLogShellDatum
open LeanFormal.IUT.XiFPaper.Mzk1Prop58iiDiagramDerivedActual
open LeanFormal.IUT.XiFPaper.Mzk1P58iiVertexArrowsActual

universe u

/-- Derived: the invariant-image vertex is inside the unit-image vertex. -/
theorem chain_invariant_le_unit (D : SourceLogShellDatum.{u}) :
    vertexSet D .invariantImage ⊆ vertexSet D .unitImage :=
  Mzk1Prop58iiDiagramDerivedActual.diagram_invariantImage_subset_unitImage D

/-- Derived: under the bridge, the unit-image vertex is inside the log-shell vertex. -/
theorem chain_unit_le_logShell (D : SourceLogShellDatum.{u})
    (h : SourceLogShellInvariantImageIdentification D) :
    vertexSet D .unitImage ⊆ vertexSet D .logShell :=
  arrow_unit_le_logShell D h

/-- Derived: under the bridge, the invariant-image vertex is inside the log-shell vertex
(composition of the two arrows). -/
theorem chain_invariant_le_logShell (D : SourceLogShellDatum.{u})
    (h : SourceLogShellInvariantImageIdentification D) :
    vertexSet D .invariantImage ⊆ vertexSet D .logShell :=
  fun _ ha => chain_unit_le_logShell D h (chain_invariant_le_unit D ha)

/-- Derived: under the bridge, the log-shell vertex equals the inv-scaled unit vertex. -/
theorem chain_logShell_eq_invScaled (D : SourceLogShellDatum.{u})
    (h : SourceLogShellInvariantImageIdentification D) :
    vertexSet D .logShell = vertexSet D .invScaledUnitImage :=
  arrow_logShell_eq_invScaled D h

/-- Derived: under the bridge, the invariant-image vertex is inside the inv-scaled unit
vertex. -/
theorem chain_invariant_le_invScaled (D : SourceLogShellDatum.{u})
    (h : SourceLogShellInvariantImageIdentification D) :
    vertexSet D .invariantImage ⊆ vertexSet D .invScaledUnitImage := by
  rw [← chain_logShell_eq_invScaled D h]
  exact chain_invariant_le_logShell D h

#check chain_invariant_le_unit
#check chain_unit_le_logShell
#check chain_invariant_le_logShell
#check chain_logShell_eq_invScaled
#check chain_invariant_le_invScaled

end LeanFormal.IUT.XiFPaper.Mzk1P58iiDiagramChainActual
end
