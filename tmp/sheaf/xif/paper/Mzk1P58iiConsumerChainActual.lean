import tmp.sheaf.xif.paper.Mzk1Prop58iiDiagramActual
import tmp.sheaf.xif.paper.Mzk1P58iiDiagramRowsActual
import tmp.sheaf.xif.paper.Mzk1P58iiVertexArrowsActual
import tmp.sheaf.xif.paper.Mzk1P58iiBridgeRowsActual

/-!
# Mzk1P58iiConsumerChainActual — consumer theorems for Prop 5.8(ii) Gamma^x_non model
assets (P58/P58IDR/P58VA/P58BR, all EXIT0). Composed projections only; no axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1P58iiConsumerChainActual

open LeanFormal.IUT
open LeanFormal.IUT.SourceLogShellDatum
open LeanFormal.IUT.XiFPaper.Mzk1Prop58iiDiagramActual
open LeanFormal.IUT.XiFPaper.Mzk1P58iiDiagramRowsActual
open LeanFormal.IUT.XiFPaper.Mzk1P58iiVertexArrowsActual
open LeanFormal.IUT.XiFPaper.Mzk1P58iiBridgeRowsActual

universe u

/-- Consumer: the concrete NonDiagramModel is inhabited (P58). -/
theorem consumer_nonDiagramModel_nonempty (D : SourceLogShellDatum.{u}) :
    Nonempty (NonDiagramModel D) :=
  nonDiagramModel_nonempty D

/-- Consumer: the unit-layer image vertex is the exact log-image of units (P58IDR). -/
theorem consumer_unitImage (D : SourceLogShellDatum.{u}) :
    (nonDiagramModel D).unitImage =
      (fun u : D.Units => (D.logMap u).toAdd) '' (Set.univ : Set D.Units) :=
  nonDiagramModel_unitImage D

/-- Consumer: the diagram's invariant-image arrow is contained in the unit image (P58VA). -/
theorem consumer_arrow (D : SourceLogShellDatum.{u}) :
    vertexSet D .invariantImage ⊆ vertexSet D .unitImage :=
  arrow_invariant_le_unit D

/-- Consumer: under the bridge hypothesis the log-shell vertex equals the inv-scaled one
(P58BR). -/
theorem consumer_bridge_logShell (D : SourceLogShellDatum.{u})
    (h : SourceLogShellInvariantImageIdentification D) :
    vertexSet D .logShell = vertexSet D .invScaledUnitImage :=
  arrow_logShell_eq_invScaled D h

#check consumer_nonDiagramModel_nonempty
#check consumer_unitImage
#check consumer_arrow
#check consumer_bridge_logShell

end LeanFormal.IUT.XiFPaper.Mzk1P58iiConsumerChainActual
end
