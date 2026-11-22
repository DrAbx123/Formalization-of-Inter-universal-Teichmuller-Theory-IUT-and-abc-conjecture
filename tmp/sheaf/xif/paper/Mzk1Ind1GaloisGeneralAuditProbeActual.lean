/- Read-only probes for general Galois integral action inhabitants (abc) -/
import tmp.sheaf.xif.paper.Mzk1Ind1GaloisIntegralGeneralActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1Ind1GaloisIntegralGeneralActual

open LeanFormal.IUT.XiFPaper.Mzk1Ind1IntegrationActionActual
open LeanFormal.IUT.XiFPaper.Mzk1Ind1ActualSourceUnitLayerActual
open LeanFormal.IUT.XiFPaper.Mzk1Ind1GaloisIntegralGeneralActual

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem audit_generalStableAction_nonempty : Nonempty (IntegralUnitStableAlgebraicAction K) :=
  ⟨localStableAlgebraicAction (1 : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)⟩

theorem audit_generalActualInd1Action_nonempty : Nonempty (ActualInd1UnitAction K) :=
  ⟨localActualInd1UnitAction (1 : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)⟩

end LeanFormal.IUT.XiFPaper.Mzk1Ind1GaloisIntegralGeneralActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1Ind1GaloisIntegralGeneralActual.localStableAlgebraicAction
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Ind1GaloisIntegralGeneralActual.localActualInd1UnitAction
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Ind1GaloisIntegralGeneralActual.audit_generalStableAction_nonempty
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Ind1GaloisIntegralGeneralActual.audit_generalActualInd1Action_nonempty