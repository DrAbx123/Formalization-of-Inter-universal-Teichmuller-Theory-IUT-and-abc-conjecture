/- Read-only axiom probes for Ind1 Galois integral action inhabitant (abc) -/
import tmp.sheaf.xif.paper.Mzk1Ind1GaloisIntegralActionActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1Ind1GaloisIntegralActionActual

open LeanFormal.IUT.XiFPaper.Mzk1Ind1IntegrationActionActual
open LeanFormal.IUT.XiFPaper.Mzk1Ind1ActualSourceUnitLayerActual
open LeanFormal.IUT.XiFPaper.Mzk1Ind1GaloisIntegralActionActual

theorem audit_actualStableAction_nonempty {p : Nat} [Fact p.Prime] :
    Nonempty (IntegralUnitStableAlgebraicAction ℚ_[p]) :=
  ⟨localGaloisStableAlgebraicAction (p := p) (1 : LeanFormal.IUT.LocalAbsoluteGalois p)⟩

theorem audit_actualInd1Action_nonempty {p : Nat} [Fact p.Prime] :
    Nonempty (ActualInd1UnitAction ℚ_[p]) :=
  ⟨localGaloisActualInd1UnitAction (p := p) (1 : LeanFormal.IUT.LocalAbsoluteGalois p)⟩

end LeanFormal.IUT.XiFPaper.Mzk1Ind1GaloisIntegralActionActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1Ind1GaloisIntegralActionActual.localGaloisStableAlgebraicAction
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Ind1GaloisIntegralActionActual.localGaloisActualInd1UnitAction
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Ind1GaloisIntegralActionActual.audit_actualStableAction_nonempty
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Ind1GaloisIntegralActionActual.audit_actualInd1Action_nonempty