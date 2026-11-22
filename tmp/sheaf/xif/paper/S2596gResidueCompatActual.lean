import tmp.sheaf.xif.paper.S2596fSmulUActual
import tmp.sheaf.xif.paper.S2595LResidueEquivActual
noncomputable section
set_option autoImplicit false
open Polynomial NumberField
namespace LeanFormal.IUT.XiFPaper.S2596gResidueCompatActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2594LP0PActual
open LeanFormal.IUT.XiFPaper.S2595LResidueEquivActual
open LeanFormal.IUT.XiFPaper.S2592GenericLocalizedResidueIsoActual
open LeanFormal.IUT.XiFPaper.S2587LocalizedResidueDataActual
open LeanFormal.IUT.XiFPaper.S2596eSigmaEquivHomActual
open LeanFormal.IUT.XiFPaper.S2596dHfixActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
local instance : MulSemiringAction Gal(S2057FiveDivisionField/S1720Field) S2594LP0PActual.OL :=
  IsIntegralClosure.MulSemiringAction (RingOfIntegers S1720Field) S1720Field S2057FiveDivisionField (RingOfIntegers S2057FiveDivisionField)
lemma S2595LResidueEquiv_mk_algebraMap
    (D : S2587LocalizedResidueDataS)
    (h613 : (algebraMap ℤ S) (613 : ℤ) ∈ D.p) (b : S2594LP0PActual.OL) :
    S2595LResidueEquivActual.S2595LResidueEquiv D h613 (Ideal.Quotient.mk (S2595P0 D h613) b) =
      Ideal.Quotient.mk (S2594P (S2595P0 D h613)) (algebraMap S2594LP0PActual.OL S2594LP0PActual.T b) := by
  unfold S2595LResidueEquivActual.S2595LResidueEquiv S2594LP0PActual.S2594LResidueEquiv
  unfold localizedResidueEquiv
  simp [Ideal.quotientMap_mk]
lemma S2595LResidueEquiv_sigma
    (D : S2587LocalizedResidueDataS)
    (h613 : (algebraMap ℤ S) (613 : ℤ) ∈ D.p)
    (sigma : Gal(S2057FiveDivisionField/S1720Field)) (b : S2594LP0PActual.OL) :
    S2595LResidueEquivActual.S2595LResidueEquiv D h613
        (Ideal.Quotient.mk (S2595P0 D h613) (eSigma sigma b)) =
      Ideal.Quotient.mk (S2594P (S2595P0 D h613))
        (sigmaRingEquiv sigma (algebraMap S2594LP0PActual.OL S2594LP0PActual.T b)) := by
  rw [sigmaRingEquiv_apply_algebraMap]
  exact S2595LResidueEquiv_mk_algebraMap D h613 (eSigma sigma b)
#print axioms S2595LResidueEquiv_mk_algebraMap
#print axioms S2595LResidueEquiv_sigma
end LeanFormal.IUT.XiFPaper.S2596gResidueCompatActual
end
