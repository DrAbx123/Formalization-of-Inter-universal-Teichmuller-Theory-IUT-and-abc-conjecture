import tmp.sheaf.xif.paper.S2591LocalizedResidueEquivActual
import tmp.sheaf.xif.paper.S2596gResidueCompatActual
noncomputable section
set_option autoImplicit false
open Polynomial NumberField
namespace LeanFormal.IUT.XiFPaper.S2596hQuotientCardActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2587LocalizedResidueDataActual
open LeanFormal.IUT.XiFPaper.S2591LocalizedResidueEquivActual
open LeanFormal.IUT.XiFPaper.S2590LocalizedPrimeContractionActual
lemma localized_quotient_card (D : S2587LocalizedResidueDataS)
    (h613 : (algebraMap ℤ S2565ConcreteIntegralClosureCActual.S) (613 : ℤ) ∈ D.p) :
    Nat.card (S2565ConcreteIntegralClosureCActual.S ⧸ D.p) =
      Nat.card (S2565ConcreteIntegralClosureCActual.C ⧸ D.p.comap (algebraMap S2565ConcreteIntegralClosureCActual.C S2565ConcreteIntegralClosureCActual.S)) :=
  Nat.card_congr (S2591_localized_residue_equiv D h613).symm.toEquiv
#print axioms localized_quotient_card
end LeanFormal.IUT.XiFPaper.S2596hQuotientCardActual
end
