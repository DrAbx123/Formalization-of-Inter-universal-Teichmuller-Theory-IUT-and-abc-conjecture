import tmp.sheaf.xif.paper.S2543CorrectedQuotMapActual
import tmp.sheaf.xif.paper.S2542FunctorFaithfulActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2540CorrectedObjectMapActual
open LeanFormal.IUT.XiFPaper.S2543CorrectedQuotMapActual
open LeanFormal.IUT.XiFPaper.S2542FunctorFaithfulActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual

namespace LeanFormal.IUT.XiFPaper.S2545CorrectedQuotInjectiveActual

theorem S2545QuotMapR_injective
    {A B : CommAlgCat.FiniteEtale S2482CoordinateRing} :
    Function.Injective (S2543QuotMapR (A := A) (B := B)) := by
  intro f g h
  have h' : S2540Functor.map (Quiver.Hom.op f) =
      S2540Functor.map (Quiver.Hom.op g) := h
  have hop : Quiver.Hom.op f = Quiver.Hom.op g :=
    S2542Functor_faithful.map_injective h'
  exact Quiver.Hom.op_inj hop

#check S2545QuotMapR_injective
#print axioms S2545QuotMapR_injective
end LeanFormal.IUT.XiFPaper.S2545CorrectedQuotInjectiveActual
end