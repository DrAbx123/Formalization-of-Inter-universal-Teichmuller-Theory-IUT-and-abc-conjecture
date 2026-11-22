import tmp.sheaf.xif.paper.S2545CorrectedQuotInjectiveActual
import tmp.sheaf.xif.paper.S2542FunctorFaithfulActual
import tmp.sheaf.xif.paper._FullD3D4Agent

noncomputable section
open CategoryTheory
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2540CorrectedObjectMapActual
open LeanFormal.IUT.XiFPaper.S2543CorrectedQuotMapActual
open LeanFormal.IUT.XiFPaper.S2542FunctorFaithfulActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.FullD3D4Agent
open LeanFormal.IUT.XiFPaper.S2545CorrectedQuotInjectiveActual

namespace LeanFormal.IUT.XiFPaper.S2547CorrectedFullyFaithfulActual

theorem S2547QuotMapR_bijective
    {A B : CommAlgCat.FiniteEtale S2482CoordinateRing} :
    Function.Bijective (S2543QuotMapR (A := A) (B := B)) :=
  ⟨S2545QuotMapR_injective,
    FullD3D4Agent.S2543QuotMapRSurjective_holds (A := A) (B := B)⟩

noncomputable instance S2547Functor_full : S2540Functor.Full where
  map_surjective {X Y} h := by
    induction X using Opposite.rec with
    | op B =>
      induction Y using Opposite.rec with
      | op A =>
        obtain ⟨f, hf⟩ := FullD3D4Agent.S2543QuotMapRSurjective_holds
          (A := A) (B := B) h
        refine ⟨Quiver.Hom.op f, ?_⟩
        rw [← S2543QuotMapR_eq_functorMap]
        exact hf

noncomputable def S2547Functor_fullyFaithful :
    S2540Functor.FullyFaithful :=
  letI : S2540Functor.Faithful := S2542Functor_faithful
  letI : S2540Functor.Full := S2547Functor_full
  Functor.FullyFaithful.ofFullyFaithful S2540Functor

#check S2547QuotMapR_bijective
#check S2547Functor_full
#check S2547Functor_fullyFaithful
#print axioms S2547Functor_fullyFaithful
end LeanFormal.IUT.XiFPaper.S2547CorrectedFullyFaithfulActual
end