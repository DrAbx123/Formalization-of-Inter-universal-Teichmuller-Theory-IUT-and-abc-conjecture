import tmp.sheaf.xif.paper.S3123UnitActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S3123XKStackExtension
open LeanFormal.IUT.XiFPaper.S3123FiberEquivalenceActual
open LeanFormal.IUT.XiFPaper.S3123FiberNatTransActual
open LeanFormal.IUT.XiFPaper.S3123FiberStrongTransActual
open LeanFormal.IUT.XiFPaper.S3123FiberStrongTransInvActual
open LeanFormal.IUT.XiFPaper.S3123InvAppActual
open LeanFormal.IUT.XiFPaper.S3123InvNatActual
open LeanFormal.IUT.XiFPaper.S3123ObjEqActual
open LeanFormal.IUT.XiFPaper.S3123StrongInvActual
open LeanFormal.IUT.XiFPaper.S3123UnitActual

namespace LeanFormal.IUT.XiFPaper.S3123UnitAppActual
variable {l : PrimeGeFive}

set_option maxHeartbeats 800000 in
lemma S3123UnitNat
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ)
    {X Y : (S3123Left (l := l)).obj U} (f : X ⟶ Y) :
    (𝟭 ((S3123Left (l := l)).obj U)).map f ≫
        (S3123UnitComp (l := l) U Y.as).hom =
      (S3123UnitComp (l := l) U X.as).hom ≫
        ((S3123FiberApp (l := l) U ≫
          S3123FiberAppInv (l := l) U).toFunctor.map f) := by
  rcases X with ⟨x⟩
  rcases Y with ⟨y⟩
  let e := (Over.mapPullbackAdj (S3123BaseSpecMap (l := l))).homEquiv
    (Opposite.unop U.as) (S1419AffineOver (l := l))
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj,
    Functor.comp_map, S3123FiberApp_apply, S3123FiberAppInv_apply]
  haveI : Subsingleton ((Discrete.mk x) ⟶ (Discrete.mk (e (e.symm y)))) :=
    S3123FiberNatTransActual.S3123DiscreteHomSubsingleton _ _ _
  exact Subsingleton.elim _ _

set_option maxHeartbeats 800000 in
noncomputable def S3123UnitApp
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ) :
    (𝟙 ((S3123Left (l := l)).obj U)) ≅
      (S3123FiberApp (l := l) U ≫ S3123FiberAppInv (l := l) U) :=
  CategoryTheory.Cat.Hom.isoMk
    (NatIso.ofComponents
      (fun X => by rcases X with ⟨P⟩; exact S3123UnitComp (l := l) U P)
      (fun {X Y} f => S3123UnitNat (l := l) U f))

#check S3123UnitApp


end LeanFormal.IUT.XiFPaper.S3123UnitAppActual
end
