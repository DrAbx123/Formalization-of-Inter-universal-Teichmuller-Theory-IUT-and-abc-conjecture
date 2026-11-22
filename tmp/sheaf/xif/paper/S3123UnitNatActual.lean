import tmp.sheaf.xif.paper.S3123UnitHomActual

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
open LeanFormal.IUT.XiFPaper.S3123UnitHomActual

namespace LeanFormal.IUT.XiFPaper.S3123UnitNatActual

variable {l : PrimeGeFive}

set_option maxHeartbeats 2000000 in
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
  rw [S3123UnitComp_hom, S3123UnitComp_hom]
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj,
    Functor.comp_map, S3123FiberApp_apply, S3123FiberAppInv_apply]
  haveI : Subsingleton ((Discrete.mk x) ⟶ (Discrete.mk (e (e.symm y)))) :=
    S3123FiberNatTransActual.S3123DiscreteHomSubsingleton _ _ _
  exact Subsingleton.elim _ _

#check S3123UnitNat

end LeanFormal.IUT.XiFPaper.S3123UnitNatActual
end
