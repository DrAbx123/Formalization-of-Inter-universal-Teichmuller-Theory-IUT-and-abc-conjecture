import tmp.sheaf.xif.paper.S3123StrongInvActual
import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo

attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.instBicategory
attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.homCategory

noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Bicategory
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open scoped Pseudofunctor.StrongTrans
open CategoryTheory.Pseudofunctor.StrongTrans
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
open LeanFormal.IUT.XiFPaper.S3123StrongInvActual

namespace LeanFormal.IUT.XiFPaper.S3123UnitIsoDataActual

variable {l : PrimeGeFive}

structure S3123UnitIsoData where
  app : ∀ U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ,
    (Pseudofunctor.StrongTrans.id (S3123Result (l := l)).fiber).app U ≅
      (Pseudofunctor.StrongTrans.vcomp (S3123FiberStrongTrans (l := l))
        (S3123FiberStrongTransInv (l := l))).app U
  naturality : ∀ {U V : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ}
    (f : U ⟶ V),
    (S3123Result (l := l)).fiber.map f ◁ (app V).hom ≫
        ((Pseudofunctor.StrongTrans.vcomp (S3123FiberStrongTrans (l := l))
          (S3123FiberStrongTransInv (l := l))).naturality f).hom =
      ((Pseudofunctor.StrongTrans.id (S3123Result (l := l)).fiber).naturality f).hom ≫
        (app U).hom ▷ (S3123Result (l := l)).fiber.map f

set_option maxHeartbeats 800000 in
noncomputable def S3123UnitIsoData.toIso (d : S3123UnitIsoData (l := l)) :
    Pseudofunctor.StrongTrans.id (S3123Result (l := l)).fiber ≅
      Pseudofunctor.StrongTrans.vcomp (S3123FiberStrongTrans (l := l))
        (S3123FiberStrongTransInv (l := l)) :=
  Pseudofunctor.StrongTrans.isoMk d.app d.naturality

structure S3123CounitIsoData where
  app : ∀ U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ,
    (Pseudofunctor.StrongTrans.vcomp (S3123FiberStrongTransInv (l := l))
      (S3123FiberStrongTrans (l := l))).app U ≅
      (Pseudofunctor.StrongTrans.id (S3123Right (l := l))).app U
  naturality : ∀ {U V : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ}
    (f : U ⟶ V),
    (S3123Right (l := l)).map f ◁ (app V).hom ≫
        ((Pseudofunctor.StrongTrans.id (S3123Right (l := l))).naturality f).hom =
      ((Pseudofunctor.StrongTrans.vcomp (S3123FiberStrongTransInv (l := l))
        (S3123FiberStrongTrans (l := l))).naturality f).hom ≫
        (app U).hom ▷ (S3123Right (l := l)).map f

set_option maxHeartbeats 800000 in
noncomputable def S3123CounitIsoData.toIso (d : S3123CounitIsoData (l := l)) :
    Pseudofunctor.StrongTrans.vcomp (S3123FiberStrongTransInv (l := l))
      (S3123FiberStrongTrans (l := l)) ≅
      Pseudofunctor.StrongTrans.id (S3123Right (l := l)) :=
  Pseudofunctor.StrongTrans.isoMk d.app d.naturality

#check S3123UnitIsoData.toIso
#check S3123CounitIsoData.toIso

end LeanFormal.IUT.XiFPaper.S3123UnitIsoDataActual
end
