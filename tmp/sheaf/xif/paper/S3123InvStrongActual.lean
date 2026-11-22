import tmp.sheaf.xif.paper.S3123InvNatActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S3123XKStackExtension
open LeanFormal.IUT.XiFPaper.S3123FiberEquivalenceActual
open LeanFormal.IUT.XiFPaper.S3123FiberNatTransActual
open LeanFormal.IUT.XiFPaper.S3123FiberStrongTransActual
open LeanFormal.IUT.XiFPaper.S3123FiberStrongTransInvActual
open LeanFormal.IUT.XiFPaper.S3123InvAppActual
open LeanFormal.IUT.XiFPaper.S3123InvNatActual

namespace LeanFormal.IUT.XiFPaper.S3123InvStrongActual

variable {l : PrimeGeFive}

@[irreducible] noncomputable def S3123InvLeftFunctor
    {a b : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ}
    (g : a ⟶ b) :
    (S3123Right (l := l)).obj a ⥤ (S3123Left (l := l)).obj b :=
  ((S3123Right (l := l)).map g ≫ S3123FiberAppInv (l := l) b).toFunctor

@[irreducible] noncomputable def S3123InvRightFunctor
    {a b : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ}
    (g : a ⟶ b) :
    (S3123Right (l := l)).obj a ⥤ (S3123Left (l := l)).obj b :=
  (((S3123FiberAppInv (l := l) a ≫ (S3123Left (l := l)).map g).toFunctor)

set_option maxHeartbeats 800000 in
noncomputable def S3123FiberNatTransInvApp'
    {a b : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ}
    (g : a ⟶ b) (X : (S3123Right (l := l)).obj a) :
    (S3123InvLeftFunctor (l := l) g).obj X ⟶
      (S3123InvRightFunctor (l := l) g).obj X :=
  S3123FiberNatTransInvApp (l := l) g X

set_option maxHeartbeats 800000 in
lemma S3123FiberNatTransInv_naturality'
    {a b : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ}
    (g : a ⟶ b) {X Y : (S3123Right (l := l)).obj a} (f : X ⟶ Y) :
    (S3123InvLeftFunctor (l := l) g).map f ≫
        S3123FiberNatTransInvApp' (l := l) g Y =
      S3123FiberNatTransInvApp' (l := l) g X ≫
        (S3123InvRightFunctor (l := l) g).map f :=
  S3123FiberNatTransInv_naturality (l := l) g f

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
noncomputable def S3123FiberNatTransInv
    {a b : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ}
    (g : a ⟶ b) :
    NatTrans (S3123InvLeftFunctor (l := l) g)
      (S3123InvRightFunctor (l := l) g) :=
  { app := fun X => S3123FiberNatTransInvApp' (l := l) g X
    naturality := fun X Y f => S3123FiberNatTransInv_naturality' (l := l) g f }

#check S3123FiberNatTransInv

end LeanFormal.IUT.XiFPaper.S3123InvStrongActual
end
