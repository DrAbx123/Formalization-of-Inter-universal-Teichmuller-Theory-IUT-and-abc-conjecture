import tmp.sheaf.xif.paper.S3123InvAppActual

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

namespace LeanFormal.IUT.XiFPaper.S3123InvNatActual

variable {l : PrimeGeFive}

set_option maxHeartbeats 800000 in
lemma S3123FiberNatTransInv_naturality
    {a b : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ}
    (g : a ⟶ b) {X Y : (S3123Right (l := l)).obj a} (f : X ⟶ Y) :
    ((S3123Right (l := l)).map g ≫ S3123FiberAppInv (l := l) b).toFunctor.map f ≫
        S3123FiberNatTransInvApp (l := l) g Y =
      S3123FiberNatTransInvApp (l := l) g X ≫
        ((S3123FiberAppInv (l := l) a ≫ (S3123Left (l := l)).map g).toFunctor.map f) := by
  haveI : Subsingleton
      (((S3123Right (l := l)).map g ≫ S3123FiberAppInv (l := l) b).toFunctor.obj X ⟶
        ((S3123FiberAppInv (l := l) a ≫ (S3123Left (l := l)).map g).toFunctor.obj Y)) := by
    change Subsingleton ((Discrete.mk _) ⟶ (Discrete.mk _))
    exact S3123FiberNatTransActual.S3123DiscreteHomSubsingleton _ _ _
  exact Subsingleton.elim _ _

#check S3123FiberNatTransInv_naturality

end LeanFormal.IUT.XiFPaper.S3123InvNatActual
end
