import tmp.sheaf.xif.paper.S3123StrongInvActual

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
open LeanFormal.IUT.XiFPaper.S3123StrongInvActual

attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.instBicategory

namespace LeanFormal.IUT.XiFPaper.S3123StrongTransCompActualAdapted

variable {l : PrimeGeFive}

@[simp] lemma S3123ForwardInv_app
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ) :
    (S3123FiberStrongTrans (l := l) ≫
      S3123FiberStrongTransInv (l := l)).app U =
    (S3123FiberStrongTrans (l := l)).app U ≫
      (S3123FiberStrongTransInv (l := l)).app U := rfl

@[simp] lemma S3123InvForward_app
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ) :
    (S3123FiberStrongTransInv (l := l) ≫
      S3123FiberStrongTrans (l := l)).app U =
    (S3123FiberStrongTransInv (l := l)).app U ≫
      (S3123FiberStrongTrans (l := l)).app U := rfl

@[simp] lemma S3123IdLeft_app
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ) :
    (𝟙 (S3123Result (l := l)).fiber).app U =
    𝟙 ((S3123Result (l := l)).fiber.obj U) := rfl

@[simp] lemma S3123IdRight_app
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ) :
    (𝟙 (S3123Right (l := l))).app U =
    𝟙 ((S3123Right (l := l)).obj U) := rfl

#check S3123ForwardInv_app
#check S3123InvForward_app
#check S3123IdLeft_app
#check S3123IdRight_app

end LeanFormal.IUT.XiFPaper.S3123StrongTransCompActualAdapted
end
