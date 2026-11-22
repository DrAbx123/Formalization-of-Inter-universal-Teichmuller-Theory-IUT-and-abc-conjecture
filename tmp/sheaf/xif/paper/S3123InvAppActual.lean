import tmp.sheaf.xif.paper.S3123FiberInvNatLemma

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

namespace LeanFormal.IUT.XiFPaper.S3123InvAppActual

variable {l : PrimeGeFive}

set_option maxHeartbeats 800000 in
noncomputable def S3123FiberNatTransInvApp
    {a b : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ}
    (g : a ⟶ b) (X : (S3123Right (l := l)).obj a) :
    ((S3123Right (l := l)).map g ≫ S3123FiberAppInv (l := l) b).toFunctor.obj X ⟶
      ((S3123FiberAppInv (l := l) a ≫ (S3123Left (l := l)).map g).toFunctor.obj X) := by
  rcases X with ⟨Q⟩
  apply Discrete.eqToHom
  simp only [CategoryTheory.Cat.Hom.comp_toFunctor, Functor.comp_obj,
    S3123Right_map_apply, S3123FiberAppInv_apply, S3123Left_map_apply]
  exact S3123FiberNatTransInv_app_eq (l := l) g Q

#check S3123FiberNatTransInvApp

end LeanFormal.IUT.XiFPaper.S3123InvAppActual
end
