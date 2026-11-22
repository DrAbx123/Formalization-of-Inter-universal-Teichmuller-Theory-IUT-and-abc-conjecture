import tmp.sheaf.xif.paper.S3127G2GammaInvariantInterfaceActual
import tmp.sheaf.xif.paper.S3127G2GammaAlgHomActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127GammaRAlgebraActual
open LeanFormal.IUT.XiFPaper.S3127GammaCompActual
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2GammaAlgHomActual
open LeanFormal.IUT.XiFPaper.S3127G2GammaInvariantInterfaceActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2HPhiConsumerActual
variable {l : PrimeGeFive} {G : Type} [Group G]
variable {A B : S3127FiniteEtaleOverKFull l} (act : S3127OverRAction A G)
variable (f : A ⟶ B) (hf : ∀ g : G, S3127G2Action A act g ≫ f = f)

/-- Actual hφ consumer: the R-linearity map constructed from `f` is
invariant under the action of `G`. -/
theorem S3127G2HPhiConsumer (hf : ∀ g : G, S3127G2Action A act g ≫ f = f) (g : G) (b : Scheme.Γ.obj (Opposite.op B.obj.left.left)) :
    letI := gammaMulSemiringAction act.act
    letI := gammaAlgebraOf B.obj.left.left B.obj.hom.left
    letI := gammaAlgebraOf A.obj.left.left A.obj.hom.left
    groupActionRingEquiv (Scheme.Γ.obj (Opposite.op A.obj.left.left)) G g
      (gammaAlgHomOfFullHom f b) = gammaAlgHomOfFullHom f b := by
  letI := gammaMulSemiringAction act.act
  letI := gammaAlgebraOf B.obj.left.left B.obj.hom.left
  letI := gammaAlgebraOf A.obj.left.left A.obj.hom.left
  exact gammaAlgHomOfFullHom_invariant act f hf g b

#check S3127G2HPhiConsumer
end LeanFormal.IUT.XiFPaper.S3127G2HPhiConsumerActual
end
