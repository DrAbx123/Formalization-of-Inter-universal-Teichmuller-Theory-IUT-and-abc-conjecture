import tmp.sheaf.xif.paper.S3127G2GammaAlgHomActual
import tmp.sheaf.xif.paper.S3127G2RActionActual
import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
import tmp.sheaf.xif.paper.S3127GammaActionActual
import tmp.sheaf.xif.paper.S3127GammaCompActual
import tmp.sheaf.xif.paper.S3127GammaRAlgebraActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127GammaRAlgebraActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127GammaCompActual
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
open LeanFormal.IUT.XiFPaper.S3127G2GammaAlgHomActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2GammaInvariantInterfaceActual
variable {l : PrimeGeFive} {G : Type} [Group G]
variable {A B : S3127FiniteEtaleOverKFull l}
variable (act : S3127OverRAction A G) (f : A ⟶ B)

theorem S3127G2GammaActionBridge (g : G) :
    letI := gammaMulSemiringAction act.act
    letI := gammaAlgebraOf A.obj.left.left A.obj.hom.left
    groupActionRingEquiv (Scheme.Γ.obj (Opposite.op A.obj.left.left)) G g =
      gammaAut ((act.act g).symm) := by
  letI := gammaMulSemiringAction act.act
  letI := gammaAlgebraOf A.obj.left.left A.obj.hom.left
  ext x
  rfl

theorem gammaAlgHomOfFullHom_invariant
    (hf : ∀ g : G, S3127G2Action A act g ≫ f = f) :
    letI := gammaMulSemiringAction act.act
    letI := gammaAlgebraOf B.obj.left.left B.obj.hom.left
    letI := gammaAlgebraOf A.obj.left.left A.obj.hom.left
    ∀ (g : G) (b : Scheme.Γ.obj (Opposite.op B.obj.left.left)),
      groupActionRingEquiv (Scheme.Γ.obj (Opposite.op A.obj.left.left)) G g
        (gammaAlgHomOfFullHom f b) = gammaAlgHomOfFullHom f b := by
  letI := gammaMulSemiringAction act.act
  letI := gammaAlgebraOf B.obj.left.left B.obj.hom.left
  letI := gammaAlgebraOf A.obj.left.left A.obj.hom.left
  intro g b
  rw [S3127G2GammaActionBridge act g]
  have h := congrArg
    (fun k : A ⟶ B => (Scheme.Γ.map k.hom.left.left.op).hom) (hf g)
  have h' := congrArg
    (fun φ : Scheme.Γ.obj (Opposite.op B.obj.left.left) →+*
      Scheme.Γ.obj (Opposite.op A.obj.left.left) => φ b) h
  unfold gammaAut
  change (CommRingCat.Hom.hom
    (Scheme.Γ.map (Iso.op (Iso.symm (act.act g))).hom))
    ((gammaAlgHomOfFullHom f) b) = (gammaAlgHomOfFullHom f) b
  convert h' using 2 <;> rfl

#check S3127G2GammaActionBridge
#check gammaAlgHomOfFullHom_invariant
end LeanFormal.IUT.XiFPaper.S3127G2GammaInvariantInterfaceActual
end
