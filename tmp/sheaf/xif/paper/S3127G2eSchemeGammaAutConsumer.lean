import tmp.sheaf.xif.paper.S3127G2eSchemeSpecMapConsumer
import tmp.sheaf.xif.paper.S3127G2ActionBaseActual
import tmp.sheaf.xif.paper.S3127GammaActionActual
import tmp.sheaf.xif.paper.S3127KLinearFullActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeSpecMapConsumer
namespace LeanFormal.IUT.XiFPaper.S3127G2eSchemeGammaAutConsumer
variable {l : PrimeGeFive} {G : Type} [Group G]

noncomputable def S3127G2eSchemeOfGammaAut
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) (g : G) :
    Spec (CommRingCat.of (Scheme.Γ.obj (Opposite.op A.obj.left.left))) ≅
      Spec (CommRingCat.of (Scheme.Γ.obj (Opposite.op A.obj.left.left))) :=
  S3127G2eScheme A.obj.left.left (gammaAut (act.act g))

theorem S3127G2eSchemeOfGammaAut_hom
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) (g : G) :
    (S3127G2eSchemeOfGammaAut A act g).hom =
      Spec.map (CommRingCat.ofHom (gammaAut (act.act g)).toRingHom) := by
  rfl

#check S3127G2eSchemeOfGammaAut_hom
end LeanFormal.IUT.XiFPaper.S3127G2eSchemeGammaAutConsumer
end