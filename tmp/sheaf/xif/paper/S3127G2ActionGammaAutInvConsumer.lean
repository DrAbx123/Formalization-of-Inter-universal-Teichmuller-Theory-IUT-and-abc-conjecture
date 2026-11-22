import tmp.sheaf.xif.paper.S3127G2ActionBaseActual
import tmp.sheaf.xif.paper.S3127G2GammaAutInvApplyActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2GammaAutInvApplyActual
namespace LeanFormal.IUT.XiFPaper.S3127G2ActionGammaAutInvConsumer
variable {l : PrimeGeFive} {G : Type} [Group G]

theorem S3127G2Action_gammaAut_symm
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) (g : G) :
    gammaAut (act.act g).symm = (gammaAut (act.act g)).symm := by
  exact S3127G2GammaAut_symm_general (act.act g)

theorem S3127G2Action_gammaAut_symm_apply
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) (g : G)
    (x : Scheme.Γ.obj (Opposite.op A.obj.left.left)) :
    gammaAut (act.act g).symm (gammaAut (act.act g) x) = x := by
  exact S3127G2GammaAut_symm_apply (act.act g) x

#check S3127G2Action_gammaAut_symm_apply
end LeanFormal.IUT.XiFPaper.S3127G2ActionGammaAutInvConsumer
end