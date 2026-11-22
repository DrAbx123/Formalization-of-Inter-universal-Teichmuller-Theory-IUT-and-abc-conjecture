import tmp.sheaf.xif.paper.S3127G2ActionBaseActual
import tmp.sheaf.xif.paper.S3127G2GammaAutSymmTransActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2GammaAutSymmTransActual
namespace LeanFormal.IUT.XiFPaper.S3127G2ActionGammaAutSymmMulConsumerAdapted
variable {l : PrimeGeFive} {G : Type} [Group G]

theorem S3127G2Action_gammaAut_symm_mul
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) (g h : G)
    (x : Scheme.Γ.obj (Opposite.op A.obj.left.left)) :
    gammaAut (act.act g ≪≫ act.act h).symm x =
      gammaAut (act.act g).symm (gammaAut (act.act h).symm x) := by
  exact S3127G2GammaAut_symm_trans (act.act g) (act.act h) x

#check S3127G2Action_gammaAut_symm_mul
end LeanFormal.IUT.XiFPaper.S3127G2ActionGammaAutSymmMulConsumerAdapted
end