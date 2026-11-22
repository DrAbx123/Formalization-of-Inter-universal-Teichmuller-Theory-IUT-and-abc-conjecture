import tmp.sheaf.xif.paper.S3127G2ActionGammaAutConsumer
import tmp.sheaf.xif.paper.S3127G2GammaAutMulApplyActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2ActionGammaAutConsumer
open LeanFormal.IUT.XiFPaper.S3127G2GammaAutMulApplyActual
namespace LeanFormal.IUT.XiFPaper.S3127G2ActionGammaAutApplyConsumer
variable {l : PrimeGeFive} {G : Type} [Group G]

theorem S3127G2Action_gammaAut_apply
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) (g h : G)
    (x : Scheme.Γ.obj (Opposite.op A.obj.left.left)) :
    gammaAut (act.act (g * h)) x =
      gammaAut (act.act g) (gammaAut (act.act h) x) := by
  rw [S3127G2Action_gammaAut_mul]
  rw [S3127G2GammaAut_mul_apply]

#check S3127G2Action_gammaAut_apply
end LeanFormal.IUT.XiFPaper.S3127G2ActionGammaAutApplyConsumer
end