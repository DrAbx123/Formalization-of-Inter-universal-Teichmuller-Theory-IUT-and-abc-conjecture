import tmp.sheaf.xif.paper.S3127G2GammaAutMulActual
import tmp.sheaf.xif.paper.S3127G2ActionBaseActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2GammaAutMulActual
namespace LeanFormal.IUT.XiFPaper.S3127G2ActionGammaAutConsumer
variable {l : PrimeGeFive} {G : Type} [Group G]

theorem S3127G2Action_gammaAut_mul
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) (g h : G) :
    gammaAut (act.act (g * h)) =
      (gammaAut (act.act g)).trans (gammaAut (act.act h)) := by
  rw [act.act.map_mul]
  rw [Aut.Aut_mul_def]
  rw [S3127G2GammaAut_mul]

#check S3127G2Action_gammaAut_mul
end LeanFormal.IUT.XiFPaper.S3127G2ActionGammaAutConsumer
end