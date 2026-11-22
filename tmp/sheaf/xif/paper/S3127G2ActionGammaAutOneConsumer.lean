import tmp.sheaf.xif.paper.S3127G2ActionBaseActual
import tmp.sheaf.xif.paper.S3127G2GammaAutReflApplyActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2GammaAutReflApplyActual
namespace LeanFormal.IUT.XiFPaper.S3127G2ActionGammaAutOneConsumer
variable {l : PrimeGeFive} {G : Type} [Group G]

theorem S3127G2Action_gammaAut_one
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
    (x : Scheme.Γ.obj (Opposite.op A.obj.left.left)) :
    gammaAut (act.act (1 : G)) x = x := by
  rw [act.act.map_one]
  exact S3127G2GammaAut_refl_apply A.obj.left.left x

#check S3127G2Action_gammaAut_one
end LeanFormal.IUT.XiFPaper.S3127G2ActionGammaAutOneConsumer
end