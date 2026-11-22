import tmp.sheaf.xif.paper.S3127G2GammaAutMulActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
open LeanFormal.IUT.XiFPaper.S3127G2GammaAutMulActual
namespace LeanFormal.IUT.XiFPaper.S3127G2GammaAutMulApplyActual

theorem S3127G2GammaAut_mul_apply {Y : Scheme} (e f : Y ≅ Y)
    (x : Scheme.Γ.obj (Opposite.op Y)) :
    gammaAut (e ≪≫ f) x = gammaAut e (gammaAut f x) := by
  rw [S3127G2GammaAut_mul]
  rfl

#check S3127G2GammaAut_mul_apply
end LeanFormal.IUT.XiFPaper.S3127G2GammaAutMulApplyActual
end