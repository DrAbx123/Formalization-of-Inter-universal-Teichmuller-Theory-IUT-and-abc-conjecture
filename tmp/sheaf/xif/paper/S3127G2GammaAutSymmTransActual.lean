import tmp.sheaf.xif.paper.S3127G2GammaAutMulApplyActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
open LeanFormal.IUT.XiFPaper.S3127G2GammaAutMulApplyActual
namespace LeanFormal.IUT.XiFPaper.S3127G2GammaAutSymmTransActual

theorem S3127G2GammaAut_symm_trans {Y : Scheme} (e f : Y ≅ Y)
    (x : Scheme.Γ.obj (Opposite.op Y)) :
    gammaAut (e ≪≫ f).symm x =
      gammaAut f.symm (gammaAut e.symm x) := by
  rw [Iso.trans_symm]
  rw [S3127G2GammaAut_mul_apply]

#check S3127G2GammaAut_symm_trans
end LeanFormal.IUT.XiFPaper.S3127G2GammaAutSymmTransActual
end