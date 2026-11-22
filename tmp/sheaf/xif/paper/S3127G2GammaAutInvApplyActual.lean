import tmp.sheaf.xif.paper.S3127GammaActionActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
namespace LeanFormal.IUT.XiFPaper.S3127G2GammaAutInvApplyActual

theorem S3127G2GammaAut_symm_general {Y : Scheme} (e : Y ≅ Y) :
    gammaAut e.symm = (gammaAut e).symm := by
  rfl

theorem S3127G2GammaAut_symm_apply {Y : Scheme} (e : Y ≅ Y)
    (x : Scheme.Γ.obj (Opposite.op Y)) :
    gammaAut e.symm (gammaAut e x) = x := by
  rw [S3127G2GammaAut_symm_general]
  exact (gammaAut e).symm_apply_apply x

theorem S3127G2GammaAut_apply_symm {Y : Scheme} (e : Y ≅ Y)
    (x : Scheme.Γ.obj (Opposite.op Y)) :
    gammaAut e (gammaAut e.symm x) = x := by
  rw [S3127G2GammaAut_symm_general]
  exact (gammaAut e).apply_symm_apply x

#check S3127G2GammaAut_symm_apply
#check S3127G2GammaAut_apply_symm
end LeanFormal.IUT.XiFPaper.S3127G2GammaAutInvApplyActual
end