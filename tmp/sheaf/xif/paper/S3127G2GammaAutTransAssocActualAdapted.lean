import tmp.sheaf.xif.paper.S3127G2GammaAutMulApplyActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
open LeanFormal.IUT.XiFPaper.S3127G2GammaAutMulApplyActual
namespace LeanFormal.IUT.XiFPaper.S3127G2GammaAutTransAssocActualAdapted

theorem S3127G2GammaAut_trans_assoc {Y : Scheme} (e f g : Y ≅ Y)
    (x : Scheme.Γ.obj (Opposite.op Y)) :
    gammaAut ((e ≪≫ f) ≪≫ g) x =
      gammaAut g (gammaAut f (gammaAut e x)) := by
  rw [S3127G2GammaAut_mul_apply]
  rw [S3127G2GammaAut_mul_apply]

#check S3127G2GammaAut_trans_assoc
end LeanFormal.IUT.XiFPaper.S3127G2GammaAutTransAssocActualAdapted
end