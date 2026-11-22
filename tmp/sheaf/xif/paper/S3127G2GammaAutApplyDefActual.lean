import tmp.sheaf.xif.paper.S3127GammaActionActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
namespace LeanFormal.IUT.XiFPaper.S3127G2GammaAutApplyDefActual

theorem S3127G2GammaAut_toRingHom_apply {Y : Scheme} (e : Y ≅ Y)
    (x : Scheme.Γ.obj (Opposite.op Y)) :
    (gammaAut e).toRingHom x = gammaAut e x := by
  rfl

theorem S3127G2GammaAut_apply_eq {Y : Scheme} (e : Y ≅ Y)
    (x : Scheme.Γ.obj (Opposite.op Y)) :
    gammaAut e x = (Scheme.Γ.mapIso e.op).commRingCatIsoToRingEquiv x := by
  rfl

#check S3127G2GammaAut_toRingHom_apply
#check S3127G2GammaAut_apply_eq
end LeanFormal.IUT.XiFPaper.S3127G2GammaAutApplyDefActual
end