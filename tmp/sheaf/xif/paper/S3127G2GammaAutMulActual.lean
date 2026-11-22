import tmp.sheaf.xif.paper.S3127GammaActionActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
namespace LeanFormal.IUT.XiFPaper.S3127G2GammaAutMulActual

theorem S3127G2GammaAut_mul {Y : Scheme} (e f : Y ≅ Y) :
    gammaAut (e ≪≫ f) = (gammaAut f).trans (gammaAut e) := by
  ext x
  change ((Scheme.Γ.mapIso f.op ≪≫ Scheme.Γ.mapIso e.op).commRingCatIsoToRingEquiv) x =
    ((Scheme.Γ.mapIso f.op).commRingCatIsoToRingEquiv.trans
      (Scheme.Γ.mapIso e.op).commRingCatIsoToRingEquiv) x
  rfl

#check S3127G2GammaAut_mul
end LeanFormal.IUT.XiFPaper.S3127G2GammaAutMulActual
end