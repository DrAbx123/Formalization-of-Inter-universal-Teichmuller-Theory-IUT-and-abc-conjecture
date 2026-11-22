import tmp.sheaf.xif.paper.S3127GammaActionActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
namespace LeanFormal.IUT.XiFPaper.S3127G2GammaAutDefActual

theorem S3127G2GammaAut_def {Y : Scheme} (e : Y ≅ Y) :
    gammaAut e = (Scheme.Γ.mapIso e.op).commRingCatIsoToRingEquiv := by
  rfl

#check S3127G2GammaAut_def
end LeanFormal.IUT.XiFPaper.S3127G2GammaAutDefActual
end