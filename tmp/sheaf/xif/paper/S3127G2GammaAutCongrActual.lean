import tmp.sheaf.xif.paper.S3127GammaActionActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
namespace LeanFormal.IUT.XiFPaper.S3127G2GammaAutCongrActual

theorem S3127G2GammaAut_congr {Y : Scheme} {e f : Y ≅ Y}
    (h : e = f) : gammaAut e = gammaAut f :=
  congrArg gammaAut h

theorem S3127G2GammaAut_symm_symm {Y : Scheme} (e : Y ≅ Y) :
    gammaAut e.symm.symm = gammaAut e := by
  rfl

#check S3127G2GammaAut_congr
#check S3127G2GammaAut_symm_symm
end LeanFormal.IUT.XiFPaper.S3127G2GammaAutCongrActual
end