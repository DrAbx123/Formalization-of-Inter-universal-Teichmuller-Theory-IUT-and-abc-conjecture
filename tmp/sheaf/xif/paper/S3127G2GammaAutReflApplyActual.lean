import tmp.sheaf.xif.paper.S3127GammaActionActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
namespace LeanFormal.IUT.XiFPaper.S3127G2GammaAutReflApplyActual

theorem S3127G2GammaAut_refl_apply (Y : Scheme)
    (x : Scheme.Γ.obj (Opposite.op Y)) :
    gammaAut (Iso.refl Y) x = x := by
  rfl

#check S3127G2GammaAut_refl_apply
end LeanFormal.IUT.XiFPaper.S3127G2GammaAutReflApplyActual
end