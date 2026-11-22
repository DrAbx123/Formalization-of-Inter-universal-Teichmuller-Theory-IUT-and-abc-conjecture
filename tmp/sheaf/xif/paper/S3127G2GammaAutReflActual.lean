import tmp.sheaf.xif.paper.S3127GammaActionActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
namespace LeanFormal.IUT.XiFPaper.S3127G2GammaAutReflActual

theorem S3127G2GammaAut_refl (Y : Scheme) :
    gammaAut (Iso.refl Y) = RingEquiv.refl (Scheme.Γ.obj (Opposite.op Y)) := by
  rfl

#check S3127G2GammaAut_refl
end LeanFormal.IUT.XiFPaper.S3127G2GammaAutReflActual
end