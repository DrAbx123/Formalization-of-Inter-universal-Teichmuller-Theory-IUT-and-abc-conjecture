import Mathlib.AlgebraicGeometry.AffineScheme
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace LeanFormal.IUT.XiFPaper.S3127G2GammaMapIsoSymmActual

theorem S3127G2GammaMapIso_symm {X Y : Scheme} (e : X ≅ Y) :
    Scheme.Γ.mapIso e.symm.op = (Scheme.Γ.mapIso e.op).symm := by
  rfl

#check S3127G2GammaMapIso_symm
end LeanFormal.IUT.XiFPaper.S3127G2GammaMapIsoSymmActual
end