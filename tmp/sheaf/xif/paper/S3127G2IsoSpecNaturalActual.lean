import Mathlib.AlgebraicGeometry.AffineScheme
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace LeanFormal.IUT.XiFPaper.S3127G2IsoSpecNaturalActual

/-- Affine isoSpec naturality wrapper. -/
theorem S3127G2IsoSpec_natural {X Y : Scheme} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) :
    X.isoSpec.hom ≫ Spec.map (Scheme.Hom.appTop f) =
      f ≫ Y.isoSpec.hom :=
  Scheme.isoSpec_hom_naturality f

#check S3127G2IsoSpec_natural
end LeanFormal.IUT.XiFPaper.S3127G2IsoSpecNaturalActual
end