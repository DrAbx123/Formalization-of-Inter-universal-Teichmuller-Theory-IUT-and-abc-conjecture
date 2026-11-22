import Mathlib.AlgebraicGeometry.AffineScheme
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace LeanFormal.IUT.XiFPaper.S3127G2SpecMapCompActual

theorem S3127G2SpecMap_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T) :
    Spec.map (f ≫ g) = Spec.map g ≫ Spec.map f :=
  Spec.map_comp f g

#check S3127G2SpecMap_comp
end LeanFormal.IUT.XiFPaper.S3127G2SpecMapCompActual
end