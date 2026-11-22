import tmp.sheaf.xif.paper.S3127G2eSchemeSpecMapConsumer
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeSpecMapConsumer
namespace LeanFormal.IUT.XiFPaper.S3127G2eSchemeTransConsumer

theorem S3127G2eScheme_trans_hom (Y : Scheme)
    (e f : Scheme.Γ.obj (Opposite.op Y) ≃+* Scheme.Γ.obj (Opposite.op Y)) :
    (S3127G2eScheme Y f).hom ≫ (S3127G2eScheme Y e).hom =
      (S3127G2eScheme Y (e.trans f)).hom := by
  rw [S3127G2eScheme_hom, S3127G2eScheme_hom, S3127G2eScheme_hom]
  rw [← Spec.map_comp]
  congr 1

#check S3127G2eScheme_trans_hom
end LeanFormal.IUT.XiFPaper.S3127G2eSchemeTransConsumer
end