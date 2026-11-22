import tmp.sheaf.xif.paper.S3127G2eSchemeTransConsumer
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeSpecMapConsumer
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeTransConsumer
namespace LeanFormal.IUT.XiFPaper.S3127G2eSchemeTransReflRightConsumer

theorem S3127G2eScheme_trans_refl_right (Y : Scheme)
    (e : Scheme.Γ.obj (Opposite.op Y) ≃+* Scheme.Γ.obj (Opposite.op Y)) :
    (S3127G2eScheme Y e).hom ≫
        (S3127G2eScheme Y (RingEquiv.refl (Scheme.Γ.obj (Opposite.op Y)))).hom =
      (S3127G2eScheme Y e).hom := by
  rw [S3127G2eScheme_trans_hom]
  congr 1

#check S3127G2eScheme_trans_refl_right
end LeanFormal.IUT.XiFPaper.S3127G2eSchemeTransReflRightConsumer
end