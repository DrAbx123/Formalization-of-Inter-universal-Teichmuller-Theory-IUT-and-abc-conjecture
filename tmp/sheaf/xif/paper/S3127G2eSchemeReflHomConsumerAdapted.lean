import tmp.sheaf.xif.paper.S3127G2eSchemeSpecMapConsumer
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeSpecMapConsumer
namespace LeanFormal.IUT.XiFPaper.S3127G2eSchemeReflHomConsumerAdapted

theorem S3127G2eScheme_refl_hom (Y : Scheme) :
    (S3127G2eScheme Y (RingEquiv.refl (Scheme.Γ.obj (Opposite.op Y)))).hom =
      Spec.map (CommRingCat.ofHom
        (RingHom.id (Scheme.Γ.obj (Opposite.op Y)))) := by
  rw [S3127G2eScheme_hom]
  congr 1
  ext x
  rfl

#check S3127G2eScheme_refl_hom
end LeanFormal.IUT.XiFPaper.S3127G2eSchemeReflHomConsumerAdapted
end