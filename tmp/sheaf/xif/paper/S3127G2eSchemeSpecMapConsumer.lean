import tmp.sheaf.xif.paper.S3127G2SpecMapCompActual
import tmp.sheaf.xif.paper.S3127G2GammaMapIsoCommRingCatActual
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace LeanFormal.IUT.XiFPaper.S3127G2eSchemeSpecMapConsumer

noncomputable def S3127G2eScheme (Y : Scheme) (e : Scheme.Γ.obj (Opposite.op Y) ≃+* Scheme.Γ.obj (Opposite.op Y)) :
    Spec (CommRingCat.of (Scheme.Γ.obj (Opposite.op Y))) ≅
      Spec (CommRingCat.of (Scheme.Γ.obj (Opposite.op Y))) :=
  Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso e).op

theorem S3127G2eScheme_hom (Y : Scheme)
    (e : Scheme.Γ.obj (Opposite.op Y) ≃+* Scheme.Γ.obj (Opposite.op Y)) :
    (S3127G2eScheme Y e).hom =
      Spec.map (CommRingCat.ofHom (e : Scheme.Γ.obj (Opposite.op Y) →+*
        Scheme.Γ.obj (Opposite.op Y))) := by
  rfl

#check S3127G2eScheme_hom
end LeanFormal.IUT.XiFPaper.S3127G2eSchemeSpecMapConsumer
end