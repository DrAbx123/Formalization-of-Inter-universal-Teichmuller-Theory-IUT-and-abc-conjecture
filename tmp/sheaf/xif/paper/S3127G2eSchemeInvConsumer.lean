import tmp.sheaf.xif.paper.S3127G2eSchemeSpecMapConsumer
import tmp.sheaf.xif.paper.S3127G2GammaMapIsoSymmActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeSpecMapConsumer
namespace LeanFormal.IUT.XiFPaper.S3127G2eSchemeInvConsumer

theorem S3127G2eScheme_inv (Y : Scheme)
    (e : Scheme.Γ.obj (Opposite.op Y) ≃+* Scheme.Γ.obj (Opposite.op Y)) :
    (S3127G2eScheme Y e).inv =
      Spec.map (CommRingCat.ofHom (e.symm : Scheme.Γ.obj (Opposite.op Y) →+*
        Scheme.Γ.obj (Opposite.op Y))) := by
  rfl

#check S3127G2eScheme_inv
end LeanFormal.IUT.XiFPaper.S3127G2eSchemeInvConsumer
end