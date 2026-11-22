import tmp.sheaf.xif.paper.S3127G2eSchemeInvConsumer
import tmp.sheaf.xif.paper.S3127G2eSchemeSpecMapConsumer
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeSpecMapConsumer
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeInvConsumer
namespace LeanFormal.IUT.XiFPaper.S3127G2eSchemeInvHomConsumer

theorem S3127G2eScheme_inv_hom (Y : Scheme)
    (e : Scheme.Γ.obj (Opposite.op Y) ≃+* Scheme.Γ.obj (Opposite.op Y)) :
    (S3127G2eScheme Y e).inv = (S3127G2eScheme Y e.symm).hom := by
  rw [S3127G2eScheme_inv]
  rw [S3127G2eScheme_hom]

#check S3127G2eScheme_inv_hom
end LeanFormal.IUT.XiFPaper.S3127G2eSchemeInvHomConsumer
end