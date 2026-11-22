import tmp.sheaf.xif.paper.S3127G2eSchemeSpecMapConsumer
import tmp.sheaf.xif.paper.S3127G2eSchemeInvConsumer
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeSpecMapConsumer
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeInvConsumer
namespace LeanFormal.IUT.XiFPaper.S3127G2eSchemeSymmHomConsumer

theorem S3127G2eScheme_symm_hom (Y : Scheme)
    (e : Scheme.Γ.obj (Opposite.op Y) ≃+* Scheme.Γ.obj (Opposite.op Y)) :
    (S3127G2eScheme Y e.symm).hom = (S3127G2eScheme Y e).inv := by
  rw [S3127G2eScheme_hom, S3127G2eScheme_inv]

#check S3127G2eScheme_symm_hom
end LeanFormal.IUT.XiFPaper.S3127G2eSchemeSymmHomConsumer
end