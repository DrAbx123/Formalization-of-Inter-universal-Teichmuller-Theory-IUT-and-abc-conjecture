import tmp.sheaf.xif.paper.S3127G2eSchemeTransConsumer
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeSpecMapConsumer
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeTransConsumer
namespace LeanFormal.IUT.XiFPaper.S3127G2eSchemeTransHomSwapConsumer

theorem S3127G2eScheme_trans_hom_swap (Y : Scheme)
    (e f : Scheme.Γ.obj (Opposite.op Y) ≃+* Scheme.Γ.obj (Opposite.op Y)) :
    (S3127G2eScheme Y e).hom ≫ (S3127G2eScheme Y f).hom =
      (S3127G2eScheme Y (f.trans e)).hom := by
  exact S3127G2eScheme_trans_hom Y f e

#check S3127G2eScheme_trans_hom_swap
end LeanFormal.IUT.XiFPaper.S3127G2eSchemeTransHomSwapConsumer
end