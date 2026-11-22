import tmp.sheaf.xif.paper.S3127G2eSchemeTransHomSwapConsumer
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeSpecMapConsumer
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeTransConsumer
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeTransHomSwapConsumer
namespace LeanFormal.IUT.XiFPaper.S3127G2eSchemeTransHomAssocConsumer

theorem S3127G2eScheme_trans_hom_assoc (Y : Scheme)
    (e f g : Scheme.Γ.obj (Opposite.op Y) ≃+* Scheme.Γ.obj (Opposite.op Y)) :
    ((S3127G2eScheme Y e).hom ≫ (S3127G2eScheme Y f).hom) ≫
        (S3127G2eScheme Y g).hom =
      (S3127G2eScheme Y (g.trans (f.trans e))).hom := by
  rw [S3127G2eScheme_trans_hom_swap Y e f]
  rw [S3127G2eScheme_trans_hom_swap Y (f.trans e) g]

#check S3127G2eScheme_trans_hom_assoc
end LeanFormal.IUT.XiFPaper.S3127G2eSchemeTransHomAssocConsumer
end