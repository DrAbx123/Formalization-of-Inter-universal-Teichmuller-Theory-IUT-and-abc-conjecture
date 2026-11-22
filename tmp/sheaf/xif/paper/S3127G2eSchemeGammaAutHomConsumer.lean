import tmp.sheaf.xif.paper.S3127G2eSchemeGammaAutDefConsumer
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeSpecMapConsumer
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeGammaAutDefConsumer
namespace LeanFormal.IUT.XiFPaper.S3127G2eSchemeGammaAutHomConsumer

theorem S3127G2eScheme_gammaAut_hom (Y : Scheme) (e : Y ≅ Y) :
    (S3127G2eScheme Y (gammaAut e)).hom =
      Spec.map (CommRingCat.ofHom (gammaAut e).toRingHom) := by
  rw [S3127G2eScheme_hom]

#check S3127G2eScheme_gammaAut_hom
end LeanFormal.IUT.XiFPaper.S3127G2eSchemeGammaAutHomConsumer
end