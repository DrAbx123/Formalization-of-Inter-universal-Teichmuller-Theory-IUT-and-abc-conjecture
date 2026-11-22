import tmp.sheaf.xif.paper.S3127G2eSchemeTransReflRightConsumer
import tmp.sheaf.xif.paper.S3127G2eSchemeGammaAutDefConsumer
import tmp.sheaf.xif.paper.S3127G2GammaAutReflActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeSpecMapConsumer
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeTransConsumer
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeTransReflRightConsumer
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeGammaAutDefConsumer
open LeanFormal.IUT.XiFPaper.S3127G2GammaAutReflActual
namespace LeanFormal.IUT.XiFPaper.S3127G2eSchemeTransReflRightGammaAutConsumer

theorem S3127G2eScheme_trans_refl_right_gammaAut (Y : Scheme) (e : Y ≅ Y) :
    (S3127G2eScheme Y (gammaAut e)).hom ≫
        (S3127G2eScheme Y (gammaAut (Iso.refl Y))).hom =
      (S3127G2eScheme Y (gammaAut e)).hom := by
  rw [S3127G2GammaAut_refl]
  exact S3127G2eScheme_trans_refl_right Y (gammaAut e)

#check S3127G2eScheme_trans_refl_right_gammaAut
end LeanFormal.IUT.XiFPaper.S3127G2eSchemeTransReflRightGammaAutConsumer
end