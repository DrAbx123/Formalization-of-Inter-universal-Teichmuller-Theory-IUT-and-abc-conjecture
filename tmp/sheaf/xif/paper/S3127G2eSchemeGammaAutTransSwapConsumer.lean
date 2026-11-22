import tmp.sheaf.xif.paper.S3127G2eSchemeTransHomSwapConsumer
import tmp.sheaf.xif.paper.S3127G2eSchemeGammaAutDefConsumer
import tmp.sheaf.xif.paper.S3127G2GammaAutMulActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeSpecMapConsumer
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeTransConsumer
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeTransHomSwapConsumer
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeGammaAutDefConsumer
open LeanFormal.IUT.XiFPaper.S3127G2GammaAutMulActual
namespace LeanFormal.IUT.XiFPaper.S3127G2eSchemeGammaAutTransSwapConsumer

theorem S3127G2eSchemeGammaAut_trans_swap (Y : Scheme) (e f : Y ≅ Y) :
    (S3127G2eScheme Y (gammaAut e)).hom ≫
        (S3127G2eScheme Y (gammaAut f)).hom =
      (S3127G2eScheme Y (gammaAut (e ≪≫ f))).hom := by
  rw [S3127G2eScheme_trans_hom_swap]
  rw [S3127G2GammaAut_mul]

#check S3127G2eSchemeGammaAut_trans_swap
end LeanFormal.IUT.XiFPaper.S3127G2eSchemeGammaAutTransSwapConsumer
end