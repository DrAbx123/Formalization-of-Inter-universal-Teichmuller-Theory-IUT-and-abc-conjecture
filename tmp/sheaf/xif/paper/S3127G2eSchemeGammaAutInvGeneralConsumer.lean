import tmp.sheaf.xif.paper.S3127G2eSchemeInvConsumer
import tmp.sheaf.xif.paper.S3127G2eSchemeGammaAutDefConsumer
import tmp.sheaf.xif.paper.S3127GammaActionActual
import tmp.sheaf.xif.paper.S3127G2GammaAutSymmActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeSpecMapConsumer
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeInvConsumer
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeGammaAutDefConsumer
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
open LeanFormal.IUT.XiFPaper.S3127G2GammaAutSymmActual
namespace LeanFormal.IUT.XiFPaper.S3127G2eSchemeGammaAutInvGeneralConsumer

theorem S3127G2eScheme_gammaAut_inv {Y : Scheme} (e : Y ≅ Y) :
    (S3127G2eScheme Y (gammaAut e)).inv =
      (S3127G2eScheme Y (gammaAut e.symm)).hom := by
  rw [S3127G2eScheme_inv, S3127G2eScheme_gammaAut]
  rfl

#check S3127G2eScheme_gammaAut_inv
end LeanFormal.IUT.XiFPaper.S3127G2eSchemeGammaAutInvGeneralConsumer
end