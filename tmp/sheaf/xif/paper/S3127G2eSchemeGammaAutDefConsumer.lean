import tmp.sheaf.xif.paper.S3127G2eSchemeSpecMapConsumer
import tmp.sheaf.xif.paper.S3127GammaActionActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeSpecMapConsumer
namespace LeanFormal.IUT.XiFPaper.S3127G2eSchemeGammaAutDefConsumer

theorem S3127G2eScheme_gammaAut (Y : Scheme) (e : Y ≅ Y) :
    S3127G2eScheme Y (gammaAut e) =
      Scheme.Spec.mapIso (Scheme.Γ.mapIso e.op).op := by
  rfl

#check S3127G2eScheme_gammaAut
end LeanFormal.IUT.XiFPaper.S3127G2eSchemeGammaAutDefConsumer
end