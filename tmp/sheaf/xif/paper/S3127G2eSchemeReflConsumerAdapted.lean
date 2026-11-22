import tmp.sheaf.xif.paper.S3127G2eSchemeGammaAutDefConsumer
import tmp.sheaf.xif.paper.S3127G2GammaAutReflActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeSpecMapConsumer
open LeanFormal.IUT.XiFPaper.S3127G2eSchemeGammaAutDefConsumer
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
open LeanFormal.IUT.XiFPaper.S3127G2GammaAutReflActual
namespace LeanFormal.IUT.XiFPaper.S3127G2eSchemeReflConsumerAdapted

theorem S3127G2eScheme_refl (Y : Scheme) :
    S3127G2eScheme Y (RingEquiv.refl (Scheme.Γ.obj (Opposite.op Y))) =
      Iso.refl (Spec (CommRingCat.of (Scheme.Γ.obj (Opposite.op Y)))) := by
  rw [S3127G2eScheme_hom]
  congr 1
  ext x
  rfl

theorem S3127G2eScheme_gammaAut_refl (Y : Scheme) :
    S3127G2eScheme Y (gammaAut (Iso.refl Y)) =
      Iso.refl (Spec (CommRingCat.of (Scheme.Γ.obj (Opposite.op Y)))) := by
  rw [S3127G2GammaAut_refl]
  exact S3127G2eScheme_refl Y

#check S3127G2eScheme_gammaAut_refl
end LeanFormal.IUT.XiFPaper.S3127G2eSchemeReflConsumerAdapted
end