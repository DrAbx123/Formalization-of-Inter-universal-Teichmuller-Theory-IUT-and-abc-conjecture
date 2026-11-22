/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1CarrierPrimeInvScalingActual
import tmp.sheaf.xif.paper.Mzk1CarrierBadInvScaleProductActual

/-!
# A663 thin re-export: carrier badInvScale law (mainline)

Split into `Mzk1CarrierPrimeInvScalingActual` (1D laws) and
`Mzk1CarrierBadInvScaleProductActual` (product law); this file keeps the original
`Mzk1CarrierBadInvScaleLawActual` API as thin re-exports for downstream consumers.
No new mathematics; ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped Pointwise ENNReal

namespace LeanFormal.IUT.XiFPaper.Mzk1CarrierBadInvScaleLawActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarScalingOneDimActual
open LeanFormal.IUT.XiFPaper.Mzk1CarrierPrimeInvScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1CarrierBadInvScaleProductActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

theorem prime_inv_smul_measure (S : Set (rootNormedExtension T b)) :
    rootExtensionHaar T b
        (((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)])⁻¹) • S) =
      (ENNReal.ofReal (primeFactor T b))⁻¹ * rootExtensionHaar T b S :=
  Mzk1CarrierPrimeInvScalingActual.prime_inv_smul_measure T b S

theorem prime_pow_inv_smul_measure (e : ℕ) (S : Set (rootNormedExtension T b)) :
    rootExtensionHaar T b
        ((((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) ^ e)⁻¹) • S) =
      (ENNReal.ofReal (primeFactor T b) ^ e)⁻¹ * rootExtensionHaar T b S :=
  Mzk1CarrierPrimeInvScalingActual.prime_pow_inv_smul_measure T b e S

noncomputable def badInvScale (e : Bad (nativePlaceSelection T) → ℕ) :
    RootExtensionProductCarrier T → RootExtensionProductCarrier T :=
  Mzk1CarrierBadInvScaleProductActual.badInvScale T e

theorem badInvScale_image_pi (e : Bad (nativePlaceSelection T) → ℕ)
    (S : (b : Bad (nativePlaceSelection T)) → Set (rootNormedExtension T b)) :
    badInvScale T e '' (Set.pi Set.univ S) =
      Set.pi Set.univ (fun b => (((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) ^ (e b))⁻¹) • S b) :=
  Mzk1CarrierBadInvScaleProductActual.badInvScale_image_pi T e S

theorem badInvScale_productHaar_pi (e : Bad (nativePlaceSelection T) → ℕ)
    (S : (b : Bad (nativePlaceSelection T)) → Set (rootNormedExtension T b)) :
    rootExtensionProductHaar T (badInvScale T e '' (Set.pi Set.univ S)) =
      (∏ b : Bad (nativePlaceSelection T),
          (ENNReal.ofReal (primeFactor T b) ^ (e b))⁻¹) *
        rootExtensionProductHaar T (Set.pi Set.univ S) :=
  Mzk1CarrierBadInvScaleProductActual.badInvScale_productHaar_pi T e S

/-- Next steps (not yet proved here; recorded explicitly). -/
def nextSteps : List String :=
  [ "log form of the product Haar law (via ENNReal.toReal_mul and Real.log_mul)",
    "normalized `s1902` log form (cancel `s1902HaarScale`)",
    "`badPart` arithmetic: divisibility, `<= N`, full-support criterion",
    "connect to A656 `PaperRegionScalingLaw` with ratio `badPart N` (rectangle case)" ]

theorem nextSteps_length : nextSteps.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1CarrierBadInvScaleLawActual

end