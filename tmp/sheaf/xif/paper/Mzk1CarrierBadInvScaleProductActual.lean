/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1CarrierPrimeInvScalingActual
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual

/-!
# A663 (2/2) Product badInvScale Haar law (mainline)

Product Haar law for the coordinatewise inverse bad-prime scaling on rectangles:
`μ(badInvScale e '' ∏ S_b) = (∏ ((primeFactor b)^e_b)⁻¹) · μ(∏ S_b)`.
This is the product-law blocking item for hull's scaling formula.  No canonical change;
ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1CarrierBadInvScaleProductActual

open scoped Pointwise ENNReal
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarScalingOneDimActual
open LeanFormal.IUT.XiFPaper.Mzk1CarrierPrimeInvScalingActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Coordinatewise inverse bad-prime scaling with exponents `e b`. -/
noncomputable def badInvScale (e : Bad (nativePlaceSelection T) → ℕ) :
    RootExtensionProductCarrier T → RootExtensionProductCarrier T :=
  fun x b => (((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) ^ (e b))⁻¹) • x b

/-- Image of a product rectangle under `badInvScale` is the product of the scaled
  local sets. -/
theorem badInvScale_image_pi (e : Bad (nativePlaceSelection T) → ℕ)
    (S : (b : Bad (nativePlaceSelection T)) → Set (rootNormedExtension T b)) :
    badInvScale T e '' (Set.pi Set.univ S) =
      Set.pi Set.univ (fun b => (((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) ^ (e b))⁻¹) • S b) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    intro b _
    exact ⟨y b, hy b trivial, rfl⟩
  · intro hx
    choose y hy hyx using fun b => hx b trivial
    refine ⟨y, fun b _ => hy b, ?_⟩
    funext b
    exact hyx b

/-- **Product Haar measure law on rectangles.** -/
theorem badInvScale_productHaar_pi (e : Bad (nativePlaceSelection T) → ℕ)
    (S : (b : Bad (nativePlaceSelection T)) → Set (rootNormedExtension T b)) :
    rootExtensionProductHaar T (badInvScale T e '' (Set.pi Set.univ S)) =
      (∏ b : Bad (nativePlaceSelection T),
          (ENNReal.ofReal (primeFactor T b) ^ (e b))⁻¹) *
        rootExtensionProductHaar T (Set.pi Set.univ S) := by
  rw [badInvScale_image_pi]
  unfold rootExtensionProductHaar
  rw [Measure.pi_pi, Measure.pi_pi]
  have hprod : (∏ i : Bad (nativePlaceSelection T),
        rootExtensionHaar T i ((((qVFamTensorP T i : ℚ_[(qVFamTensorP T i)]) ^ (e i))⁻¹) • S i)) =
      ∏ i : Bad (nativePlaceSelection T),
        ((ENNReal.ofReal (primeFactor T i) ^ (e i))⁻¹ *
          rootExtensionHaar T i (S i)) := by
    refine Finset.prod_congr rfl ?_
    intro i _
    exact prime_pow_inv_smul_measure T i (e i) (S i)
  rw [hprod, Finset.prod_mul_distrib]

end LeanFormal.IUT.XiFPaper.Mzk1CarrierBadInvScaleProductActual

end

/-! ### Axiom gate (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1CarrierBadInvScaleProductActual.badInvScale_productHaar_pi