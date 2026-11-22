/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1CarrierBadInvScaleProductActual
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual

/-!
# A666 corrected-region log law: concrete step + blockers (mainline)

Concrete step proved here: the inverse bad-prime scaling acts on the ACTUAL unit
region `s1902UnitRegion = rootExtensionProductUnitBall` (a product rectangle) by the
green product law:
`rootExtensionProductHaar (badInvScale e '' s1902UnitRegion) =
   (∏_b (ofReal primeFactor_b ^ e_b)⁻¹) * rootExtensionProductHaar s1902UnitRegion`.

Blockers for the full `CorrectedRegionLogLaw` (recorded, NOT assumed silently):
* (B1) single points are null for `rootExtensionProductHaar` (needed for the union with
  the triple-dependent point `{point a b c}`);
* (B2) normalization split: unwrap `s1902NormalizedHaar = s1902HaarScale • productHaar`
  and `s1902LogVolume = logVolume ∘ s1902NormalizedHaar` (plus finiteness/positivity);
* (B3) log arithmetic: `log (∏ (ofReal primeFactor_b ^ e_b)⁻¹).toReal =
  ∑ e_b d_b log p_b` using `primeFactor` and the p-adic norm.

No canonical change; ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1CorrectedRegionLogLawBlockersActual

open scoped Pointwise ENNReal
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarScalingOneDimActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1CarrierBadInvScaleProductActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The green product law specialised to the ACTUAL unit region. -/
theorem corrected_unitRegion_measure (e : Bad (nativePlaceSelection T) → Nat) :
    rootExtensionProductHaar T (Mzk1CarrierBadInvScaleProductActual.badInvScale T e '' s1902UnitRegion T) =
      (∏ b : Bad (nativePlaceSelection T),
          (ENNReal.ofReal (primeFactor T b) ^ (e b))⁻¹) *
        rootExtensionProductHaar T (s1902UnitRegion T) := by
  rw [s1902UnitRegion, rootExtensionProductUnitBall]
  exact badInvScale_productHaar_pi T e (fun b => rootExtensionUnitBall T b)

/-- The three blockers for the corrected-region log law (see file docstring). -/
def logLawBlockers : List String :=
  [ "B1: rootExtensionProductHaar {x} = 0 (null singletons) for the union with the point",
    "B2: normalization split for s1902NormalizedHaar / s1902LogVolume (smul unwrap)",
    "B3: log arithmetic log (prod (ofReal primeFactor ^ e)⁻¹).toReal = sum e d log p" ]

theorem logLawBlockers_length : logLawBlockers.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1CorrectedRegionLogLawBlockersActual

end

/-! ### Axiom gates (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1CorrectedRegionLogLawBlockersActual.corrected_unitRegion_measure
#print axioms LeanFormal.IUT.XiFPaper.Mzk1CorrectedRegionLogLawBlockersActual.logLawBlockers_length