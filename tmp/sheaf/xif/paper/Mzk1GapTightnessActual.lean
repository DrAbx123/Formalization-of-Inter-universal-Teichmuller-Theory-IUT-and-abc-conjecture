/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import tmp.sheaf.xif.paper.Mzk1PaperRegionNecessityFinalActual
import tmp.sheaf.xif.paper.Mzk1LanaBridgeAuditActual

/-!
# A646 GAP TIGHTNESS (mainline, statement/re-export)

Semantic purpose: **the reduction is tight** — the bridge boundary is calibrated to
`ABCConjecture` (`Nonempty Cor312ToABCBridgeInterface.{0} ↔ ABCConjecture`, green), and
the two named comparison fields of the region-necessity audit imply `ABCConjecture`.
Hence the named fields cannot be weakened while keeping the same reduction: their
strength is exactly the ABC boundary.  **This is NOT a proof of ABC**: the two fields
remain named hypotheses; ABC gate NOT passed.

`Mzk1PaperRegionNecessityFinalActual.paperRegionNecessityFinal` is the final audit
conjunction; here it is juxtaposed with the green boundary calibration. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1GapTightnessActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open Mzk1LanaBridgeAuditActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperRegionNecessityFinalActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- (②) The green boundary calibration: the bridge interface has exactly the strength
  of `ABCConjecture`. -/
theorem paperGap_boundary_calibrated :
    Nonempty Cor312ToABCBridgeInterface.{0} ↔ ABCConjecture :=
  cor312ToABCBridgeInterface_nonempty_iff_abcConjecture

/-- The exact proposition proved by `Mzk1PaperRegionNecessityFinalActual.paperRegionNecessityFinal`,
  restated as a `Prop` so that it can be used in a type. -/
def PaperRegionNecessityFinalClaim
    (point : Nat → Nat → Nat → S1902Carrier T) (epsilon : ℝ)
    {X : Type*} (W : IQHullLogVolumeInterface X)
    (region : Nat → Nat → Nat → Set X)
    (hfin : W.logVolume W.hull < ⊤)
    (hsub : ∀ a b c : Nat, IsABCTriple a b c → region a b c ⊆ W.hull) : Prop :=
  (¬ (∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + epsilon) * (s1902LogVolume T (s1902UnitRegion T)).toReal)) ∧
    (Gap1Prop W region →
      (∀ B : ℝ, ∃ a b c : Nat, IsABCTriple a b c ∧
        B < (W.logVolume (region a b c)).toReal)) ∧
    (¬ Gap1Prop W region) ∧
    (Nonempty (TripleDependentComparison T point) ↔
      (Gap1Prop (s1902IQHullLogVolumeInterface T)
          (paperComparisonRegion T point) ∧
        Gap2Prop (s1902IQHullLogVolumeInterface T)
          (paperComparisonRegion T point))) ∧
    ((Gap1Prop (s1902IQHullLogVolumeInterface T)
        (paperComparisonRegion T point) ∧
      Gap2Prop (s1902IQHullLogVolumeInterface T)
        (paperComparisonRegion T point)) → ABCConjecture) ∧
    (Mzk1LanaBridgeAuditActual.lanaAuditRows.length = 11)
/-- (③) Tightness: the final region-necessity audit conjunction combined with the
  boundary calibration.  The named fields remain hypotheses; this is not an ABC
  proof. -/
theorem paperGap_reduction_tight
    (point : Nat → Nat → Nat → S1902Carrier T) (epsilon : ℝ)
    {X : Type*} (W : IQHullLogVolumeInterface X)
    (region : Nat → Nat → Nat → Set X)
    (hfin : W.logVolume W.hull < ⊤)
    (hsub : ∀ a b c : Nat, IsABCTriple a b c → region a b c ⊆ W.hull) :
    PaperRegionNecessityFinalClaim T point epsilon W region hfin hsub ∧
      (Nonempty Cor312ToABCBridgeInterface.{0} ↔ ABCConjecture) :=
  ⟨paperRegionNecessityFinal T point epsilon W region hfin hsub,
   paperGap_boundary_calibrated⟩

/-- The two named comparison fields alone imply `ABCConjecture`; combined with (②),
  they are as strong as the ABC boundary (not weaker). -/
theorem paperGap_named_fields_tight
    (point : Nat → Nat → Nat → S1902Carrier T)
    (h1 : Gap1Prop (s1902IQHullLogVolumeInterface T)
      (paperComparisonRegion T point))
    (h2 : Gap2Prop (s1902IQHullLogVolumeInterface T)
      (paperComparisonRegion T point)) : ABCConjecture :=
  abc_of_gapProps T point h1 h2

end LeanFormal.IUT.XiFPaper.Mzk1GapTightnessActual

end

/-! ### Axiom gates (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1GapTightnessActual.paperGap_boundary_calibrated
#print axioms LeanFormal.IUT.XiFPaper.Mzk1GapTightnessActual.paperGap_reduction_tight
#print axioms LeanFormal.IUT.XiFPaper.Mzk1GapTightnessActual.paperGap_named_fields_tight