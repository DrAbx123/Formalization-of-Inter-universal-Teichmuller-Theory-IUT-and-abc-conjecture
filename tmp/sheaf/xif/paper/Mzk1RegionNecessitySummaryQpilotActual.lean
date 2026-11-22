/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import Mathlib.Tactic

/-! # Mzk1RegionNecessitySummaryQpilotActual — region necessity summary (A636)

Summary of the two obstruction theorems from the green bridge module:
* no triple-independent comparison region can support the height comparison
  (`no_constantRegion_heightComparison`), so the region must depend on the triple;
* no height dictionary into the finite hull (`no_heightDictionary_into_finiteHull`),
  so the comparison routes through the additive constant. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1RegionNecessitySummaryQpilotActual

open LeanFormal.IUT
open MeasureTheory
open scoped ENNReal

universe u

/-- No constant region can support the height comparison (triple-dependence is
necessary). -/
theorem regionNecessity_noConstant {X : Type u} (W : IQHullLogVolumeInterface X)
    (R : Set X) (epsilon : Real) :
    ¬ (∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + epsilon) * (W.logVolume R).toReal) :=
  no_constantRegion_heightComparison W R epsilon

/-- No height dictionary into the finite hull region. -/
theorem regionNecessity_noDictionary {X : Type u} (W : IQHullLogVolumeInterface X)
    (hfin : W.logVolume W.hull < ⊤)
    (region : Nat → Nat → Nat → Set X)
    (hsub : ∀ a b c : Nat, IsABCTriple a b c → region a b c ⊆ W.hull) :
    ¬ (∀ a b c : Nat, IsABCTriple a b c →
        ENNReal.ofReal (Height.logHeight₁ (abcRationalPoint a c)) ≤
          W.logVolume (region a b c)) :=
  no_heightDictionary_into_finiteHull W hfin region hsub

/-- Region necessity audit rows. -/
def regionNecessityRows : List (String × String × String) :=
  [ ("triple-independent region impossible", "PROVED (obstruction)",
     "no_constantRegion_heightComparison"),
    ("height dictionary into finite hull impossible", "PROVED (obstruction)",
     "no_heightDictionary_into_finiteHull"),
    ("triple-dependent region retained", "DESIGN CONSEQUENCE",
     "normalizedComparisonRegion / TripleScalingSpec"),
    ("route through additive constant", "DESIGN CONSEQUENCE",
     "heightWeightBound_of_normalizedVolumeComparison") ]

theorem regionNecessityRows_length : regionNecessityRows.length = 4 := rfl

/-- Region necessity payload: both obstructions as function-valued fields. -/
structure RegionNecessityPayload where
  noConstant : ∀ {X : Type u} (W : IQHullLogVolumeInterface X) (R : Set X)
    (epsilon : Real),
    ¬ (∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + epsilon) * (W.logVolume R).toReal)
  noDictionary : ∀ {X : Type u} (W : IQHullLogVolumeInterface X)
    (hfin : W.logVolume W.hull < ⊤)
    (region : Nat → Nat → Nat → Set X)
    (hsub : ∀ a b c : Nat, IsABCTriple a b c → region a b c ⊆ W.hull),
    ¬ (∀ a b c : Nat, IsABCTriple a b c →
        ENNReal.ofReal (Height.logHeight₁ (abcRationalPoint a c)) ≤
          W.logVolume (region a b c))

/-- The constructed region necessity payload. -/
noncomputable def regionNecessityPayload : RegionNecessityPayload where
  noConstant := fun {X} W R epsilon => regionNecessity_noConstant W R epsilon
  noDictionary := fun {X} W hfin region hsub =>
    regionNecessity_noDictionary W hfin region hsub

#check regionNecessityRows_length
#check regionNecessityPayload

end LeanFormal.IUT.XiFPaper.Mzk1RegionNecessitySummaryQpilotActual
end
