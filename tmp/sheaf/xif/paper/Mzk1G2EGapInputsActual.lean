import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1G2EGapInputsActual — G2.e: explicit gap-input structure -> epsilon comparison

DAG node: iutiv-abc:G2.e.  Packages the two named IUT IV section-2 comparison fields
as an explicit structure of named Props (no proof), constructs the per-epsilon
comparison from a structure witness, and composes to ABC through the bridge.
This makes the gap inputs first-class parameters instead of anonymous fields.
Conditional; no gap proved; no closure; gate NOT PASSED.
Registry frozen 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1G2EGapInputsActual

open LeanFormal.IUT

universe u

/-- Explicit named gap inputs for Cor312EpsilonArithmeticComparison. -/
structure EpsilonGapInputs {X : Type u} (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X) (epsilon : Real) : Prop where
  height_le_normalizedRegionVolume : ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤
      (1 + epsilon) *
        (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal
  regionVolume_le_normalizedWeight : ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
    (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal ≤
      (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
        (W.logVolume W.hull).toReal + D

/-- Construct the per-epsilon comparison from explicit gap inputs. -/
def epsilonComparison_of_gapInputs {X : Type u} {W : IQHullLogVolumeInterface X}
    {logShellPoint : Nat → Nat → Nat → X} {epsilon : Real}
    (I : EpsilonGapInputs W logShellPoint epsilon) :
    Cor312EpsilonArithmeticComparison W epsilon :=
{ logShellPoint := logShellPoint
  height_le_normalizedRegionVolume := I.height_le_normalizedRegionVolume
  regionVolume_le_normalizedWeight := I.regionVolume_le_normalizedWeight }

/-- Build the bridge from per-epsilon explicit gap inputs. -/
def bridgeInterface_of_gapInputs (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    (I : ∀ epsilon : Real, 0 < epsilon → EpsilonGapInputs W logShellPoint epsilon) :
    Cor312ToABCBridgeInterface.{u} :=
{ carrier := X
  hullData := W
  epsilonComparison := fun epsilon hepsilon =>
    epsilonComparison_of_gapInputs (I epsilon hepsilon) }

/-- ABC from explicit gap inputs (conditional). -/
theorem abcConjecture_of_gapInputs (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X)
    (I : ∀ epsilon : Real, 0 < epsilon → EpsilonGapInputs W logShellPoint epsilon) :
    ABCConjecture :=
  cor312ToABCBridge_abcConjecture (bridgeInterface_of_gapInputs X W logShellPoint I)

/-- Rows: G2.e explicit gap-input status. -/
def g2EGapInputRows : List (String × String × String) :=
  [ ("explicit gap input structure", "EpsilonGapInputs", "DEF (named Props)"),
    ("epsilon comparison construction", "epsilonComparison_of_gapInputs", "DEF (conditional)"),
    ("bridge from gap inputs", "bridgeInterface_of_gapInputs", "DEF (conditional)"),
    ("ABC consumer", "abcConjecture_of_gapInputs", "PROVED (conditional)"),
    ("scope", "gaps named; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem g2EGapInputRows_length : g2EGapInputRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1G2EGapInputsActual

end
