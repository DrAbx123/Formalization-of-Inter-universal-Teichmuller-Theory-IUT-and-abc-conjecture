import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1G2EEpsilonActual — G2.e consumer: epsilon comparison -> bridge interface

DAG node: iutiv-abc:G2.e (CONDITIONAL, interface).  Exposes the definitional construction
of the bridge interface from its three data fields (carrier / hullData / per-epsilon
comparison) and the two named comparison fields as projections.  This is the interface
consumer used by the fragment; it proves no comparison (the two fields stay named).

No closure claim; gate NOT PASSED.  Registry frozen 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1G2EEpsilonActual

open LeanFormal.IUT

universe u

/-- **G2.e construction:** build the bridge interface from its three explicit data fields. -/
def bridgeInterface_of_data (carrier : Type u) (hullData : IQHullLogVolumeInterface carrier)
    (epsilonComparison : ∀ epsilon : Real, 0 < epsilon →
      Cor312EpsilonArithmeticComparison hullData epsilon) :
    Cor312ToABCBridgeInterface.{u} :=
  { carrier := carrier
    hullData := hullData
    epsilonComparison := epsilonComparison }

/-- **G2.e consumer:** from the three data fields the ABC height bound follows (through the
proved conditional bridge). -/
theorem heightBound_of_data (carrier : Type u) (hullData : IQHullLogVolumeInterface carrier)
    (epsilonComparison : ∀ epsilon : Real, 0 < epsilon →
      Cor312EpsilonArithmeticComparison hullData epsilon) :
    ∀ epsilon : Real, 0 < epsilon → ∃ A : Real, ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A :=
  cor312ToABCBridge_heightBound (bridgeInterface_of_data carrier hullData epsilonComparison)

/-- **G2.e ABC consumer.** -/
theorem abcConjecture_of_data (carrier : Type u) (hullData : IQHullLogVolumeInterface carrier)
    (epsilonComparison : ∀ epsilon : Real, 0 < epsilon →
      Cor312EpsilonArithmeticComparison hullData epsilon) :
    ABCConjecture :=
  cor312ToABCBridge_abcConjecture (bridgeInterface_of_data carrier hullData epsilonComparison)

/-- The two named comparison fields of the per-epsilon data (projections; unproved). -/
theorem epsilonComparison_named_fields {X : Type u} {W : IQHullLogVolumeInterface X}
    {epsilon : Real} (C : Cor312EpsilonArithmeticComparison W epsilon) :
    (∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + epsilon) *
          (W.logVolume (normalizedComparisonRegion W C.logShellPoint a b c)).toReal) ∧
    (∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      (W.logVolume (normalizedComparisonRegion W C.logShellPoint a b c)).toReal ≤
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
          (W.logVolume W.hull).toReal + D) :=
  ⟨C.height_le_normalizedRegionVolume, C.regionVolume_le_normalizedWeight⟩

/-- Rows: G2.e consumer status. -/
def g2eRows : List (String × String × String) :=
  [ ("G2.e data construction", "bridgeInterface_of_data", "DEF (definitional assembly)"),
    ("G2.e height bound consumer", "heightBound_of_data", "PROVED (conditional on fields)"),
    ("G2.e ABC consumer", "abcConjecture_of_data", "PROVED (conditional on fields)"),
    ("named comparison fields", "height_le_normalizedRegionVolume / regionVolume_le_normalizedWeight", "NAMED (not proved)"),
    ("scope", "no closure; gate NOT PASSED", "INTEGRITY") ]

theorem g2eRows_length : g2eRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1G2EEpsilonActual

end
