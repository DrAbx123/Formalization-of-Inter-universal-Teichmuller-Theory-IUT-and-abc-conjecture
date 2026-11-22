import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison
import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1HWConsumerActual — HW.add node consumers (equivalence + constant extraction)

DAG node: iutiv-abc:HW.add (CONDITIONAL, 0 unproved deps).  Exposes the proved
equivalence between ABCConjecture and the version-2 additive height-weight bound,
and the per-epsilon constant extraction.  The additive bound itself remains a
conditional/named target (not proved here).

No closure claim; gate NOT PASSED.  Registry frozen 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1HWConsumerActual

open LeanFormal.IUT

/-- ABCConjecture -> additive bound (forward equivalence direction). -/
theorem additiveBound_of_abcConjecture (h : ABCConjecture) :
    ABCHeightWeightAdditiveBoundV2 :=
  abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.mp h

/-- Additive bound -> ABCConjecture (backward equivalence direction). -/
theorem abcConjecture_of_additiveBound (h : ABCHeightWeightAdditiveBoundV2) :
    ABCConjecture :=
  abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.mpr h

/-- Per-epsilon constant extraction from the additive bound. -/
theorem additiveBound_exists_constant (h : ABCHeightWeightAdditiveBoundV2)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ A : Real, ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A :=
  ABCHeightWeightAdditiveBoundV2.exists_constant h hepsilon

/-- Rows: HW.add consumer status. -/
def hwConsumerRows : List (String × String × String) :=
  [ ("ABC <-> additive bound", "abcConjecture_iff_ABCHeightWeightAdditiveBoundV2 (core)", "PROVED equivalence"),
    ("forward/backward consumers", "additiveBound_of_abcConjecture / abcConjecture_of_additiveBound", "PROVED"),
    ("constant extraction", "additiveBound_exists_constant", "PROVED"),
    ("additive bound itself", "ABCHeightWeightAdditiveBoundV2", "CONDITIONAL/NAMED (not proved)"),
    ("scope", "no closure; gate NOT PASSED", "INTEGRITY") ]

theorem hwConsumerRows_length : hwConsumerRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1HWConsumerActual

end
