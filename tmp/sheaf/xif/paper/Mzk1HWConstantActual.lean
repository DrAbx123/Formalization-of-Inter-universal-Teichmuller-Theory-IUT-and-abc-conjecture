import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1HWConstantActual — additive height-weight bound with nonnegative constants

DAG node: iutiv-abc:HW.add.  Normalizes the version-2 additive bound so its
additive constant can be chosen nonnegative; this is the form used by consumers
that need 0 <= A (e.g. dilation bookkeeping).  No new arithmetic input;
no closure; gate NOT PASSED.  Registry 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1HWConstantActual

open LeanFormal.IUT

/-- The additive bound with a nonnegative constant. -/
theorem exists_constant_nonneg (h : ABCHeightWeightAdditiveBoundV2)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ A : Real, 0 ≤ A ∧ ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A := by
  obtain ⟨A, hA⟩ := h.exists_constant hepsilon
  refine ⟨max A 0, le_max_right _ _, ?_⟩
  intro a b c habc
  have h1 := hA a b c habc
  have hA0 : A ≤ max A 0 := le_max_left _ _
  linarith

/-- Equivalent nonnegative-constant form of the version-2 additive bound. -/
theorem additiveBoundV2_iff_forall_nonneg_constant :
    ABCHeightWeightAdditiveBoundV2 ↔
      ∀ epsilon : Real, 0 < epsilon → ∃ A : Real, 0 ≤ A ∧
        ∀ a b c : Nat, IsABCTriple a b c →
          Height.logHeight₁ (abcRationalPoint a c) ≤
            (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A := by
  constructor
  · intro h epsilon hepsilon
    exact exists_constant_nonneg h hepsilon
  · intro h epsilon hepsilon
    obtain ⟨A, _, hA⟩ := h epsilon hepsilon
    exact ⟨A, hA⟩

/-- Rows: nonnegative-constant normalization status. -/
def hwConstantRows : List (String × String × String) :=
  [ ("nonneg constant", "exists_constant_nonneg", "PROVED"),
    ("equivalent form", "additiveBoundV2_iff_forall_nonneg_constant", "PROVED"),
    ("scope", "normalization consumer; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem hwConstantRows_length : hwConstantRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1HWConstantActual

end
