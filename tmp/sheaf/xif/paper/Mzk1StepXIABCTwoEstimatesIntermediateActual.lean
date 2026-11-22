import tmp.sheaf.xif.paper.Mzk1StepXIABCTwoGapsFormalActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi ABC two-estimates intermediate lemmas

From the two explicit estimates (`height_gap`, `main_gap`) derive the intermediate
coefficient data used by the Stage-5 adapter, without changing the input object. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoEstimatesIntermediateActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoGapsFormalActual

theorem twoGaps_delta_selection (I : StepXIABCTwoGaps) {ε : Real} (hε : 0 < ε) :
    ∃ δ : Real, 0 < δ ∧ (1 + δ) ^ 2 ≤ 1 + ε ∧
      ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
        I.logVolume a b c ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) +
          I.hullVolume + D := by
  obtain ⟨δ, hδ0, hδsq⟩ := exists_delta_sq_le_one_add hε
  obtain ⟨D, hD⟩ := I.main_gap δ hδ0
  exact ⟨δ, hδ0, hδsq, D, hD⟩

theorem twoGaps_height_intermediate (I : StepXIABCTwoGaps) {ε : Real} (hε : 0 < ε) :
    ∃ δ : Real, 0 < δ ∧ (1 + δ) ^ 2 ≤ 1 + ε ∧
      ∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + δ) * I.logVolume a b c := by
  obtain ⟨δ, hδ0, hδsq⟩ := exists_delta_sq_le_one_add hε
  exact ⟨δ, hδ0, hδsq, I.height_gap δ hδ0⟩

theorem twoGaps_main_intermediate (I : StepXIABCTwoGaps) {δ : Real} (hδ : 0 < δ) :
    ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      I.logVolume a b c ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) +
        I.hullVolume + D :=
  I.main_gap δ hδ

end LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoEstimatesIntermediateActual

end
