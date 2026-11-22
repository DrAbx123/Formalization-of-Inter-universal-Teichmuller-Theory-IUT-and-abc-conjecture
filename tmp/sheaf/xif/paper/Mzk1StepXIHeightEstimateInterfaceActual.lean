import tmp.sheaf.xif.paper.Mzk1IUTIVStage5ABCFormActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi height-estimate interface

The height gap as explicit named data; monotonicity in the volume scaling is proved. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIHeightEstimateInterfaceActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual

structure StepXIHeightEstimate where
  logVolume : Nat → Nat → Nat → Real
  height_le : ∀ δ : Real, 0 < δ → ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + δ) * logVolume a b c

theorem heightEstimate_mono (H : StepXIHeightEstimate)
    (hV : ∀ a b c : Nat, 0 ≤ H.logVolume a b c)
    {δ δ' : Real} (hδ : 0 < δ) (hle : δ ≤ δ') :
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + δ') * H.logVolume a b c := by
  intro a b c habc
  have h1 := H.height_le δ hδ a b c habc
  have h2 : (1 + δ) * H.logVolume a b c ≤ (1 + δ') * H.logVolume a b c := by
    exact mul_le_mul_of_nonneg_right (by linarith) (hV a b c)
  linarith

theorem heightEstimate_at_eps (H : StepXIHeightEstimate) {ε : Real} (hε : 0 < ε) :
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + ε) * H.logVolume a b c :=
  H.height_le ε hε

end LeanFormal.IUT.XiFPaper.Mzk1StepXIHeightEstimateInterfaceActual

end
