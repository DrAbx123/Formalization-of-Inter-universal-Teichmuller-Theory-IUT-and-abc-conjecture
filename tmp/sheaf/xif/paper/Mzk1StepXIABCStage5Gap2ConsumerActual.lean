import tmp.sheaf.xif.paper.Mzk1IUTIVStage5ABCFormActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi ABC Stage-5 gap2 consumer

Consumes the green IUT IV Stage-5 literal-estimate rung
(`abcConjecture_of_literalEstimates`) with a stepxi-owned input structure.
The two estimates are explicit theorem hypotheses; no sorry/True. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIABCStage5Gap2ConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual

structure StepXIABCStage5Input where
  logVolume : Nat → Nat → Nat → Real
  hullVolume : Real
  hheight : ∀ δ : Real, 0 < δ → ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + δ) * logVolume a b c
  hmain : ∀ δ : Real, 0 < δ → ∃ D : Real,
    ∀ a b c : Nat, IsABCTriple a b c →
      logVolume a b c ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) +
        hullVolume + D

theorem stepxi_abcStage5_gap2 (I : StepXIABCStage5Input) : ABCConjecture :=
  abcConjecture_of_literalEstimates I.logVolume I.hullVolume I.hheight I.hmain

end LeanFormal.IUT.XiFPaper.Mzk1StepXIABCStage5Gap2ConsumerActual

end
