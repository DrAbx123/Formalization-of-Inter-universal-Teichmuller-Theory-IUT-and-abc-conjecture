import tmp.sheaf.xif.paper.Mzk1IUTIVStage5ABCFormActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi ABC two-gap formalization

The two literal Stage-5 estimates (height comparison and main log-volume estimate)
are packaged as explicit theorem data and fed to the green adapter
`abcFormAdditiveHeightBound_of_literalEstimates`. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoGapsFormalActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual

structure StepXIABCTwoGaps where
  logVolume : Nat → Nat → Nat → Real
  hullVolume : Real
  height_gap : ∀ δ : Real, 0 < δ → ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + δ) * logVolume a b c
  main_gap : ∀ δ : Real, 0 < δ → ∃ D : Real,
    ∀ a b c : Nat, IsABCTriple a b c →
      logVolume a b c ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) +
        hullVolume + D

theorem stepxi_twoGaps_abcForm (I : StepXIABCTwoGaps) :
    ABCFormAdditiveHeightBound :=
  abcFormAdditiveHeightBound_of_literalEstimates I.logVolume I.hullVolume
    I.height_gap I.main_gap

theorem stepxi_twoGaps_ABC (I : StepXIABCTwoGaps) : ABCConjecture :=
  abcConjecture_of_abcFormAdditiveHeightBound (stepxi_twoGaps_abcForm I)

end LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoGapsFormalActual

end
