import tmp.sheaf.xif.paper.Mzk1StepXIABCTwoGapsFormalActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi ABC two-estimates model

A model carrying the two literal estimates as fields, with proved equivalence to
`StepXIABCTwoGaps` and the ABC consequence. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoEstimatesModelActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoGapsFormalActual

structure StepXIABCTwoEstimatesModel where
  logVolume : Nat → Nat → Nat → Real
  hullVolume : Real
  height_le : ∀ δ : Real, 0 < δ → ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + δ) * logVolume a b c
  main_le : ∀ δ : Real, 0 < δ → ∃ D : Real,
    ∀ a b c : Nat, IsABCTriple a b c →
      logVolume a b c ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) +
        hullVolume + D

def StepXIABCTwoEstimatesModel.toGaps (I : StepXIABCTwoEstimatesModel) :
    StepXIABCTwoGaps where
  logVolume := I.logVolume
  hullVolume := I.hullVolume
  height_gap := I.height_le
  main_gap := I.main_le

def StepXIABCTwoGaps.toModel (I : StepXIABCTwoGaps) : StepXIABCTwoEstimatesModel where
  logVolume := I.logVolume
  hullVolume := I.hullVolume
  height_le := I.height_gap
  main_le := I.main_gap

theorem stepxi_model_ABC (I : StepXIABCTwoEstimatesModel) : ABCConjecture :=
  stepxi_twoGaps_ABC I.toGaps

end LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoEstimatesModelActual

end
