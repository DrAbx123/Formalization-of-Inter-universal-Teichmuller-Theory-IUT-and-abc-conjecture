import tmp.sheaf.xif.paper.Mzk1StepXIABCTwoGapsFormalActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi triple-dependent scaling interface

Generalizes the uniform two-gap estimates to scalings that may depend on the ABC
triple.  The uniform two-gap input embeds by taking scale = 1. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXITripleDependentScalingActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIABCTwoGapsFormalActual

structure StepXITripleDependentScaling where
  logVolume : Nat → Nat → Nat → Real
  hullVolume : Real
  scale : Nat → Nat → Nat → Real
  scale_pos : ∀ a b c : Nat, 0 < scale a b c
  height_le : ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + scale a b c) * logVolume a b c
  main_le : ∀ a b c : Nat, IsABCTriple a b c →
    ∃ D : Real, logVolume a b c ≤
      (1 + scale a b c) * arithmeticWeight (abcRationalPoint a c) + hullVolume + D

def uniformToTriple (I : StepXIABCTwoGaps) : StepXITripleDependentScaling where
  logVolume := I.logVolume
  hullVolume := I.hullVolume
  scale := fun _ _ _ => 1
  scale_pos := by intro a b c; norm_num
  height_le := by
    intro a b c habc
    simpa using I.height_gap 1 (by norm_num) a b c habc
  main_le := by
    intro a b c habc
    obtain ⟨D, hD⟩ := I.main_gap 1 (by norm_num)
    exact ⟨D, by simpa using hD a b c habc⟩

end LeanFormal.IUT.XiFPaper.Mzk1StepXITripleDependentScalingActual

end
