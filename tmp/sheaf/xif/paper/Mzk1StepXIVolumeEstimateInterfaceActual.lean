import tmp.sheaf.xif.paper.Mzk1IUTIVStage5ABCFormActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi volume-estimate interface

The main gap as explicit named data; monotonicity in the scaling is proved. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIVolumeEstimateInterfaceActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual

structure StepXIVolumeEstimate where
  logVolume : Nat → Nat → Nat → Real
  hullVolume : Real
  main_le : ∀ δ : Real, 0 < δ → ∃ D : Real,
    ∀ a b c : Nat, IsABCTriple a b c →
      logVolume a b c ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) +
        hullVolume + D

theorem volumeEstimate_mono (V : StepXIVolumeEstimate)
    {δ δ' : Real} (hδ : 0 < δ) (hle : δ ≤ δ') :
    ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      V.logVolume a b c ≤ (1 + δ') * arithmeticWeight (abcRationalPoint a c) +
        V.hullVolume + D := by
  obtain ⟨D, hD⟩ := V.main_le δ hδ
  refine ⟨D, fun a b c habc => ?_⟩
  have h1 := hD a b c habc
  have hw : 0 ≤ arithmeticWeight (abcRationalPoint a c) := arithmeticWeight_nonneg_local _
  have h2 : (1 + δ) * arithmeticWeight (abcRationalPoint a c) ≤
      (1 + δ') * arithmeticWeight (abcRationalPoint a c) := by
    exact mul_le_mul_of_nonneg_right (by linarith) hw
  linarith

theorem volumeEstimate_at_eps (V : StepXIVolumeEstimate) {ε : Real} (hε : 0 < ε) :
    ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      V.logVolume a b c ≤ (1 + ε) * arithmeticWeight (abcRationalPoint a c) +
        V.hullVolume + D :=
  V.main_le ε hε

end LeanFormal.IUT.XiFPaper.Mzk1StepXIVolumeEstimateInterfaceActual

end
