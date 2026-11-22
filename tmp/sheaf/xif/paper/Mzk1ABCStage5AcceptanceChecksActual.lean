/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ABCStage5AcceptanceActual

/-!
# A574 checks: ABC Stage-5 acceptance (actual base API)

The base `Mzk1ABCStage5AcceptanceActual` provides exactly two theorems:
`acceptance_abcStage5` and `acceptance_heightBound`.  This file checks that they are
the green IUT IV Stage-5 reductions (definitional equality).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCStage5AcceptanceChecksActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCStage5AcceptanceActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5NumericalActual

/-- The acceptance theorem is the green Stage-5 ABC reduction (rfl). -/
theorem acceptance_eq_green (logVolume : Nat → Nat → Nat → ℝ) (hullVolume : ℝ)
    (hheight : ∀ δ : ℝ, 0 < δ → ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + δ) * logVolume a b c)
    (hmain : ∀ δ : ℝ, 0 < δ → ∃ D : ℝ,
      ∀ a b c : Nat, IsABCTriple a b c →
        logVolume a b c ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) +
          hullVolume + D) :
    acceptance_abcStage5 logVolume hullVolume hheight hmain =
      abcConjecture_of_literalLogVolumeEstimates logVolume hullVolume hheight hmain :=
  rfl

/-- The height-bound acceptance is the green additive-height-bound reduction (rfl). -/
theorem heightBound_eq_green (logVolume : Nat → Nat → Nat → ℝ) (hullVolume : ℝ)
    (hheight : ∀ δ : ℝ, 0 < δ → ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + δ) * logVolume a b c)
    (hmain : ∀ δ : ℝ, 0 < δ → ∃ D : ℝ,
      ∀ a b c : Nat, IsABCTriple a b c →
        logVolume a b c ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) +
          hullVolume + D) :
    acceptance_heightBound logVolume hullVolume hheight hmain =
      additiveHeightBound_of_literalLogVolumeEstimates logVolume hullVolume hheight hmain :=
  rfl

end LeanFormal.IUT.XiFPaper.Mzk1ABCStage5AcceptanceChecksActual

end