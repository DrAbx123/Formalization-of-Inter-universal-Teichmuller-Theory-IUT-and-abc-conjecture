/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ABCStage5AcceptanceV2Actual

/-!
# A572 ABC Stage-5 acceptance V2 checks (mainline lane)

Machine checks of the adopted `Mzk1ABCStage5AcceptanceV2Actual`:
* the acceptance is the green `abcConjecture_of_literalLogVolumeEstimates`;
* the same inputs give the additive height bound;
* the axiom gate output for `Mzk1AxiomGateActual.gate_cor312` is in the watchdog log
  (expected `[propext, Classical.choice, Quot.sound]`).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCStage5AcceptanceV2ChecksActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCStage5AcceptanceV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5NumericalActual

/-- The acceptance is the green Stage-5 reduction (definitional). -/
theorem acceptance_eq_green (logVolume : Nat → Nat → Nat → Real) (hullVolume : Real)
    (hheight : ∀ δ : Real, 0 < δ → ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + δ) * logVolume a b c)
    (hmain : ∀ δ : Real, 0 < δ → ∃ D : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        logVolume a b c ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) +
          hullVolume + D) :
    acceptance_abcStage5 logVolume hullVolume hheight hmain =
      abcConjecture_of_literalLogVolumeEstimates logVolume hullVolume hheight hmain :=
  rfl

/-- The height-bound acceptance is the green additive-height-bound reduction. -/
theorem heightBound_eq_green (logVolume : Nat → Nat → Nat → Real) (hullVolume : Real)
    (hheight : ∀ δ : Real, 0 < δ → ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + δ) * logVolume a b c)
    (hmain : ∀ δ : Real, 0 < δ → ∃ D : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        logVolume a b c ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) +
          hullVolume + D) :
    acceptance_heightBound logVolume hullVolume hheight hmain =
      additiveHeightBound_of_literalLogVolumeEstimates logVolume hullVolume hheight hmain :=
  rfl

end LeanFormal.IUT.XiFPaper.Mzk1ABCStage5AcceptanceV2ChecksActual

end
