/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1IUTIVStage5NumericalActual
import Mathlib.Tactic

/-!
# A573 ABC Stage-5 acceptance (clean; axiom gate moved to `Mzk1ABCStage5AxiomGateActual`)

* `acceptance_abcStage5`: the IUT IV Stage-5 ABC-form reduction as a conditional
  theorem from the two named literal log-volume estimates (no closure claim);
* `acceptance_heightBound`: the same named inputs give the additive height bound.

Green imports (`Mzk1IUTIVStage5NumericalActual`) only; the axiom gate and the
Cor 3.12 payload live in `Mzk1ABCStage5AxiomGateActual.lean`. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCStage5AcceptanceActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5NumericalActual

/-- Acceptance: the IUT IV Stage-5 ABC reduction (named literal estimates). -/
theorem acceptance_abcStage5
    (logVolume : Nat → Nat → Nat → Real) (hullVolume : Real)
    (hheight : ∀ δ : Real, 0 < δ → ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + δ) * logVolume a b c)
    (hmain : ∀ δ : Real, 0 < δ → ∃ D : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        logVolume a b c ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) +
          hullVolume + D) :
    ABCConjecture :=
  abcConjecture_of_literalLogVolumeEstimates logVolume hullVolume hheight hmain

/-- Acceptance: the same named inputs give the additive height bound. -/
theorem acceptance_heightBound
    (logVolume : Nat → Nat → Nat → Real) (hullVolume : Real)
    (hheight : ∀ δ : Real, 0 < δ → ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + δ) * logVolume a b c)
    (hmain : ∀ δ : Real, 0 < δ → ∃ D : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        logVolume a b c ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) +
          hullVolume + D) :
    ABCFormAdditiveHeightBound :=
  additiveHeightBound_of_literalLogVolumeEstimates logVolume hullVolume hheight hmain

end LeanFormal.IUT.XiFPaper.Mzk1ABCStage5AcceptanceActual

end