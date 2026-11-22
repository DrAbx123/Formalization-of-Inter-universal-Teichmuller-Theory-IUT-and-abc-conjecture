/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1IUTIVStage5NumericalActual
import tmp.sheaf.xif.paper.Mzk1AxiomGateActual
import Mathlib.Tactic

/-!
# A570 ABC Stage-5 acceptance V2 (green-import-only consumer; adopted under mainline)

* `acceptance_abcStage5`: the Stage-5 ABC-form reduction as a conditional theorem,
  named literal-estimate inputs, no closure claim;
* `acceptance_heightBound`: the same named inputs give the additive height bound;
* axiom gate: `#print axioms` of the green `Mzk1AxiomGateActual.gate_cor312`
  (expected `[propext, Classical.choice, Quot.sound]`).

Green imports only; no leftover `#print`-in-namespace, no broken payload.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCStage5AcceptanceV2Actual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5NumericalActual
open LeanFormal.IUT.XiFPaper.Mzk1AxiomGateActual

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

end LeanFormal.IUT.XiFPaper.Mzk1ABCStage5AcceptanceV2Actual

/-! ### Axiom gate (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1AxiomGateActual.gate_cor312

end