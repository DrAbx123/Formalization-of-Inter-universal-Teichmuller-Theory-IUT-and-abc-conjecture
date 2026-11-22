/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ABCStage5AcceptanceActual
import tmp.sheaf.xif.paper.Mzk1ABCStage5AcceptanceChecksActual
import tmp.sheaf.xif.paper.Mzk1ABCStage5AcceptanceV2ChecksActual

/-!
# A577 ABC Stage-5 acceptance wrap-up (mainline lane)

Packaging of the Stage-5 entry and its checks:
* `stage5_acceptance`: the conditional ABC reduction from the two literal estimates;
* `stage5_height_bound`: the additive height bound from the same inputs;
* checks re-exported from the acceptance checks files.

Gap-2 witness is produced by the abc/qpilot lane; the axiom gate evidence package is
qpilot-owned.  This file is the mainline statement-level wrap-up.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCStage5AcceptanceWrapUpActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCStage5AcceptanceActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCStage5AcceptanceChecksActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCStage5AcceptanceV2ChecksActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual

/-- **Stage-5 acceptance (wrap-up)**: the two literal estimates imply `ABCConjecture`. -/
theorem stage5_acceptance (logVolume : Nat → Nat → Nat → ℝ) (hullVolume : ℝ)
    (hheight : ∀ δ : ℝ, 0 < δ → ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + δ) * logVolume a b c)
    (hmain : ∀ δ : ℝ, 0 < δ → ∃ D : ℝ,
      ∀ a b c : Nat, IsABCTriple a b c →
        logVolume a b c ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) +
          hullVolume + D) :
    ABCConjecture :=
  acceptance_abcStage5 logVolume hullVolume hheight hmain

/-- **Stage-5 height bound (wrap-up)**: the same inputs give the additive height bound. -/
theorem stage5_height_bound (logVolume : Nat → Nat → Nat → ℝ) (hullVolume : ℝ)
    (hheight : ∀ δ : ℝ, 0 < δ → ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + δ) * logVolume a b c)
    (hmain : ∀ δ : ℝ, 0 < δ → ∃ D : ℝ,
      ∀ a b c : Nat, IsABCTriple a b c →
        logVolume a b c ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) +
          hullVolume + D) :
    ABCFormAdditiveHeightBound :=
  acceptance_heightBound logVolume hullVolume hheight hmain

end LeanFormal.IUT.XiFPaper.Mzk1ABCStage5AcceptanceWrapUpActual

end
