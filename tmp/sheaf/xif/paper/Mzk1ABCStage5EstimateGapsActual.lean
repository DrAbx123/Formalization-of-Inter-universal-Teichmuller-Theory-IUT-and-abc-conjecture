/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ABCStage5AcceptanceActual

/-!
# A590 ABC Stage-5: the two named estimate GAPS (explicit, no closure)

The two missing inputs of the Stage-5 ABC chain are recorded as the fields of
`ABCStage5Gaps` (height comparison / main log-volume estimate).  From them the ABC
conjecture follows by the green Stage-5 reduction; no `sorry`, no custom axiom, and
no claim that the gaps themselves are proved.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCStage5EstimateGapsActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCStage5AcceptanceActual

/-- The two named estimate gaps of the Stage-5 ABC chain. -/
structure ABCStage5Gaps where
  /-- Gap 1: literal height comparison (`-|log Theta| >= -|log q|` input shape). -/
  logVolume : Nat → Nat → Nat → ℝ
  hullVolume : ℝ
  hheight : ∀ δ : ℝ, 0 < δ → ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + δ) * logVolume a b c
  /-- Gap 2: main log-volume estimate (`(HDD)`/SHE output shape). -/
  hmain : ∀ δ : ℝ, 0 < δ → ∃ D : ℝ,
    ∀ a b c : Nat, IsABCTriple a b c →
      logVolume a b c ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) +
        hullVolume + D

/-- **Conditional Stage-5 rung**: the two gaps imply the ABC conjecture. -/
theorem abc_of_gaps (G : ABCStage5Gaps) : ABCConjecture :=
  acceptance_abcStage5 G.logVolume G.hullVolume G.hheight G.hmain

/-- The gap structure is non-vacuous in shape: its fields are exactly the two
  named estimates (definitional projections). -/
theorem gaps_fields_shape (G : ABCStage5Gaps) :
    (∀ δ : ℝ, 0 < δ → ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + δ) * G.logVolume a b c) ∧
    (∀ δ : ℝ, 0 < δ → ∃ D : ℝ,
      ∀ a b c : Nat, IsABCTriple a b c →
        G.logVolume a b c ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) +
          G.hullVolume + D) :=
  ⟨G.hheight, G.hmain⟩

end LeanFormal.IUT.XiFPaper.Mzk1ABCStage5EstimateGapsActual

end
