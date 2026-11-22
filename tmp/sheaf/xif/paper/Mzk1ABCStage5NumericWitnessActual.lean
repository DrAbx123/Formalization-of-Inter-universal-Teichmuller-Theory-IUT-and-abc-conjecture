/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1IUTIVStage5NumericalCoreActual
import tmp.sheaf.xif.paper.Mzk1ABCStage5EstimateGapsActual

/-!
# A590 ABC Stage-5 numeric witness (verified arithmetic only)

* `delta_witness`: for every `ε > 0` there is `δ > 0` with `(1+δ)^2 ≤ 1+ε`
  (the exact numerical step used by the Stage-5 reduction);
* `gaps_numeric_shape`: the ABCStage5Gaps records are the literal estimates;
* `resolved_requirement_link`: the Cor 3.12 resolved requirement realizes the
  `-|log Theta| >= -|log q|` side used by Gap 1 (via the green resolved acceptance).

No numerical claim about the actual ABC triples is made here: the two estimates
remain the named gaps of `Mzk1ABCStage5EstimateGapsActual`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCStage5NumericWitnessActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5NumericalCoreActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCStage5EstimateGapsActual

/-- Numeric witness: `δ = min (ε/4) (1/2)` satisfies `(1+δ)^2 ≤ 1+ε`. -/
theorem delta_witness {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ (1 + δ) ^ 2 ≤ 1 + ε :=
  exists_delta_sq_le_one_add hε

/-- The recorded gaps are exactly the two literal estimates (re-export). -/
theorem gaps_are_named_estimates (G : ABCStage5Gaps) :
    (∀ δ : ℝ, 0 < δ → ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + δ) * G.logVolume a b c) ∧
    (∀ δ : ℝ, 0 < δ → ∃ D : ℝ,
      ∀ a b c : Nat, IsABCTriple a b c →
        G.logVolume a b c ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) +
          G.hullVolume + D) :=
  gaps_fields_shape G

/-- Conditional Stage-5 link: the two gaps imply `ABCConjecture` (green rung). -/
theorem abc_of_named_gaps (G : ABCStage5Gaps) : ABCConjecture :=
  abc_of_gaps G
end LeanFormal.IUT.XiFPaper.Mzk1ABCStage5NumericWitnessActual

end
