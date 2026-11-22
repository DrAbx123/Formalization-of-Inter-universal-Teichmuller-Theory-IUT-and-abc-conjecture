/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ABCEstimatesArithmeticQpilotActual
import Mathlib.Tactic

/-! # Mzk1WeightCounterexampleQpilotActual — weight/absorption counterexamples (A652)

Why the absorption `(1+ε)^2 ≤ 1+3ε` needs `ε ≤ 1`, and why the absorbed bound needs
nonnegative weight.  Explicit numeric counterexamples. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1WeightCounterexampleQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ABCEstimatesArithmeticQpilotActual

/-- Absorption fails without `ε ≤ 1`: at `ε = 2`, `(1+ε)^2 = 9 > 7 = 1+3ε`. -/
theorem absorption_needs_eps_le_one :
    ¬ ((1 + (2 : Real)) * (1 + 2) ≤ 1 + 3 * 2) :=
  by norm_num

/-- At `ε = 2` the absorption inequality is false in its universal form. -/
theorem absorption_false_at_two :
    ∃ epsilon : Real, ¬ ((1 + epsilon) * (1 + epsilon) ≤ 1 + 3 * epsilon) :=
  ⟨2, by norm_num⟩

/-- The absorbed bound needs nonnegative weight: at `ε = 1/2`, `w = -1`,
`(1+ε)^2·w = -2.25 > -2.5 = (1+3ε)·w`. -/
theorem absorbed_needs_weight_nonneg :
    ∃ (w epsilon : Real), w < 0 ∧
      ¬ ((1 + epsilon) * (1 + epsilon) * w ≤ (1 + 3 * epsilon) * w) :=
  ⟨-1, 1/2, by norm_num, by norm_num⟩

/-- The sharp reparametrization keeps `3δ ≤ ε` for all `ε > 0` with `δ = min (ε/3) 1`. -/
theorem sharp_delta_keeps_bound {epsilon : Real} (h : 0 < epsilon) :
    3 * min (epsilon / 3) 1 ≤ epsilon := by
  have hle : min (epsilon / 3) 1 ≤ epsilon / 3 := min_le_left _ _
  linarith

#check absorption_false_at_two
#check absorbed_needs_weight_nonneg
#check sharp_delta_keeps_bound

end LeanFormal.IUT.XiFPaper.Mzk1WeightCounterexampleQpilotActual
end
