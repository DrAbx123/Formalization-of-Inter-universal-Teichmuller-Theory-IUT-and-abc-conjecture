/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HeightWeightFromTripleQpilotActual
import tmp.sheaf.xif.paper.Mzk1ABCEstimatesArithmeticQpilotActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesModelQpilotActual
import tmp.sheaf.xif.paper.Mzk1HeightEstimateQpilotActual

/-! # Mzk1GapHeightWeightSharpQpilotActual — sharper (1+ε) height-weight bound (A652)

Real mathematical content: from the bridge comparison family the global height-weight
bound is derived with the **sharp reparametrization** `δ = min (ε/3) 1`, i.e.
`(1+3δ) ≤ 1+ε` holds with `δ = ε/3`, and the constant is explicit
`A = (1+δ)·(θ + D_δ)`. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.Mzk1GapHeightWeightSharpQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1HeightEstimateQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesModelQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1HeightWeightFromTripleQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCEstimatesArithmeticQpilotActual
open MeasureTheory
open scoped ENNReal

universe u

/-- Reparametrization lemma: `δ = min (ε/3) 1` satisfies `3δ ≤ ε`, `0 < δ`, `δ ≤ 1`. -/
theorem delta_third_spec {epsilon : Real} (hepsilon : 0 < epsilon) :
    0 < min (epsilon / 3) 1 ∧ min (epsilon / 3) 1 ≤ 1 ∧
      3 * min (epsilon / 3) 1 ≤ epsilon := by
  refine ⟨lt_min (by linarith) (by norm_num), min_le_right _ _, ?_⟩
  have hle : min (epsilon / 3) 1 ≤ epsilon / 3 := min_le_left _ _
  linarith

/-- Sharper global height-weight bound from a per-ε comparison family. -/
theorem heightWeightBoundShape_sharp {X : Type u} {W : IQHullLogVolumeInterface X}
    (C : ∀ epsilon : Real, 0 < epsilon → Cor312EpsilonArithmeticComparison W epsilon) :
    HeightWeightBoundShape := by
  intro epsilon hepsilon
  obtain ⟨hpos, hle1, hle3⟩ := delta_third_spec hepsilon
  obtain ⟨A, hA⟩ := height_estimate_exists (C (min (epsilon / 3) 1) hpos)
    (le_of_lt hpos) hle1
  refine ⟨A, fun a b c habc => ?_⟩
  have hh := hA a b c habc
  have hw : (0 : Real) ≤ arithmeticWeight (abcRationalPoint a c) :=
    arithmeticWeight_nonneg _
  have hmul : (1 + 3 * min (epsilon / 3) 1) * arithmeticWeight (abcRationalPoint a c) ≤
      (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) := by
    nlinarith
  linarith

#check heightWeightBoundShape_sharp

end LeanFormal.IUT.XiFPaper.Mzk1GapHeightWeightSharpQpilotActual
end
