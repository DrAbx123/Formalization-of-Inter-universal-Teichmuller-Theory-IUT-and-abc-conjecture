/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract

/-!
# A543 facts about any Cor 3.12 StepXI contract (chain-independent)

Consumers of the green `StepXIContract`/`Cor312Conclusion` (no dependency on the
Kummer chain): the conclusion `qSigned <= thetaSigned`, sign facts, paper-shape
rewrites, the `C_Theta >= -1` form, and the strict variant when the contract has a
strict middle inequality.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312ConclusionFactsActual

open LeanFormal.IUT

/-- The conclusion, projection form. -/
theorem conclusion_of_contract (c : StepXIContract) :
    c.qSigned ≤ c.thetaSigned :=
  cor312_of_constructed_stepXI c

/-- The q reading is negative (`-|log q| < 0`). -/
theorem q_neg (c : StepXIContract) : c.qSigned < 0 :=
  c.q_negative

/-- The absolute magnitude `|log q| = -qSigned` is positive. -/
theorem qMagnitude_pos (c : StepXIContract) : 0 < -c.qSigned :=
  neg_pos.mpr c.q_negative

/-- The conclusion in difference form: `thetaSigned - qSigned >= 0`. -/
theorem difference_nonneg (c : StepXIContract) :
    0 ≤ c.thetaSigned - c.qSigned :=
  sub_nonneg.mpr (conclusion_of_contract c)

/-- The middle chain: `qSigned <= targetSigned <= thetaSigned`. -/
theorem chain (c : StepXIContract) :
    c.qSigned ≤ c.targetSigned ∧ c.targetSigned ≤ c.thetaSigned :=
  ⟨c.q_le_target, c.target_le_theta⟩

/-- `C_Theta >= -1` from the contract's conclusion and the C-Theta bound. -/
theorem CTheta_ge_neg_one (c : StepXIContract) {C : ℝ}
    (hC : c.thetaSigned ≤ C * (-c.qSigned)) : -1 ≤ C := by
  have hq : 0 < -c.qSigned := qMagnitude_pos c
  have h1 : c.qSigned ≤ C * (-c.qSigned) :=
    le_trans (conclusion_of_contract c) hC
  have h2 : c.qSigned / (-c.qSigned) ≤ C := (div_le_iff₀ hq).mpr h1
  have h3 : c.qSigned / (-c.qSigned) = -1 := by
    have hne : c.qSigned ≠ 0 := ne_of_lt (q_neg c)
    calc c.qSigned / (-c.qSigned) = -(c.qSigned / c.qSigned) := by rw [div_neg]
      _ = -(1 : ℝ) := by rw [div_self hne]
      _ = -1 := by ring
  rw [h3] at h2
  linarith

/-- Strict conclusion when the middle inequality is strict. -/
theorem strict_conclusion (c : StepXIContract) (h : c.targetSigned < c.thetaSigned) :
    c.qSigned < c.thetaSigned :=
  lt_of_le_of_lt c.q_le_target h

end

end LeanFormal.IUT.XiFPaper.Mzk1Cor312ConclusionFactsActual
-- A543 retry after transient missing mathlib private olean.
