/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract

/-!
# A541 bridge: Cor312Conclusion (StepXI contract) to the paper statement

Consumes the green `StepXIContract`/`Cor312Conclusion` and records:
* the paper statement shape `qSigned <= thetaSigned` (Cor 3.12),
* the `C_Theta >= -1` form for any `C` with `thetaSigned <= C * (-qSigned)`,
* and the strict/negative reading facts.

This is a statement-level consumer; the instantiation of the contract is in
`Mzk1Cor312FinalAssemblyActual` (waiting on the Kummer chain).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperStatementBridgeActual

open LeanFormal.IUT

/-- A paper statement record: the two real readings with the Cor 3.12 inequality. -/
structure PaperStatement where
  /-- `-|log q|`. -/
  qLog : ℝ
  /-- `-|log(Theta)|`. -/
  thetaLog : ℝ
  shape : qLog ≤ thetaLog

/-- Every StepXI contract satisfying its conclusion gives a paper statement. -/
def paperStatementOfContract (c : StepXIContract) : PaperStatement where
  qLog := c.qSigned
  thetaLog := c.thetaSigned
  shape := cor312_of_constructed_stepXI c

/-- The conclusion is exactly the paper inequality. -/
theorem paperShape_iff_conclusion (c : StepXIContract) :
    Cor312Conclusion c ↔ c.qSigned ≤ c.thetaSigned :=
  Iff.rfl

/-- **`C_Theta >= -1`**: if the Theta reading is bounded by `C * (-qSigned)`, then
  `-1 <= C`; the hypothesis `0 < -qSigned` is the paper's `|log q| > 0`. -/
theorem CTheta_ge_neg_one_of_contract (c : StepXIContract) {C : ℝ}
    (hq : 0 < -c.qSigned) (hC : c.thetaSigned ≤ C * (-c.qSigned)) : -1 ≤ C := by
  have hle : c.qSigned ≤ c.thetaSigned := cor312_of_constructed_stepXI c
  have h1 : c.qSigned ≤ C * (-c.qSigned) := le_trans hle hC
  have h2 : c.qSigned / (-c.qSigned) ≤ C := (div_le_iff₀ hq).mpr h1
  have h3 : c.qSigned / (-c.qSigned) = -1 := by
    have hne : c.qSigned ≠ 0 := ne_of_lt c.q_negative
    calc c.qSigned / (-c.qSigned) = -(c.qSigned / c.qSigned) := by rw [div_neg]
      _ = -(1 : ℝ) := by rw [div_self hne]
      _ = -1 := by ring
  rw [h3] at h2
  linarith

/-- The q reading is negative (`-|log q| < 0`) in a constructed contract. -/
theorem q_negative_of_contract (c : StepXIContract) : c.qSigned < 0 :=
  c.q_negative

/-- FINITENESS: the paper readings are real numbers. -/
theorem readings_are_finite (c : StepXIContract) :
    ∃ qLog thetaLog : ℝ, qLog = c.qSigned ∧ thetaLog = c.thetaSigned :=
  ⟨c.qSigned, c.thetaSigned, rfl, rfl⟩

end

end LeanFormal.IUT.XiFPaper.Mzk1PaperStatementBridgeActual
-- A543 retry after transient missing mathlib private olean.
