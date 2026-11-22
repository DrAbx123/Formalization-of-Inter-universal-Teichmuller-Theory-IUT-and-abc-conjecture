/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ABCBridgeGap2ConsumerActual
import Mathlib.Tactic

/-! # Mzk1Gap2NumericWitnessQpilotActual — Gap-2 SNamed numeric witnesses

A576 (qpilot lane, own name): explicit numeric inhabitants of the Gap-2 named
estimate `SNamed` and of the real-form bound `gap2_real_bound`, including a
non-degenerate instance with positive volume/weight.  These are non-vacuity
witnesses for the A502 adapter consumer, not paper estimates. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Gap2NumericWitnessQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.Objects.ABCBridgeGap2
open MeasureTheory
open scoped ENNReal

/-- Zero witness: the trivially satisfiable Gap-2 shape (`regionVolume = 0`). -/
theorem gap2_zero_witness :
    SNamed (0 : ENNReal) 0 0 0 0 ∧
      (0 : ENNReal).toReal ≤ (1 + (0 : Real)) * 0 + 0 + 0 := by
  have hS : SNamed (0 : ENNReal) 0 0 0 0 := by
    unfold SNamed
    simp
  have hR : (0 : Real) ≤ (1 + (0 : Real)) * 0 + 0 + 0 := by norm_num
  exact ⟨hS, gap2_real_bound hR hS⟩

/-- Non-degenerate witness: `regionVolume = ofReal 1`, `ε = 1/2`, `weight = 2`,
`theta = 0`, `D = 0`, so the real form reads `1 ≤ 3`. -/
theorem gap2_numeric_witness :
    SNamed (ENNReal.ofReal 1) (1/2) 2 0 0 ∧
      (ENNReal.ofReal 1).toReal ≤ (1 + (1/2 : Real)) * 2 + 0 + 0 := by
  have hS : SNamed (ENNReal.ofReal 1) (1/2) 2 0 0 := by
    unfold SNamed
    apply ENNReal.ofReal_le_ofReal
    norm_num
  have hR : (0 : Real) ≤ (1 + (1/2 : Real)) * 2 + 0 + 0 := by norm_num
  exact ⟨hS, gap2_real_bound hR hS⟩

/-- The numeric witness yields the exact real-form inequality of Gap 2. -/
theorem gap2_numeric_bound :
    (ENNReal.ofReal 1).toReal ≤ (1 + (1/2 : Real)) * 2 + 0 + 0 :=
  gap2_numeric_witness.2

#check gap2_zero_witness
#check gap2_numeric_witness

end LeanFormal.IUT.XiFPaper.Mzk1Gap2NumericWitnessQpilotActual
end
