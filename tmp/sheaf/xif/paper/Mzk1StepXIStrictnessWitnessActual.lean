import tmp.sheaf.xif.paper.Mzk1StepXIStrictnessV3Actual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi strictness numeric witnesses

Concrete witnesses for the 1D and finite-product strictness lemmas. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIStrictnessWitnessActual

open LeanFormal.IUT.XiFPaper.Mzk1StepXIStrictnessV3Actual

theorem oneDim_witness : ENNReal.ofReal (2 : Real) < ENNReal.ofReal (3 : Real) :=
  oneDim_ennreal_strict (by norm_num) (by norm_num)

theorem product_witness :
    (∏ i ∈ Finset.range 3, ((i : Real) + 2)) <
      (∏ i ∈ Finset.range 3, ((i : Real) + 3)) := by
  apply Finset.prod_lt_prod
  · intro i hi; positivity
  · intro i hi; linarith
  · exact ⟨0, by simp, by norm_num⟩

end LeanFormal.IUT.XiFPaper.Mzk1StepXIStrictnessWitnessActual

end
