import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi corrected-region log law

Log law for the corrected region volume under uniform scaling. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXICorrectedRegionLogLawActual

def correctedRegionVolume (V c : Real) : Real := c * V

theorem correctedRegion_log_law {V c : Real} (hV : 0 < V) (hc : 0 < c) :
    Real.log (correctedRegionVolume V c) = Real.log c + Real.log V := by
  unfold correctedRegionVolume
  exact Real.log_mul hc.ne' hV.ne'

theorem correctedRegion_log_law_prod {ι : Type*} [Fintype ι]
    (f : ι → Real) {c : Real} (hc : 0 < c) (hf : ∀ i, 0 < f i) :
    Real.log (∏ i, correctedRegionVolume (f i) c) =
      (Fintype.card ι : Real) * Real.log c + Real.log (∏ i, f i) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  rw [Real.log_mul (by positivity) (Finset.prod_pos fun i _ => hf i), Real.log_pow]
  ring

end LeanFormal.IUT.XiFPaper.Mzk1StepXICorrectedRegionLogLawActual

end
