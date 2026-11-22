import tmp.sheaf.xif.paper.Mzk1Gap2ArithmeticReductionActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# stepxi vacuity arithmetic support (A703)

For every prime `P ≥ 5`, `(1, (P-3)/2, (P-1)/2)` is an ABC triple and has
`N = a+b+c+1 = P`.  This supports the retraction of `final_conditional_ABC`. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIVacuityArithmeticActual

theorem isABCTriple_one_of_prime
    (P : Nat) (hP : Nat.Prime P) (h5 : 5 ≤ P) :
    IsABCTriple 1 ((P - 3) / 2) ((P - 1) / 2) := by
  obtain ⟨k, hk⟩ := hP.odd_of_ne_two (by omega)
  subst hk
  have hk2 : 2 ≤ k := by omega
  have hb_eq : 2 * k + 1 - 3 = 2 * (k - 1) := by omega
  have hc_eq : 2 * k + 1 - 1 = 2 * k := by omega
  have hb : (2 * k + 1 - 3) / 2 = k - 1 := by
    rw [hb_eq, Nat.mul_div_right _ (by norm_num)]
  have hc : (2 * k + 1 - 1) / 2 = k := by
    rw [hc_eq, Nat.mul_div_right _ (by norm_num)]
  rw [hb, hc]
  refine ⟨by norm_num, by omega, by omega, Nat.coprime_one_left _⟩

end LeanFormal.IUT.XiFPaper.Mzk1StepXIVacuityArithmeticActual

end
