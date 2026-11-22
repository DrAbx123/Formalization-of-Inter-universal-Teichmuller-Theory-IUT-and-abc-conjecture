import Mathlib
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatDifferentActual
/-- Log of the Fermat different (model value). -/
def fermatLogDifferent (n : Nat) : ℝ := Real.log (n : ℝ)
/-- Numeric different bound: `log n ≤ log rad + n` for any radical `rad ≥ 1`. -/
theorem fermatLogDifferent_le_log_radical_add (n rad : Nat)
    (hn : 1 ≤ n) (hrad : 1 ≤ rad) :
    fermatLogDifferent n ≤ Real.log (rad : ℝ) + (n : ℝ) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog : fermatLogDifferent n ≤ (n : ℝ) - 1 := by
    unfold fermatLogDifferent
    exact Real.log_le_sub_one_of_pos hnpos
  have hradlog : 0 ≤ Real.log (rad : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast hrad)
  linarith
#print axioms fermatLogDifferent_le_log_radical_add
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatDifferentActual
end