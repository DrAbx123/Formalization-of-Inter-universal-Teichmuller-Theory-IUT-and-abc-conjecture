import tmp.sheaf.xif.paper.Mzk1G1FermatDifferentActual
import tmp.sheaf.xif.paper.Mzk1G1FermatCurveNumericActual
import Mathlib
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatDifferentBoundDoneActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatDifferentActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveNumericActual
/-- Explicit different bound for a fixed exponent. -/
theorem fermatDifferent_bound (n rad : Nat) (hn : 0 < n) (hrad : 1 ≤ rad) :
    fermatLogDifferent n ≤ Real.log (rad : ℝ) + (fermatDifferentExponent n : ℝ) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog : fermatLogDifferent n ≤ (n : ℝ) := by
    have h1 := Real.log_le_sub_one_of_pos (by exact_mod_cast hn : (0:ℝ) < n)
    unfold fermatLogDifferent
    linarith
  have hradlog : 0 ≤ Real.log (rad : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast hrad)
  have hn2 : (n : ℝ) ≤ (fermatDifferentExponent n : ℝ) := by
    unfold fermatDifferentExponent
    rw [Nat.cast_pow]
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  linarith
#print axioms fermatDifferent_bound
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatDifferentBoundDoneActual
end