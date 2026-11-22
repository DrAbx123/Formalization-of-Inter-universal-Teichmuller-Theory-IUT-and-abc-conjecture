import tmp.sheaf.xif.paper.Mzk1G1FermatDifferentActual
import tmp.sheaf.xif.paper.Mzk1G1FermatCurveNumericActual
import Mathlib
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatDifferentBoundActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatDifferentActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveNumericActual
/-- Explicit different bound for a fixed exponent: the Fermat log-different
is at most `n + log rad` for any radical `rad ≥ 1`. -/
theorem fermatDifferent_bound (n rad : Nat) (hn : 0 < n) (hrad : 1 ≤ rad) :
    fermatLogDifferent n ≤ Real.log (rad : ℝ) + (fermatDifferentExponent n : ℝ) := by
  have h := fermatLogDifferent_le_log_radical_add n rad (Nat.succ_le_of_lt hn) hrad
  unfold fermatDifferentExponent
  have hcast : (n : ℝ) ≤ ((n ^ 2 : Nat) : ℝ) := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hn2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((n : ℝ) - 1)]
    exact hn2
  linarith
#print axioms fermatDifferent_bound
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatDifferentBoundActual
end