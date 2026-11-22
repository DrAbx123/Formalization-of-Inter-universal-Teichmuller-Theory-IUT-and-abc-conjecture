import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # Mzk1ProcessionContributionNumericsActual — procession sum of local log-volume contributions

Lean transcription of the arithmetic of the mined independent verification script
12_procession_local_contributions (laichunwing, IUT-Verification, Unit L):
at a bad prime p with theta value Theta_j = q^{j^2/(2l)}, the local log-volume
contribution at level j is mu_j = (j^2 * m)/(2l) * log p, and its
procession-normalized sum is ((l+1)/24) * m * log p with l = 2*l* + 1.

Pure real arithmetic; no new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ProcessionContributionNumericsActual

open scoped BigOperators

/-- The local log-volume contribution of the theta value at level j:
mu_j = j^2 * m / (2 l) * log p. -/
noncomputable def processionContribution (m l j : Nat) (p : Real) : Real :=
  (j : Real) ^ 2 * (m : Real) / (2 * (l : Real)) * Real.log p

/-- Closed form of the sum of squares: sum_{j=0}^{n} j^2 = n(n+1)(2n+1)/6. -/
theorem sum_range_sq_succ (n : Nat) :
    (∑ j ∈ Finset.range (n + 1), (j : Real) ^ 2) =
      (n : Real) * ((n : Real) + 1) * (2 * (n : Real) + 1) / 6 := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- The local contributions factor as a constant times j^2. -/
theorem processionContribution_eq_factor (m n j : Nat) (p : Real) :
    processionContribution m (2 * n + 1) j p =
      ((m : Real) * Real.log p / (2 * (2 * (n : Real) + 1))) * (j : Real) ^ 2 := by
  unfold processionContribution
  push_cast
  ring

/-- Procession sum identity (Unit L): averaging the local contributions over
j = 1, ..., l* gives ((l+1)/24) * m * log p with l = 2*l* + 1. -/
theorem processionContribution_average (m n : Nat) (p : Real) (hn : 0 < n) :
    (1 / (n : Real)) *
        (∑ j ∈ Finset.range (n + 1), processionContribution m (2 * n + 1) j p) =
      ((n : Real) + 1) / 12 * (m : Real) * Real.log p := by
  have hfactor : ∀ j ∈ Finset.range (n + 1),
      processionContribution m (2 * n + 1) j p =
        ((m : Real) * Real.log p / (2 * (2 * (n : Real) + 1))) * (j : Real) ^ 2 :=
    fun j _ => processionContribution_eq_factor m n j p
  rw [Finset.sum_congr rfl hfactor, ← Finset.mul_sum, sum_range_sq_succ]
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast hn
  field_simp
  ring

/-- The averaged contribution written with l = 2 l* + 1: coefficient (l+1)/24. -/
theorem processionContribution_average_l (m n : Nat) (p : Real) (hn : 0 < n) :
    (1 / (n : Real)) *
        (∑ j ∈ Finset.range (n + 1), processionContribution m (2 * n + 1) j p) =
      (((2 * n + 1 : Nat) : Real) + 1) / 24 * (m : Real) * Real.log p := by
  rw [processionContribution_average m n p hn]
  push_cast
  ring

/-- Concrete Unit L instance: p = 11, m = 5. -/
theorem processionContribution_average_eleven (n : Nat) (hn : 0 < n) :
    (1 / (n : Real)) *
        (∑ j ∈ Finset.range (n + 1),
          processionContribution 5 (2 * n + 1) j (11 : Real)) =
      ((n : Real) + 1) / 12 * 5 * Real.log (11 : Real) :=
  processionContribution_average 5 n (11 : Real) hn

#check processionContribution
#check sum_range_sq_succ
#check processionContribution_average
#check processionContribution_average_l
#check processionContribution_average_eleven

end LeanFormal.IUT.XiFPaper.Mzk1ProcessionContributionNumericsActual
end
