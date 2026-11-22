import LeanFormal.IUT.IUTIII.Corollary312.TateQPilotJComparison

/-!
# ShehddQPilotExpChainActual — q-pilot log-volume exponential chain

Real chain theorems derived from the compiled q-pilot/j-invariant log-volume laws
(TateQPilotJComparison): exponentiate the log-volumes, identify the prime value and
combine the two volumes additively.  These are new consequences (the tree only states
the log-volume identities); no new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddQPilotExpChainActual

open LeanFormal.IUT
open LeanFormal.IUT.TateCurvePadic

variable (l : PrimeGeFive) [Fact (Nat.Prime l.value)]

/-- **PROVED chain:** the exponential of the q-pilot log-volume is the prime `l.value`. -/
theorem qPilotLogVolume_exp_eq_prime :
    Real.exp (qPilotLogVolume l) = (l.value : ℝ) := by
  rw [qPilotLogVolume_eq_log_prime]
  exact Real.exp_log (by exact_mod_cast (Fact.out : Nat.Prime l.value).pos)

/-- **PROVED chain:** the exponential of the Tate j-invariant log-volume is its norm. -/
theorem tateJInvariantLogVolume_exp_eq_norm :
    Real.exp (tateJInvariantLogVolume l) = ‖tateJInvariant l‖ :=
  Real.exp_log (tateJInvariant_norm_pos l)

/-- **PROVED chain:** the two log-volumes add to `2 * log (l.value)`. -/
theorem qPilotLogVolume_add_tateJInvariantLogVolume :
    qPilotLogVolume l + tateJInvariantLogVolume l =
      2 * Real.log (l.value : ℝ) := by
  rw [qPilotLogVolume_eq_log_prime, tateJInvariantLogVolume_eq_log_prime]
  ring

/-- **PROVED chain:** exponentiating the sum gives the product of the prime and the
j-invariant norm. -/
theorem exp_add_eq_prime_mul_norm :
    Real.exp (qPilotLogVolume l + tateJInvariantLogVolume l) =
      (l.value : ℝ) * ‖tateJInvariant l‖ := by
  rw [Real.exp_add, qPilotLogVolume_exp_eq_prime,
    tateJInvariantLogVolume_exp_eq_norm]

/-- **PROVED chain:** the q-pilot log-volume is positive and its exponential exceeds one
(`l.value ≥ 5`). -/
theorem one_lt_exp_qPilotLogVolume :
    1 < Real.exp (qPilotLogVolume l) := by
  rw [qPilotLogVolume_exp_eq_prime]
  have h : (5 : ℝ) ≤ (l.value : ℝ) := by exact_mod_cast l.ge_five
  linarith

end LeanFormal.IUT.XiFPaper.ShehddQPilotExpChainActual
end
