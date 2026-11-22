import LeanFormal.IUT.Foundations.Geometry.TateCurvePadicEstimates

/-!
# ShehddQNormPowerChainActual — Tate q-norm power-decay chain

New chain consequences of the compiled q-norm estimates: the q-norm is a positive inverse
prime below one, its logarithm recovers it under exp, and its powers strictly decrease
with the exponent.  No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddQNormPowerChainActual

open LeanFormal.IUT
open LeanFormal.IUT.TateCurvePadic

variable (l : PrimeGeFive) [Fact (Nat.Prime l.value)]

/-- **PROVED chain:** the q-norm is positive, below one, and equals the inverse prime. -/
theorem qNorm_bounds_chain :
    0 < ‖q l‖ ∧ ‖q l‖ < 1 ∧ ‖q l‖ = (l.value : ℝ)⁻¹ :=
  ⟨q_norm_pos l, q_norm_lt_one l, q_norm_eq l⟩

/-- **PROVED chain:** exponentiating the log of the q-norm recovers the q-norm. -/
theorem exp_log_qNorm_chain :
    Real.exp (Real.log ‖q l‖) = ‖q l‖ :=
  Real.exp_log (q_norm_pos l)

/-- **PROVED chain:** powers of the q-norm strictly decrease as the exponent grows. -/
theorem qNorm_pow_succ_lt_chain (n : Nat) :
    ‖q l‖ ^ (n + 1) < ‖q l‖ ^ n := by
  have hqpos : 0 < ‖q l‖ := q_norm_pos l
  have hq1 : ‖q l‖ < 1 := q_norm_lt_one l
  calc ‖q l‖ ^ (n + 1) = ‖q l‖ ^ n * ‖q l‖ := by ring
    _ < ‖q l‖ ^ n * 1 := by
        exact mul_lt_mul_of_pos_left hq1 (pow_pos hqpos n)
    _ = ‖q l‖ ^ n := by ring

end LeanFormal.IUT.XiFPaper.ShehddQNormPowerChainActual
end
