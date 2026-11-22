import LeanFormal.IUT.IUTIII.Corollary312.TateQPilotJComparison
import LeanFormal.IUT.Foundations.Geometry.TateJInvariantNorm

/-!
# ShehddQPilotNormInverseChainActual — q/j norm-inverse and exponential chain

New chain consequences of the compiled Tate q/j norm laws: the q-norm is the inverse
j-norm and the inverse prime, the exponentials of the negated log-volumes recover the
q-norm, and the two norms multiply to one at the log level.  No new assumptions, no
sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddQPilotNormInverseChainActual

open LeanFormal.IUT
open LeanFormal.IUT.TateCurvePadic

variable (l : PrimeGeFive) [Fact (Nat.Prime l.value)]

/-- **PROVED chain:** the q-norm is the inverse of the j-invariant norm. -/
theorem qNorm_eq_inv_jNorm :
    ‖q l‖ = (‖tateJInvariant l‖)⁻¹ := by
  rw [tateJInvariant_norm, inv_inv]

/-- **PROVED chain:** the q-norm is the inverse prime. -/
theorem qNorm_eq_inv_prime :
    ‖q l‖ = (l.value : ℝ)⁻¹ := q_norm_eq l

/-- **PROVED chain:** the exponential of the negated q-pilot log-volume is the q-norm. -/
theorem exp_neg_qPilotLogVolume :
    Real.exp (-qPilotLogVolume l) = ‖q l‖ := by
  rw [qPilotLogVolume_eq_neg_log_q_norm, neg_neg]
  exact Real.exp_log (q_norm_pos l)

/-- **PROVED chain:** the exponential of the negated j log-volume is also the q-norm. -/
theorem exp_neg_tateJInvariantLogVolume :
    Real.exp (-tateJInvariantLogVolume l) = ‖q l‖ := by
  rw [tateJInvariantLogVolume_eq_qPilotLogVolume]
  exact exp_neg_qPilotLogVolume l

/-- **PROVED chain:** the logarithms of the two norms sum to zero. -/
theorem log_qNorm_add_log_jNorm :
    Real.log ‖q l‖ + Real.log ‖tateJInvariant l‖ = 0 := by
  rw [tateJInvariant_norm, Real.log_inv]
  ring

end LeanFormal.IUT.XiFPaper.ShehddQPilotNormInverseChainActual
end
