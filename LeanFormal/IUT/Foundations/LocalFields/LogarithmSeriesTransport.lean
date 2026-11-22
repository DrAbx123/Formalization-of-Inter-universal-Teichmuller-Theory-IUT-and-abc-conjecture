import LeanFormal.IUT.Foundations.LocalFields.LogarithmSeries

/-!
# Continuity, rather than isometry, transports the actual logarithm series

The target norm may use a different positive normalization. Mapping the
proved convergent sum gives the target sum directly; no target normed
Qp-algebra assumption is needed.
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable {p : ℕ} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra ℚ_[p] K]

include localNormedAlgebra in
theorem log1p_map_of_continuous {L : Type*} [NormedField L]
    (e : K →+* L) (he : Continuous e) (x : K) (hx : ‖x‖ < 1) :
    e (log1p x) = log1p (e x) := by
  have hm := (negativeLogSeries_hasSum (p := p) x hx).map e.toAddMonoidHom he
  change HasSum (fun n => e (negativeLogTerm x n)) (e (negativeLogSeries x)) at hm
  have hterm : (fun n => e (negativeLogTerm x n)) =
      fun n => negativeLogTerm (e x) n := by
    funext n
    simp only [negativeLogTerm, map_div₀, map_mul, map_pow, map_neg, map_one,
      map_add, map_natCast]
  rw [hterm] at hm
  have hsum : e (negativeLogSeries x) = negativeLogSeries (e x) := hm.tsum_eq.symm
  unfold log1p
  rw [map_neg, hsum]

end LeanFormal.IUT.LocalFieldLogarithm
