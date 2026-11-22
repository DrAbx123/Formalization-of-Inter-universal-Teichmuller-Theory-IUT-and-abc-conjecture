import LeanFormal.IUT.Foundations.LocalFields.LogarithmLocalInverse

/-!
# ShehddLocalLogInverseConsumerActual — local logarithm inverse/preimage consumer

Consumer chain over LogarithmLocalInverse with the prime `p` as an explicit parameter (so
the NormedAlgebra instance is determined by the caller): closed-ball log1p preimage, source
scale bounds, integral-unit offset, principal-unit log surjectivity, and the integer ring
inside the constructed integral log-shell.  No sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddLocalLogInverseConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K] [IsUltrametricDist K]

/-- **PROVED consumer:** every sufficiently small closed ball around 0 is in the image
of log1p on the same ball. -/
theorem log1p_preimage_consumer (p : Nat) [Fact p.Prime] [NormedAlgebra ℚ_[p] K]
    {r : Real} (hr : 0 ≤ r) (hrhalf : r < 1 / 2) (y : K) (hy : ‖y‖ ≤ r) :
    ∃ x : K, ‖x‖ ≤ r ∧ log1p x = y :=
  exists_log1p_preimage hr hrhalf y hy

/-- **PROVED consumer:** the source scale p* is smaller than 1/2 and positive. -/
theorem logShellScale_bounds_consumer (p : Nat) [Fact p.Prime]
    [NormedAlgebra ℚ_[p] K] :
    ‖(logShellScale p : K)‖ < 1 / 2 ∧ 0 < logShellScale p :=
  ⟨norm_logShellScale_lt_half (K := K) (p := p), logShellScale_pos (p := p)⟩

/-- **PROVED consumer:** small offsets of one have norm one (integral units). -/
theorem norm_one_add_consumer (x : K) (hx : ‖x‖ < 1) : ‖1 + x‖ = 1 :=
  norm_one_add_of_norm_lt_one x hx

/-- **PROVED consumer:** every integer-ring element is p* times the logarithm of an
actual principal unit. -/
theorem unitLog_surjective_consumer (p : Nat) [Fact p.Prime]
    [NormedAlgebra ℚ_[p] K] [ProperSpace K] (x : Integers K) :
    ∃ u : (Integers K)ˣ, u ∈ principalUnits ∧
      unitLog u = (logShellScale p : K) * (x : K) :=
  exists_unitLog_eq_scale_mul x

/-- **PROVED consumer:** the integer ring is contained in the constructed integral
log-shell. -/
theorem integers_subset_integralLogShell_consumer (p : Nat) [Fact p.Prime]
    [NormedAlgebra ℚ_[p] K] [ProperSpace K] :
    (Integers K : Set K) ⊆ (integralLogShell (K := K) (p := p) : Set K) :=
  integers_subset_integralLogShell (K := K) (p := p)

end LeanFormal.IUT.XiFPaper.ShehddLocalLogInverseConsumerActual
end
