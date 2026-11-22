import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume

/-!
# ShehddQCandidatePowChainActual — q-candidate power contraction chain

New chain consequences of the candidate data and q-norm estimates: every positive power of
a q-candidate is nonzero and still contracting.  No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddQCandidatePowChainActual

open LeanFormal.IUT
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.NumberFieldFinitePlace

variable {K : Type*} [Field K] [NumberField K]
variable {place : NumberField.FinitePlace K}

/-- **PROVED chain:** a positive power of a q-candidate is nonzero and contracting. -/
theorem qCandidate_pow_chain (parameter : FinitePlaceQCandidate place)
    (n : Nat) (hn : 0 < n) :
    parameter.q ^ n ≠ 0 ∧ ‖parameter.q ^ n‖ < 1 := by
  refine ⟨pow_ne_zero n parameter.q_ne_zero, ?_⟩
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) (qNorm_lt_one parameter)
    (Nat.pos_iff_ne_zero.mp hn)

/-- **PROVED chain:** the power candidate inherits nonzero/contracting data, and its
norm power equals the power of the norm. -/
theorem qCandidate_pow_norm_chain (parameter : FinitePlaceQCandidate place)
    (n : Nat) (hn : 0 < n) :
    ‖parameter.q ^ n‖ = ‖parameter.q‖ ^ n ∧
      0 < ‖parameter.q ^ n‖ :=
  ⟨norm_pow parameter.q n, norm_pos_iff.mpr (pow_ne_zero n parameter.q_ne_zero)⟩

end LeanFormal.IUT.XiFPaper.ShehddQCandidatePowChainActual
end