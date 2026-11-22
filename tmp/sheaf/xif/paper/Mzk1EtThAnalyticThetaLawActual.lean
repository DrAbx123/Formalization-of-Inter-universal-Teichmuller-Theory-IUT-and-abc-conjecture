import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceThetaGenerator

/-!
# Mzk1EtThAnalyticThetaLawActual — derived analytic-theta laws from the Example36 analytic
theta carrier (new theorems: HasSum/transport iteration/preservation of the convergence
range). No copies/bookkeeping; no axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1EtThAnalyticThetaLawActual

open LeanFormal.IUT

/-- Derived: the concrete analytic q-expansion is the Jacobi theta HasSum. -/
theorem concrete_analyticTheta_hasSum :
    HasSum
      (fun n : ℤ =>
        ((analyticThetaQExpansion analyticThetaCarrierConcrete n : ℝ) : ℂ))
      jacobiThetaQ :=
  analyticThetaQExpansion_concrete_hasSum

/-- Derived: concrete q-expansion coefficients are the Jacobi qExpansion terms. -/
theorem concrete_coeff_eq_qExpansionTerm (n : ℤ) :
    ((analyticThetaQExpansion analyticThetaCarrierConcrete n : ℝ) : ℂ) =
      qExpansionTerm n :=
  analyticThetaQExpansion_concrete_eq n

/-- Derived: the q-parameter transport by squaring preserves the convergence range. -/
theorem transport_q_mem (t : AnalyticThetaCarrier) :
    0 < (analyticThetaTransport t).q ∧ (analyticThetaTransport t).q < 1 :=
  ⟨(analyticThetaTransport t).q_pos, (analyticThetaTransport t).q_lt_one⟩

/-- Derived: iterating the squaring transport k times raises q to the 2^k power. -/
theorem transport_iterate_q (t : AnalyticThetaCarrier) (k : ℕ) :
    (Nat.iterate analyticThetaTransport k t).q = t.q ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', analyticThetaTransport, ih, pow_mul]
      ring_nf

#check concrete_analyticTheta_hasSum
#check concrete_coeff_eq_qExpansionTerm
#check transport_q_mem
#check transport_iterate_q

end LeanFormal.IUT.XiFPaper.Mzk1EtThAnalyticThetaLawActual
end
