import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Stage-4 host: Corollary 2.2 conditions (C1),(C2) shapes (definitional)

TEXT: papers/motizuki_corpus/text/Inter-universal Teichmuller Theory IV.txt,
Corollary 2.2, (ii) conditions (C1),(C2) p.2475-2493:
(C1) (log(q-forall))^(1/2) <= l <= 10*delta*(log(q-forall))^(1/2)*log(2*delta*log(q-forall));
(C2) (1/6)log(q) <= (1/6)log(q-non2) <= (1/6)log(q-forall)
     <= (1+eps_E)(log-diff_X(x_E) + log-cond_D(x_E)) + C_K,
with eps_E = (60*delta)^2 * log(2*delta*(log(q-forall))) / (log(q-forall))^(1/2).

CONSUMER: mainline's Cor 2.2 statement slot. Definitional shapes only.

LABEL: statement shapes (class A definitions of class B targets). Registry frozen;
new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136Cor22ConditionsShapeActual

/-- Condition (C1) of Cor 2.2: the prime l is chosen in the prescribed window. -/
noncomputable def LGPC1Shape (ell : ℕ) (logq delta : ℝ) : Prop :=
  Real.sqrt logq ≤ (ell : ℝ) ∧
    (ell : ℝ) ≤ 10 * delta * Real.sqrt logq * Real.log (2 * delta * Real.log logq)

/-- The epsilon_E invariant of Cor 2.2. -/
noncomputable def LGPEpsilonEShape (logq delta : ℝ) : ℝ :=
  (60 * delta) ^ 2 * Real.log (2 * delta * Real.log logq) / Real.sqrt logq

/-- Condition (C2) of Cor 2.2: the chain of logarithmic inequalities. -/
noncomputable def LGPC2Shape (logq logqNon2 logqForall logDiff logCond C_K epsE : ℝ) : Prop :=
  (1 / 6) * logq ≤ (1 / 6) * logqNon2 ∧
    (1 / 6) * logqNon2 ≤ (1 / 6) * logqForall ∧
      (1 / 6) * logqForall ≤ (1 + epsE) * (logDiff + logCond) + C_K

/-- Unfolding lemma for condition (C1). -/
theorem LGPC1Shape_iff (ell : ℕ) (logq delta : ℝ) :
    LGPC1Shape ell logq delta ↔
      (Real.sqrt logq ≤ (ell : ℝ) ∧
        (ell : ℝ) ≤ 10 * delta * Real.sqrt logq * Real.log (2 * delta * Real.log logq)) :=
  Iff.rfl

/-- Unfolding lemma for epsilon_E. -/
theorem LGPEpsilonEShape_eq (logq delta : ℝ) :
    LGPEpsilonEShape logq delta =
      (60 * delta) ^ 2 * Real.log (2 * delta * Real.log logq) / Real.sqrt logq := rfl

/-- Unfolding lemma for condition (C2). -/
theorem LGPC2Shape_iff (logq logqNon2 logqForall logDiff logCond C_K epsE : ℝ) :
    LGPC2Shape logq logqNon2 logqForall logDiff logCond C_K epsE ↔
      ((1 / 6) * logq ≤ (1 / 6) * logqNon2 ∧
        (1 / 6) * logqNon2 ≤ (1 / 6) * logqForall ∧
          (1 / 6) * logqForall ≤ (1 + epsE) * (logDiff + logCond) + C_K) :=
  Iff.rfl

#check LGPC1Shape_iff
#check LGPEpsilonEShape_eq
#check LGPC2Shape_iff

end LeanFormal.IUT.XiFPaper.S3136Cor22ConditionsShapeActual
end