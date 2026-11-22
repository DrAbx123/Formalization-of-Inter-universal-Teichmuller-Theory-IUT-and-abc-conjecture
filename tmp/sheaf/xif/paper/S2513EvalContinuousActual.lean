import tmp.sheaf.xif.paper.S2433ReverseEvalActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2481CoeffLimitActual
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual

namespace LeanFormal.IUT.XiFPaper.S2513EvalContinuousActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-- Continuity of the finite-level evaluation map on the cyclotome. -/
theorem S2481Eval_continuous (n : ℕ+) :
    Continuous (fun f : PsiCnsCyclotome p => S2481Eval (p := p) f n) := by
  apply Continuous.subtype_mk
  · exact KummerCyclotome.continuous_eval_discrete
      (Multiplicative.ofAdd (((1 : ℚ) / (n : ℚ) : ℚ) : AddCircle (1 : ℚ)))

end LeanFormal.IUT.XiFPaper.S2513EvalContinuousActual
end