import tmp.sheaf.xif.paper.PaperScopeLemma24Actual

/-! Mainline (B4c / StepProvider f5 ingredient): real composition laws for the P1
  polynomial evaluation map and the derivative chain rule on Qbar points. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1F0CompositionChainActual

open LeanFormal.IUT.XiFPaper.PaperScopeLemma24Actual

theorem polyEvalP1K_comp (f g : Polynomial F) (p : P1Point F) :
    polyEvalP1K (g.comp f) p = polyEvalP1K g (polyEvalP1K f p) := by
  cases p with
  | none => rfl
  | some x =>
      simp [polyEvalP1K, Polynomial.eval_comp]

theorem aeval_derivative_comp (f g : Polynomial F) (z : F) :
    Polynomial.aeval z (Polynomial.derivative (g.comp f)) =
      Polynomial.aeval (Polynomial.aeval z f) (Polynomial.derivative g) *
        Polynomial.aeval z (Polynomial.derivative f) := by
  rw [Polynomial.derivative_comp, Polynomial.aeval_mul, Polynomial.aeval_comp]

end LeanFormal.IUT.XiFPaper.Mzk1F0CompositionChainActual