import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# shehdd A573: paper statement shape checks (chain-independent)

`PaperCor312Statement thetaLog qLog := qLog <= thetaLog` (signed readings),
and its equivalence with the `C_Theta` form: every `C` with
`thetaLog <= C * |log q|` satisfies `C >= -1`.

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312ShaStatementChecksActual

def PaperSignedStatement (thetaLog qLog : Real) : Prop := qLog ≤ thetaLog

def PaperCThetaForm (thetaLog absLogQ C : Real) : Prop :=
  thetaLog ≤ C * absLogQ

theorem signed_statement_iff_C (thetaLog absLogQ : Real) (hq : 0 < absLogQ) :
    PaperSignedStatement thetaLog (-absLogQ) ↔
      ∀ C : Real, PaperCThetaForm thetaLog absLogQ C → -1 ≤ C := by
  constructor
  · intro h C hC
    have h1 : -(absLogQ) ≤ C * absLogQ := le_trans h hC
    have h2 : (-1 : Real) ≤ (C * absLogQ) / absLogQ := (le_div_iff₀ hq).mpr h1
    have h3 : (C * absLogQ) / absLogQ = C :=
      mul_div_cancel_right₀ C (ne_of_gt hq)
    linarith
  · intro h
    have hle : thetaLog ≤ (thetaLog / absLogQ) * absLogQ := by
      rw [div_mul_cancel₀ _ (ne_of_gt hq)]
    have hdiv : -1 ≤ thetaLog / absLogQ := h _ hle
    have hmul : -(1 : Real) * absLogQ ≤ thetaLog := (le_div_iff₀ hq).mp hdiv
    calc -absLogQ = -(1 : Real) * absLogQ := by ring
      _ ≤ thetaLog := hmul

theorem signed_statement_of_magnitude {qMag thetaMag : Real}
    (h : thetaMag ≤ qMag) : -thetaMag ≤ -qMag := by linarith

end LeanFormal.IUT.XiFPaper.Mzk1Cor312ShaStatementChecksActual
