/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-! # A540 (narrow import): Cor 3.12 statement shape (IUT III:10324-10353) — statement/self-check file -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312StatementShapeActual

/-- The exact paper statement shape: with `minusAbsLogTheta = -|log Theta|`,
`minusAbsLogQ = -|log q|`, the conclusion is `minusAbsLogTheta >= minusAbsLogQ`
(l. 10351-10353), i.e. `C >= -1` for any real `C` with
`-|log Theta| <= C * |log q|`. -/
def PaperCor312Statement (minusAbsLogTheta minusAbsLogQ : ℝ) : Prop :=
  minusAbsLogTheta ≥ minusAbsLogQ

/-- The paper's `C >= -1` formulation with `|log q| > 0` (l. 10351-10353). -/
def PaperCThetaForm (minusAbsLogTheta absLogQ C : ℝ) : Prop :=
  minusAbsLogTheta ≤ C * absLogQ

/-- The paper's `C >= -1` form: `-|log Θ| ≥ -|log q|` is equivalent to the
condition that every `C` with `-|log Θ| ≤ C * |log q|` satisfies `C ≥ -1`
(the `C = -1` instance of the display is the boundary, not an equality of forms). -/
theorem paper_statement_iff_C (minusAbsLogTheta absLogQ : ℝ) (hq : 0 < absLogQ) :
    PaperCor312Statement minusAbsLogTheta (-absLogQ) ↔
      ∀ C : ℝ, minusAbsLogTheta ≤ C * absLogQ → -1 ≤ C := by
  constructor
  · intro h C hC
    have h1 : -(absLogQ) ≤ C * absLogQ := le_trans h hC
    have h2 : (-1 : ℝ) ≤ (C * absLogQ) / absLogQ := (le_div_iff₀ hq).mpr h1
    have h3 : (C * absLogQ) / absLogQ = C := mul_div_cancel_right₀ C (ne_of_gt hq)
    linarith [h2, h3]
  · intro h
    have hle : minusAbsLogTheta ≤
        (minusAbsLogTheta / absLogQ) * absLogQ := by
      rw [div_mul_cancel₀ _ (ne_of_gt hq)]
    have hdiv : -1 ≤ minusAbsLogTheta / absLogQ := h _ hle
    have hmul : -(1 : ℝ) * absLogQ ≤ minusAbsLogTheta := (le_div_iff₀ hq).mp hdiv
    linarith

/-- The trivial branch recorded by the paper (l. 10354-10358): if
`-|log Theta| >= 0` then the conclusion follows from `-|log q| < 0`. -/
theorem trivial_branch (minusAbsLogTheta minusAbsLogQ : ℝ) (h0 : 0 ≤ minusAbsLogTheta)
    (hq : minusAbsLogQ < 0) : PaperCor312Statement minusAbsLogTheta minusAbsLogQ :=
  le_of_lt (lt_of_lt_of_le hq h0)

/-- The nontrivial branch assumption `-|log Theta| < 0` (l. 10354-10358). -/
def NontrivialBranch (minusAbsLogTheta : ℝ) : Prop :=
  minusAbsLogTheta < 0

end LeanFormal.IUT.XiFPaper.Mzk1Cor312StatementShapeActual
