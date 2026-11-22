import tmp.sheaf.xif.paper.S1372XCoordinateFormulaActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1377OmegaFormulaActual

open Polynomial
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1372XCoordinateFormulaActual
open WeierstrassCurve

variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve.Affine K)

lemma prePsi_four_eval {x y : K} (h : W.Nonsingular x y) :
    (W.preΨ 4).eval x =
      (W.a₁ * (2 * y + W.a₁ * x + W.a₃) + 2 * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y)) *
          (W.preΨ 3).eval x - (2 * y + W.a₁ * x + W.a₃) ^ 4 := by
  have hE : y ^ 2 + W.a₁ * x * y + W.a₃ * y -
      (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 :=
    (WeierstrassCurve.Affine.equation_iff' (W := W) x y).mp h.1
  rw [show W.preΨ 4 = W.preΨ₄ from by
        rw [show (4:ℤ) = ((4:ℕ):ℤ) by norm_num, WeierstrassCurve.preΨ_ofNat,
          WeierstrassCurve.preΨ'_four],
      show W.preΨ 3 = W.Ψ₃ from by
        rw [show (3:ℤ) = ((3:ℕ):ℤ) by norm_num, WeierstrassCurve.preΨ_ofNat,
          WeierstrassCurve.preΨ'_three]]
  simp only [WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat]
  linear_combination (norm := ring)
    (8 * (W.a₁ ^ 2 * x ^ 2 + 2 * W.a₁ * W.a₃ * x + 2 * W.a₁ * x * y + 2 * W.a₂ * x ^ 2 +
      W.a₃ ^ 2 + 2 * W.a₃ * y + 2 * W.a₄ * x + 2 * W.a₆ + 2 * x ^ 3 + 2 * y ^ 2)) * hE

end LeanFormal.IUT.XiFPaper.S1377OmegaFormulaActual
