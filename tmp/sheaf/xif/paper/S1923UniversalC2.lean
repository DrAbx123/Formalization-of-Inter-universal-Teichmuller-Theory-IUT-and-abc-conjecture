import tmp.sheaf.xif.paper.S1923UniversalC1

set_option maxHeartbeats 1000000

noncomputable section
open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
namespace Universal

open Coeff

lemma cusp_ψ₂ : cusp.ψ₂ = 2 * Y := by
  simp [cusp, WeierstrassCurve.ψ₂, Affine.polynomialY]
  rfl

lemma cusp_Ψ₃ : cusp.Ψ₃ = 3 * (Polynomial.X : Polynomial ℤ) ^ 4 := by
  simp [cusp, WeierstrassCurve.Ψ₃, b₂, b₄, b₆, b₈]

lemma cusp_preΨ₄ : cusp.preΨ₄ = 2 * (Polynomial.X : Polynomial ℤ) ^ 6 := by
  simp [cusp, WeierstrassCurve.preΨ₄, b₂, b₄, b₆, b₈]

lemma polyEval_cusp_ψ (n : ℤ) : polyEval cusp 1 1 (curve.ψ n) = n := by
  rw [polyEval_apply, ← map_ψ]
  have hmap : (map curve (specialize cusp)) = cusp := map_specialize cusp
  rw [hmap]
  rw [show cusp.ψ n = normEDS cusp.ψ₂ (Polynomial.C cusp.Ψ₃) (Polynomial.C cusp.preΨ₄) n from rfl]
  change Polynomial.evalEvalRingHom (1 : ℤ) (1 : ℤ)
    (normEDS cusp.ψ₂ (Polynomial.C cusp.Ψ₃) (Polynomial.C cusp.preΨ₄) (n : ℤ)) = n
  rw [map_normEDS (f := Polynomial.evalEvalRingHom (1 : ℤ) (1 : ℤ))]
  simp only [cusp_ψ₂, cusp_Ψ₃, cusp_preΨ₄]
  norm_num [Polynomial.evalEval, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_mul,
    Polynomial.eval_pow]
  rw [normEDS_two_three_two]

lemma polyToField_ψ_ne_zero {n : ℤ} (h0 : n ≠ 0) : polyToField (curve.ψ n) ≠ 0 := by
  intro h
  have h' : AdjoinRoot.mk curve.polynomial (curve.ψ n) = 0 := by
    apply IsFractionRing.injective Universal.Ring Universal.Field
    simpa [polyToField_apply] using h
  have h2 := congrArg (ringEval cusp_equation_one_one) h'
  rw [ringEval_mk, polyEval_cusp_ψ, map_zero] at h2
  exact h0 h2

end Universal
end WeierstrassCurve
