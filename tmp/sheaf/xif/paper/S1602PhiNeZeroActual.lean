import tmp.sheaf.xif.paper.S1601ZSMulPointFormulaActual
import tmp.sheaf.xif.paper.S1577CuspPsiEvalActual
noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
namespace WeierstrassCurve.Universal
theorem s1602PolyEvalCusp_C_X :
    polyEvalCusp (C (Polynomial.X : Polynomial (MvPolynomial Coeff ℤ))) = 1 := by
  simp [polyEvalCusp, specializeCusp]
theorem s1602PolyEvalCusp_φ (n : ℤ) :
    polyEvalCusp (curve.toAffine.φ n) = 1 := by
  rw [show curve.toAffine.φ n = C Polynomial.X * curve.toAffine.ψ n ^ 2 -
      curve.toAffine.ψ (n + 1) * curve.toAffine.ψ (n - 1) from rfl]
  rw [map_sub (polyEvalCusp), map_mul (polyEvalCusp), map_pow (polyEvalCusp),
    s1602PolyEvalCusp_C_X, polyEvalCusp_ψ]
  rw [map_mul (polyEvalCusp), polyEvalCusp_ψ, polyEvalCusp_ψ]
  ring
theorem s1602PolyToField_φ_ne_zero (n : ℤ) :
    polyToField (curve.toAffine.φ n) ≠ 0 := by
  intro h
  rw [polyToField_apply] at h
  have hring : polyToRing (curve.toAffine.φ n) = 0 := by
    exact (map_eq_zero_iff (algebraMap Ring Field)
      (IsFractionRing.injective Ring Field)).mp h
  have h2 := congrArg ringEvalCusp hring
  rw [map_zero] at h2
  change ringEvalCusp
      (AdjoinRoot.mk curve.toAffine.polynomial (curve.toAffine.φ n)) = 0 at h2
  rw [ringEvalCusp_mk, s1602PolyEvalCusp_φ] at h2
  exact one_ne_zero h2
theorem s1602SmulX_zero : smulX 0 = 0 := by
  simp [smulX, WeierstrassCurve.φ_zero, WeierstrassCurve.ψ_zero]
theorem s1602SmulX_ne_zero (n : ℤ) (h0 : n ≠ 0) : smulX n ≠ 0 :=
  div_ne_zero (s1602PolyToField_φ_ne_zero n)
    (pow_ne_zero _ (polyToField_ψ_ne_zero n h0))
theorem s1602SmulX_ne_smulX (m n : ℤ) (ne : m ≠ n) (ne_neg : m ≠ -n) :
    smulX m ≠ smulX n := by
  obtain rfl | hm := eq_or_ne m 0
  · rw [s1602SmulX_zero]
    exact (s1602SmulX_ne_zero n ne.symm).symm
  obtain rfl | hn := eq_or_ne n 0
  · rw [s1602SmulX_zero]
    exact s1602SmulX_ne_zero m ne
  rw [← sub_ne_zero, smulX_sub_smulX m n hm hn]
  rw [ne_comm, ← sub_ne_zero] at ne
  rw [Ne, ← add_eq_zero_iff_eq_neg, add_comm] at ne_neg
  refine div_ne_zero (mul_ne_zero ?_ ?_)
    (pow_ne_zero _ <| mul_ne_zero ?_ ?_) <;>
    apply polyToField_ψ_ne_zero <;> assumption
theorem s1602SmulX_eq_smulX_iff (m n : ℤ) :
    smulX m = smulX n ↔ m = n ∨ m = -n := by
  refine ⟨fun h => ?_, ?_⟩
  · contrapose! h
    exact s1602SmulX_ne_smulX m n h.1 h.2
  · rintro (rfl | rfl)
    · exact rfl
    · exact smulX_neg n
end WeierstrassCurve.Universal

end
