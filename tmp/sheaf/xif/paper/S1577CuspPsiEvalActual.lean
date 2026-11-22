import tmp.sheaf.xif.paper.S1573CuspPolyEvalActual
noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
namespace WeierstrassCurve
theorem polyEvalCusp_ψ₂ : polyEvalCusp (Universal.curve.ψ₂) = 2 := by
  simp [polyEvalCusp, specializeCusp, Universal.curve, WeierstrassCurve.ψ₂,
    WeierstrassCurve.Affine.polynomialY, map_ofNat]
theorem polyEvalCusp_Ψ₃ : polyEvalCusp (C Universal.curve.Ψ₃) = 3 := by
  simp [polyEvalCusp, specializeCusp, Universal.curve, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈,
    map_ofNat]
theorem polyEvalCusp_preΨ₄ : polyEvalCusp (C Universal.curve.preΨ₄) = 2 := by
  simp [polyEvalCusp, specializeCusp, Universal.curve, WeierstrassCurve.preΨ₄,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈,
    map_ofNat]
theorem polyEvalCusp_ψ (n : ℤ) : polyEvalCusp (Universal.curve.ψ n) = n := by
  rw [show Universal.curve.ψ n =
      normEDS (Universal.curve.ψ₂) (C Universal.curve.Ψ₃) (C Universal.curve.preΨ₄) n from rfl]
  rw [map_normEDS, polyEvalCusp_ψ₂, polyEvalCusp_Ψ₃, polyEvalCusp_preΨ₄]
  exact normEDS_two_three_two n
theorem polyEvalCusp_curvePolynomial :
    polyEvalCusp (Universal.curve.toAffine.polynomial) = 0 := by
  simp [polyEvalCusp, specializeCusp, Universal.curve,
    WeierstrassCurve.Affine.polynomial, map_ofNat]
noncomputable def innerEvalCusp : Polynomial (MvPolynomial Coeff ℤ) →+* ℤ :=
  Polynomial.eval₂RingHom specializeCusp 1
noncomputable def ringEvalCusp : Universal.Ring →+* ℤ :=
  AdjoinRoot.lift innerEvalCusp 1 (by
    simpa [polyEvalCusp, innerEvalCusp] using polyEvalCusp_curvePolynomial)
theorem ringEvalCusp_mk (p : Universal.Poly) :
    ringEvalCusp (AdjoinRoot.mk Universal.curve.toAffine.polynomial p) =
      polyEvalCusp p := by
  simpa [ringEvalCusp, innerEvalCusp, polyEvalCusp] using
    (AdjoinRoot.lift_mk (f := Universal.curve.toAffine.polynomial)
      (i := innerEvalCusp) (a := 1) _ p)
theorem S1573CuspPsiEval_holds : S1573CuspPsiEval :=
  polyEvalCusp_ψ
open Universal in
theorem polyToField_ψ_ne_zero (n : ℤ) (h0 : n ≠ 0) :
    polyToField (curve.toAffine.ψ n) ≠ 0 := by
  intro h
  rw [polyToField_apply] at h
  have hring : polyToRing (curve.toAffine.ψ n) = 0 := by
    exact (map_eq_zero_iff (algebraMap Ring Field)
      (IsFractionRing.injective Ring Field)).mp h
  have h2 := congrArg ringEvalCusp hring
  rw [map_zero] at h2
  change ringEvalCusp
      (AdjoinRoot.mk curve.toAffine.polynomial (curve.toAffine.ψ n)) = 0 at h2
  rw [ringEvalCusp_mk, polyEvalCusp_ψ] at h2
  exact h0 h2
end WeierstrassCurve
end
