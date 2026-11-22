import tmp.sheaf.xif.paper.S1687Torsion23RealizationActual
import LeanFormal.IUT.ABCBridge.Galois.EllipticTorsionAlgebraicity
import LeanFormal.IUT.ABCBridge.Galois.EllipticDivisionPolynomialEvaluation

/-! # S1700: exhaustion of the eight F-rational 3-torsion points

S1687 constructed the actual number field F = SplittingField S1687H and the
eight-point set `S1687EightPointSet` (six root points plus ± the rational
3-torsion point), but left `S1687ThreeTorsionOverFClassified` open.

This file proves the classification from the explicit Psi3 factorization:
* any F-rational 3-torsion point has x-coordinate a root of `S1667Curve.Ψ₃`;
* the roots are x = 25/16 and the roots of the residual cubic `S1687F`;
* for a residual-cubic root x, y^2 = G(x), and the identities
  `P(G(x)) = F(x) Q3(x)` and `A(G(x)) - x = F(x) Q4(x)` show that y is a root
  of H and x = A(y^2), so the point is one of the six root points;
* for x = 25/16 the point is ± the rational 3-torsion point.

No sorry, axiom, Nonempty or fake fill is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1700ThreeTorsionExhaustionActual

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual
open LeanFormal.IUT.XiFPaper.S1637D5TorsionClauseActual

local instance S1700FieldDecEq : DecidableEq S1687Field := Classical.decEq _

/-! ## 1. The polynomial identities for the inverse construction -/

/-- The quotient of P(G(x)) by F(x). -/
def S1700Q3 : ℚ[X] :=
  C 603979776 * X ^ 6 + C 15728640 * X ^ 5 - C 2252029952 * X ^ 4 +
    C 4832308480 * X ^ 3 + C 1029379456 * X ^ 2 - C 12524576400 * X +
    C 9845600625

/-- The quotient of A(G(x)) - x by F(x). -/
def S1700Q4 : ℚ[X] :=
  C (-(4096 : ℚ)/33958225) * X ^ 3 +
    C ((11392 : ℚ)/101874675) * X ^ 2 +
    C ((671 : ℚ)/6237225) * X +
    C (-(577 : ℚ)/1386050)

theorem S1700P_G_eval {K : Type*} [Field K] [Algebra ℚ K] [CharZero K] (x : K) :
    aeval (aeval x S1687G) S1687P =
      (aeval x S1687F) * (aeval x S1700Q3) := by
  unfold S1687P S1687F S1687G S1700Q3
  simp only [aeval_add, aeval_sub, aeval_mul, aeval_X, aeval_C, map_pow, map_ofNat]
  simp only [show ∀ q : ℚ, algebraMap ℚ K q = (q : K) from fun q => by
    rw [← map_ratCast (algebraMap ℚ K) q]; rfl]
  ring_nf

theorem S1700A_G_eval {K : Type*} [Field K] [Algebra ℚ K] [CharZero K] (x : K) :
    aeval (aeval x S1687G) S1687A =
      x + (aeval x S1687F) * (aeval x S1700Q4) := by
  unfold S1687A S1687F S1687G S1700Q4
  simp only [aeval_add, aeval_sub, aeval_mul, aeval_X, aeval_C, map_pow, map_ofNat]
  simp only [show ∀ q : ℚ, algebraMap ℚ K q = (q : K) from fun q => by
    rw [← map_ratCast (algebraMap ℚ K) q]; rfl]
  ring_nf

/-! ## 2. The y-coordinate equation and Psi3 roots -/

theorem S1700_y_sq {x y : S1687Field}
    (hns : S1687AffineF.Nonsingular x y) :
    y ^ 2 = aeval x S1687G := by
  have hEq : S1687AffineF.Equation x y := hns.1
  rw [WeierstrassCurve.Affine.equation_iff] at hEq
  unfold S1687AffineF S1687CurveF S1667Curve at hEq
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map, WeierstrassCurve.toAffine] at hEq
  simp only [show ∀ q : ℚ, algebraMap ℚ S1687Field q = (q : S1687Field) from fun q => by
    rw [← map_ratCast (algebraMap ℚ S1687Field) q]; rfl] at hEq
  unfold S1687G
  simp only [aeval_add, aeval_sub, aeval_mul, aeval_X, aeval_C, map_pow, map_ofNat]
  simp only [show ∀ q : ℚ, algebraMap ℚ S1687Field q = (q : S1687Field) from fun q => by
    rw [← map_ratCast (algebraMap ℚ S1687Field) q]; rfl]
  ring_nf at hEq ⊢
  linear_combination hEq

theorem S1700_psi3_root {x y : S1687Field}
    (hns : S1687AffineF.Nonsingular x y)
    (h3 : (3 : ℤ) •
      (Affine.Point.some (W' := S1687AffineF) x y hns : S1687AffineF.Point) = 0) :
    aeval x S1667Curve.Ψ₃ = 0 := by
  have hpsi := evalDivisionPolynomialAtPoint_three_eq_zero_of_three_nsmul_eq_zero
    (S1687CurveF) (Affine.Point.some (W' := S1687AffineF) x y hns) h3
  rw [evalDivisionPolynomialAtPoint_some,
    S1687CurveF.evalDivisionPolynomial_eq_eval_preΨ_of_odd hns.1
      (by decide : ¬ Even (3 : ℤ)),
    WeierstrassCurve.preΨ_three] at hpsi
  unfold S1687CurveF at hpsi
  simpa [WeierstrassCurve.baseChange, WeierstrassCurve.map_Ψ₃, Polynomial.eval_map,
    Polynomial.aeval_def] using hpsi

theorem S1700_x_root_or_rational {x y : S1687Field}
    (hns : S1687AffineF.Nonsingular x y)
    (h3 : (3 : ℤ) •
      (Affine.Point.some (W' := S1687AffineF) x y hns : S1687AffineF.Point) = 0) :
    x = algebraMap ℚ S1687Field (25/16) ∨ aeval x S1687F = 0 := by
  have hψ := S1700_psi3_root hns h3
  rw [S1687_Ψ3_eval_A] at hψ
  rcases mul_eq_zero.mp hψ with hfirst | hF
  · rcases mul_eq_zero.mp hfirst with h256 | hx
    · exact absurd h256 (by norm_num)
    · left
      have hx' : x = (25/16 : S1687Field) := sub_eq_zero.mp hx
      rw [hx']
      norm_num
  · right
    exact hF

theorem S1700_rootPoint_mem {x y : S1687Field}
    (hns : S1687AffineF.Nonsingular x y)
    (hF : aeval x S1687F = 0) :
    (Affine.Point.some (W' := S1687AffineF) x y hns : S1687AffineF.Point) ∈
      S1687RootPointSet := by
  have hy2 := S1700_y_sq hns
  have hH : aeval y S1687H = 0 := by
    rw [S1687H_eval_eq, hy2, S1700P_G_eval, hF, zero_mul]
  have hA : S1687Alpha y = x := by
    unfold S1687Alpha
    rw [hy2, S1700A_G_eval, hF, zero_mul, add_zero]
  refine ⟨y, hH, ?_⟩
  rw [S1687RootPoint_coords, Affine.Point.some.injEq]
  exact ⟨hA.symm, rfl⟩

theorem S1700_rational_mem {x y : S1687Field}
    (hns : S1687AffineF.Nonsingular x y)
    (hx : x = algebraMap ℚ S1687Field (25/16)) :
    (Affine.Point.some (W' := S1687AffineF) x y hns : S1687AffineF.Point) =
        S1687RationalP ∨
      (Affine.Point.some (W' := S1687AffineF) x y hns : S1687AffineF.Point) =
        -S1687RationalP := by
  have hY := WeierstrassCurve.Affine.Y_eq_of_X_eq
    (W := S1687AffineF) hns.1 S1687RationalP_nonsingular.1 hx
  rcases hY with hy | hy
  · left
    rw [S1687RationalP_coords, Affine.Point.some.injEq]
    exact ⟨hx, hy⟩
  · right
    rw [S1687RationalP_coords, Affine.Point.neg_some, Affine.Point.some.injEq]
    exact ⟨hx, hy⟩

theorem S1700_nonzero_classified (P : S1687AffineF.Point)
    (h3 : (3 : ℤ) • P = 0) (hP0 : P ≠ 0) :
    P ∈ S1687EightPointSet := by
  cases P with
  | zero => exact (hP0 rfl).elim
  | some x y hns =>
    rcases S1700_x_root_or_rational hns h3 with hx | hF
    · rcases S1700_rational_mem hns hx with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · exact Or.inl (S1700_rootPoint_mem hns hF)

/-- The original S1687 classification is false as stated: it omits the zero
point, which is 3-torsion but is not in the eight-point affine set. -/
theorem S1700_original_classified_false :
    ¬ S1687ThreeTorsionOverFClassified := by
  intro h
  have h0 : (0 : S1687AffineF.Point) ∈ S1687EightPointSet := h 0 (zsmul_zero 3)
  rcases h0 with hroot | hrat
  · rcases hroot with ⟨r, hr, hEq⟩
    have hne : S1687RootPoint r hr ≠ 0 := by
      simpa [S1687RootPoint] using
        (Affine.Point.some_ne_zero (W' := S1687AffineF)
          (S1687Root_nonsingular r hr))
    exact hne hEq.symm
  · rcases hrat with hEq | hEq
    · have hne : S1687RationalP ≠ 0 := by
        simpa [S1687RationalP] using
          (Affine.Point.some_ne_zero (W' := S1687AffineF)
            S1687RationalP_nonsingular)
      exact hne hEq.symm
    · have hne : -S1687RationalP ≠ 0 := by
        have hpos : S1687RationalP ≠ 0 := by
          simpa [S1687RationalP] using
            (Affine.Point.some_ne_zero (W' := S1687AffineF)
              S1687RationalP_nonsingular)
        exact neg_ne_zero.mpr hpos
      exact hne hEq.symm

theorem S1700_classified_nonzero :
    ∀ P : S1687AffineF.Point, (3 : ℤ) • P = 0 → P ≠ 0 →
      P ∈ S1687EightPointSet := S1700_nonzero_classified

end LeanFormal.IUT.XiFPaper.S1700ThreeTorsionExhaustionActual
end
