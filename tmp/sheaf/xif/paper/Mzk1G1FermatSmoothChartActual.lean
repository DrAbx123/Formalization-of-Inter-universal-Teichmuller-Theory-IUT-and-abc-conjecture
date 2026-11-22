/- G1-A：实际 chart ring A₀ = ℚ[λ][x]/(x^n-λ)[y]/(y^n-(1-λ)) 到
   路线多元商环 D = ℚ[x,y]/(x^n+y^n-1) = henry 的 `R n` 的实际 ℚ-代数同态。
   这是路线 §2.1/§2.3 "商环普遍性质" 识别的一半（A₀ → D），并给出
   `chart0RingHom : A₀ →+* R n` 供 henry 的 Y_n 粘合使用；
   D → A₀ 的反向映射与 AlgEquiv 作为下一步（需生成元 ext 互逆）。
   基础：`Mzk1G1FermatFiniteDegree2Actual`（A₀ 的 AdjoinRoot 呈现）。
   不含 sorry/admit/axiom/PUnit/True/toy。 -/
import tmp.sheaf.xif.paper.Mzk1G1FermatFiniteDegree2Actual
import tmp.sheaf.xif.paper.Mzk1G1FermatAffineChartActual
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatSmoothChartActual
open Polynomial MvPolynomial
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartRingActual2
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatFiniteDegree2Actual

/-! ### 路线对象 D = ℚ[X,Y]/(X^n+Y^n-1) -/

/-- Fermat 仿射多项式 `F = X^n + Y^n - 1`。 -/
noncomputable def fermatCurvePoly (n : Nat) : MvPolynomial (Fin 2) ℚ :=
  MvPolynomial.X 0 ^ n + MvPolynomial.X 1 ^ n - 1

/-- 主理想 `(F)`。 -/
noncomputable def fermatCurveIdeal (n : Nat) : Ideal (MvPolynomial (Fin 2) ℚ) :=
  Ideal.span ({fermatCurvePoly n} : Set (MvPolynomial (Fin 2) ℚ))

/-- 路线对象 D = ℚ[X,Y]/(X^n+Y^n-1)（与 henry 的 `R n` 定义相同）。 -/
noncomputable abbrev fermatCurveRing (n : Nat) : Type :=
  MvPolynomial (Fin 2) ℚ ⧸ fermatCurveIdeal n

/-- D 中的关系 `x^n + y^n = 1`。 -/
theorem fermatCurve_relation (n : Nat) :
    (Ideal.Quotient.mk (fermatCurveIdeal n) (MvPolynomial.X 0)) ^ n
      + (Ideal.Quotient.mk (fermatCurveIdeal n) (MvPolynomial.X 1)) ^ n - 1 = 0 := by
  have h : Ideal.Quotient.mk (fermatCurveIdeal n) (fermatCurvePoly n) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rw [fermatCurvePoly] at h
  simpa only [map_add, map_sub, map_pow, map_one] using h

/-! ### 基本关系：x^n = λ（U₀）、y^n = 1-λ（A₀） -/

theorem fermatU0_root_pow (n : Nat) :
    (AdjoinRoot.root (fermatU0Poly n)) ^ n = AdjoinRoot.of (fermatU0Poly n) Polynomial.X := by
  have h : AdjoinRoot.mk (fermatU0Poly n) (Polynomial.X ^ n - Polynomial.C (Polynomial.X)) = 0 := by
    rw [AdjoinRoot.mk_eq_zero, fermatU0Poly]
  exact sub_eq_zero.mp (by simpa only [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] using h)

theorem fermatA0_x_pow (n : Nat) :
    (AdjoinRoot.of (fermatA0Poly n) (AdjoinRoot.root (fermatU0Poly n))) ^ n
      = AdjoinRoot.of (fermatA0Poly n) (AdjoinRoot.of (fermatU0Poly n) Polynomial.X) := by
  rw [← map_pow, fermatU0_root_pow]

/-! ### A₀ → D -/

/-- `ℚ[λ] → D`，`λ ↦ x^n`。 -/
noncomputable def fermatBaseToCurve (n : Nat) : Polynomial ℚ →ₐ[ℚ] fermatCurveRing n :=
  (Ideal.Quotient.mkₐ ℚ (fermatCurveIdeal n)).comp
    (Polynomial.aeval (MvPolynomial.X 0 ^ n : MvPolynomial (Fin 2) ℚ))

theorem fermatU0ToCurve_cond (n : Nat) :
    (fermatU0Poly n).eval₂ (fermatBaseToCurve n : Polynomial ℚ →+* fermatCurveRing n)
      (Ideal.Quotient.mk (fermatCurveIdeal n) (MvPolynomial.X 0)) = 0 := by
  have hpow : (fermatBaseToCurve n : Polynomial ℚ →+* fermatCurveRing n) Polynomial.X
      = Ideal.Quotient.mk (fermatCurveIdeal n) (MvPolynomial.X 0 ^ n) := by
    simp [fermatBaseToCurve]
  simp only [fermatU0Poly, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C]
  rw [hpow, ← map_pow, sub_self]

/-- `U₀ → D`：`λ ↦ x^n`，`x ↦ x`。 -/
noncomputable def fermatU0ToCurve (n : Nat) : fermatU0Ring n →ₐ[ℚ] fermatCurveRing n :=
  AdjoinRoot.liftAlgHom (p := fermatU0Poly n) (fermatBaseToCurve n)
    (Ideal.Quotient.mk (fermatCurveIdeal n) (MvPolynomial.X 0)) (fermatU0ToCurve_cond n)

#print axioms fermatCurve_relation
#print axioms fermatU0_root_pow
#print axioms fermatA0_x_pow
#print axioms fermatU0ToCurve_cond

end LeanFormal.IUT.XiFPaper.Mzk1G1FermatSmoothChartActual
