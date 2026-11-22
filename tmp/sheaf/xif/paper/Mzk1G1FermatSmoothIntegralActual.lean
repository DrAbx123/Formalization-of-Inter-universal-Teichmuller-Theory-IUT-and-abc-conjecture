/- G1-A §2.4 几何整性（Eisenstein）：曲线环 R n = ℚ[x,y]/(x^n+y^n-1) 是整环。
   做法（route §2.4）：x^n + (y^n - 1) 在 ℚ[y] 上对素元 (y-1) 满足 Eisenstein
   （常数项 y^n-1 恰被 y-1 整除一次），故不可约；UFD 中不可约即素；
   主理想 (F) 素，故商环是整环。再经 finSuccEquiv 把不可约性运回 MvPolynomial (Fin 2) ℚ。
   不含 sorry/admit/axiom/PUnit/True/toy。 -/
import tmp.sheaf.xif.paper.Mzk1G1FermatAffineChartActual
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatSmoothIntegralActual
open Polynomial MvPolynomial

/-! ### 路线对象 D = ℚ[X,Y]/(X^n+Y^n-1)（= henry 的 R n） -/

/-- Fermat 仿射多项式 `F = X^n + Y^n - 1`。 -/
noncomputable def fermatCurvePoly (n : Nat) : MvPolynomial (Fin 2) ℚ :=
  MvPolynomial.X 0 ^ n + MvPolynomial.X 1 ^ n - 1

/-- 主理想 `(F)`。 -/
noncomputable def fermatCurveIdeal (n : Nat) : Ideal (MvPolynomial (Fin 2) ℚ) :=
  Ideal.span ({fermatCurvePoly n} : Set (MvPolynomial (Fin 2) ℚ))

/-- 曲线环 D = ℚ[X,Y]/(X^n+Y^n-1)（与 henry 的 `R n` 定义相同）。 -/
noncomputable abbrev fermatCurveRing (n : Nat) : Type :=
  MvPolynomial (Fin 2) ℚ ⧸ fermatCurveIdeal n

/-! ### F 作为 ℚ[Y][X] 中的 monic 多项式 -/

/-- F = X^n + (Y^n - 1) = X^n - (1 - Y^n)，作为 ℚ[Y][X] 中的元素。 -/
noncomputable def fermatTwoVarPoly (n : Nat) : Polynomial (Polynomial ℚ) :=
  Polynomial.X ^ n - Polynomial.C (1 - Polynomial.X ^ n)

theorem fermatTwoVarPoly_monic (n : Nat) (hn : 0 < n) : (fermatTwoVarPoly n).Monic := by
  unfold fermatTwoVarPoly
  apply monic_X_pow_sub
  calc (Polynomial.C (1 - Polynomial.X ^ n) : Polynomial (Polynomial ℚ)).degree ≤ 0 :=
      Polynomial.degree_C_le
    _ < n := by exact_mod_cast hn

theorem fermatTwoVarPoly_natDegree (n : Nat) : (fermatTwoVarPoly n).natDegree = n := by
  unfold fermatTwoVarPoly
  exact Polynomial.natDegree_X_pow_sub_C

theorem fermatTwoVarPoly_coeff_zero (n : Nat) (hn : 0 < n) :
    (fermatTwoVarPoly n).coeff 0 = Polynomial.X ^ n - 1 := by
  unfold fermatTwoVarPoly
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
  simp only [if_true, if_neg (by omega : ¬ n = 0), if_neg (by omega : ¬ (0 = n))]
  ring

theorem fermatTwoVarPoly_coeff_of_pos_lt (n : Nat) (hn : 0 < n) {k : Nat}
    (hk0 : 0 < k) (hkn : k < n) : (fermatTwoVarPoly n).coeff k = 0 := by
  unfold fermatTwoVarPoly
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
  simp only [if_true, if_neg (by omega : ¬ k = 0), if_neg (by omega : ¬ k = n),
    if_neg (by omega : ¬ n = k)]
  ring

/-! ### Eisenstein 于素理想 (Y-1) ⊂ ℚ[Y] -/

/-- (Y-1) 是素理想。 -/
theorem fermatCoeffPrimeIdeal :
    (Ideal.span ({Polynomial.X - Polynomial.C (1 : ℚ)} : Set (Polynomial ℚ))).IsPrime :=
  (Ideal.span_singleton_prime (Polynomial.monic_X_sub_C (1 : ℚ)).ne_zero).mpr
    (Polynomial.prime_X_sub_C (1 : ℚ))

theorem fermatTwoVarPoly_isEisenstein (n : Nat) (hn : 0 < n) :
    (fermatTwoVarPoly n).IsEisensteinAt
      (Ideal.span ({Polynomial.X - Polynomial.C (1 : ℚ)} : Set (Polynomial ℚ))) := by
  refine Polynomial.Monic.isEisensteinAt_of_mem_of_notMem (fermatTwoVarPoly_monic n hn)
    fermatCoeffPrimeIdeal.ne_top ?_ ?_
  · intro k hk
    by_cases hk0 : k = 0
    · subst hk0
      rw [fermatTwoVarPoly_coeff_zero n hn, Ideal.mem_span_singleton]
      simpa using sub_dvd_pow_sub_pow (Polynomial.X : Polynomial ℚ) (Polynomial.C (1 : ℚ)) n
    · have hpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hlt : k < n := by
        rw [← fermatTwoVarPoly_natDegree n]
        exact hk
      rw [fermatTwoVarPoly_coeff_of_pos_lt n hn hpos hlt]
      exact Ideal.zero_mem _
  · intro hmem
    rw [fermatTwoVarPoly_coeff_zero n hn, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hmem
    have hdiv : Polynomial.X ^ 2 ∣
        ((Polynomial.X ^ n - 1 : Polynomial ℚ).comp (Polynomial.X + Polynomial.C (1 : ℚ))) :=
      (Polynomial.X_sub_C_pow_dvd_iff (t := (1 : ℚ)) (n := 2)
        (p := (Polynomial.X ^ n - 1 : Polynomial ℚ))).mp hmem
    have hc1 : ((Polynomial.X ^ n - 1 : Polynomial ℚ).comp
        (Polynomial.X + Polynomial.C (1 : ℚ))).coeff 1 = 0 :=
      Polynomial.X_pow_dvd_iff.mp hdiv 1 (by norm_num)
    have hq : ((Polynomial.X ^ n - 1 : Polynomial ℚ).comp
        (Polynomial.X + Polynomial.C (1 : ℚ))) = (Polynomial.X + 1) ^ n - 1 := by
      simp [Polynomial.C_1]
    rw [hq] at hc1
    have hcoeff : ((Polynomial.X + 1 : Polynomial ℚ) ^ n - 1).coeff 1 = (n : ℚ) := by
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_add_one_pow, Polynomial.coeff_one]
      simp
    rw [hcoeff] at hc1
    exact (Nat.cast_ne_zero.mpr hn.ne') hc1

theorem fermatTwoVarPoly_irreducible (n : Nat) (hn : 0 < n) :
    Irreducible (fermatTwoVarPoly n) :=
  (fermatTwoVarPoly_isEisenstein n hn).irreducible fermatCoeffPrimeIdeal
    (Polynomial.Monic.isPrimitive (fermatTwoVarPoly_monic n hn))
    (by rw [fermatTwoVarPoly_natDegree n]; exact hn)

/-! ### 运输到 MvPolynomial (Fin 2) ℚ -/

/-- 一次 finSuccEquiv 后的多项式：`X^n + C(Y)^n - 1` over ℚ[Y]。 -/
noncomputable def fermatSuccPoly (n : Nat) : Polynomial (MvPolynomial (Fin 1) ℚ) :=
  Polynomial.X ^ n + Polynomial.C (MvPolynomial.X 0) ^ n - 1

theorem finSucc_fermatCurvePoly (n : Nat) :
    MvPolynomial.finSuccEquiv ℚ 1 (fermatCurvePoly n) = fermatSuccPoly n := by
  have h1 : MvPolynomial.finSuccEquiv ℚ 1 (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℚ)
      = Polynomial.C (MvPolynomial.X 0) := by
    simpa using MvPolynomial.finSuccEquiv_X_succ (R := ℚ) (n := 1) (j := (0 : Fin 1))
  have h2 : MvPolynomial.finSuccEquiv ℚ 1 (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ)
      = Polynomial.X := MvPolynomial.finSuccEquiv_X_zero (R := ℚ) (n := 1)
  unfold fermatCurvePoly fermatSuccPoly
  simp only [map_add, map_sub, map_pow, map_one, h1, h2]

theorem mapAlgEquiv_fermatSuccPoly (n : Nat) :
    Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)) (fermatSuccPoly n)
      = fermatTwoVarPoly n := by
  have hY : (↑(MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)) :
      MvPolynomial (Fin 1) ℚ →+* Polynomial ℚ) (MvPolynomial.X 0) = Polynomial.X := by
    simp [MvPolynomial.uniqueAlgEquiv]
  unfold fermatSuccPoly fermatTwoVarPoly
  simp only [Polynomial.coe_mapAlgEquiv, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_pow, Polynomial.map_one, Polynomial.map_C, Polynomial.map_X, hY]
  rw [Polynomial.C_sub, Polynomial.C_1, Polynomial.C_pow]
  ring

theorem fermatSuccPoly_irreducible (n : Nat) (hn : 0 < n) : Irreducible (fermatSuccPoly n) := by
  have h : Irreducible
      (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)) (fermatSuccPoly n)) := by
    rw [mapAlgEquiv_fermatSuccPoly n]
    exact fermatTwoVarPoly_irreducible n hn
  exact (MulEquiv.irreducible_iff
    (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)))).mp h

theorem fermatCurvePoly_irreducible (n : Nat) (hn : 0 < n) :
    Irreducible (fermatCurvePoly n) := by
  have h : Irreducible (MvPolynomial.finSuccEquiv ℚ 1 (fermatCurvePoly n)) := by
    rw [finSucc_fermatCurvePoly n]
    exact fermatSuccPoly_irreducible n hn
  exact (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv ℚ 1)).mp h

theorem fermatCurvePoly_prime (n : Nat) (hn : 0 < n) : Prime (fermatCurvePoly n) :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp (fermatCurvePoly_irreducible n hn)

theorem fermatCurvePoly_ne_zero (n : Nat) (hn : 0 < n) : fermatCurvePoly n ≠ 0 :=
  (fermatCurvePoly_irreducible n hn).ne_zero

/-- 主理想 (F) 是素理想。 -/
theorem fermatCurveIdeal_isPrime (n : Nat) (hn : 0 < n) : (fermatCurveIdeal n).IsPrime :=
  (Ideal.span_singleton_prime (fermatCurvePoly_ne_zero n hn)).mpr (fermatCurvePoly_prime n hn)

/-! ### 整性：R n 是整环 -/

/-- route §2.4 的整性：曲线环 R n = ℚ[x,y]/(x^n+y^n-1) 是整环。 -/
theorem fermatCurveRing_isDomain (n : Nat) (hn : 0 < n) : IsDomain (fermatCurveRing n) :=
  (Ideal.Quotient.isDomain_iff_prime (fermatCurveIdeal n)).mpr
    (fermatCurveIdeal_isPrime n hn)

/-- 与 henry/alan/emmy 共享图环 R n 的整性（定义与 fermatCurveRing 相同）。 -/
theorem fermatChartRing_isDomain (n : Nat) (hn : 0 < n) :
    IsDomain (LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual.R n) :=
  fermatCurveRing_isDomain n hn

#print axioms fermatTwoVarPoly_monic
#print axioms fermatTwoVarPoly_coeff_zero
#print axioms fermatTwoVarPoly_isEisenstein
#print axioms fermatTwoVarPoly_irreducible
#print axioms finSucc_fermatCurvePoly
#print axioms mapAlgEquiv_fermatSuccPoly
#print axioms fermatCurvePoly_irreducible
#print axioms fermatCurvePoly_prime
#print axioms fermatCurveIdeal_isPrime
#print axioms fermatCurveRing_isDomain
#print axioms fermatChartRing_isDomain

end LeanFormal.IUT.XiFPaper.Mzk1G1FermatSmoothIntegralActual