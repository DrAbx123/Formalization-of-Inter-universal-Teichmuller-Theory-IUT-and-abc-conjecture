/- G1-A §2.4 (h) step 3：∞-chart 的 k̄ 上整性（Eisenstein）：k̄[u,v]/(1+u^n-v^n) 是整环。
   与 GeomIntegral 同型：G = 1 + X0^n - X1^n；finSuccEquiv 后为 X^n + 1 - C(Y)^n = X^n - C(Y^n - 1)，
   在素理想 (Y-1) 处 Eisenstein（常数项 1-Y^n = -(Y^n-1) 恰被 Y-1 整除一次）。
   做法（route §2.4）：x^n + (y^n - 1) 在 ℚ[y] 上对素元 (y-1) 满足 Eisenstein
   （常数项 y^n-1 恰被 y-1 整除一次），故不可约；UFD 中不可约即素；
   主理想 (F) 素，故商环是整环。再经 finSuccEquiv 把不可约性运回 MvPolynomial (Fin 2) ℚ。
   不含 sorry/admit/axiom/PUnit/True/toy。 -/
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import tmp.sheaf.xif.paper.Mzk1G1FermatSmoothGeomIntegralActual
import tmp.sheaf.xif.paper.Mzk1G1FermatSecondChartActual
import tmp.sheaf.xif.paper.Mzk1G1ChartKbarActual
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartInfKbarActual
open Polynomial MvPolynomial
open scoped TensorProduct
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSmoothGeomIntegralActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ChartKbarActual

/-! ### 路线对象 D = FermatK[X,Y]/(X^n+Y^n-1)（= henry 的 R n） -/

/-- Fermat 仿射多项式 `F = X^n + Y^n - 1`。 -/
noncomputable def fermatInfPoly (n : Nat) : MvPolynomial (Fin 2) FermatK :=
  1 + MvPolynomial.X 0 ^ n - MvPolynomial.X 1 ^ n

/-- 主理想 `(F)`。 -/
noncomputable def fermatInfIdeal (n : Nat) : Ideal (MvPolynomial (Fin 2) FermatK) :=
  Ideal.span ({fermatInfPoly n} : Set (MvPolynomial (Fin 2) FermatK))

/-- 曲线环 D = FermatK[X,Y]/(X^n+Y^n-1)（与 henry 的 `R n` 定义相同）。 -/
noncomputable abbrev fermatInfRing (n : Nat) : Type :=
  MvPolynomial (Fin 2) FermatK ⧸ fermatInfIdeal n

/-! ### F 作为 FermatK[Y][X] 中的 monic 多项式 -/

/-- F = X^n + (Y^n - 1) = X^n - (1 - Y^n)，作为 FermatK[Y][X] 中的元素。 -/
noncomputable def fermatInfTwoVarPoly (n : Nat) : Polynomial (Polynomial FermatK) :=
  Polynomial.X ^ n - Polynomial.C (Polynomial.X ^ n - 1)

theorem fermatInfTwoVarPoly_monic (n : Nat) (hn : 0 < n) : (fermatInfTwoVarPoly n).Monic := by
  unfold fermatInfTwoVarPoly
  apply monic_X_pow_sub
  calc (Polynomial.C (Polynomial.X ^ n - 1) : Polynomial (Polynomial FermatK)).degree ≤ 0 :=
      Polynomial.degree_C_le
    _ < n := by exact_mod_cast hn

theorem fermatInfTwoVarPoly_natDegree (n : Nat) : (fermatInfTwoVarPoly n).natDegree = n := by
  unfold fermatInfTwoVarPoly
  exact Polynomial.natDegree_X_pow_sub_C

theorem fermatInfTwoVarPoly_coeff_zero (n : Nat) (hn : 0 < n) :
    (fermatInfTwoVarPoly n).coeff 0 = 1 - Polynomial.X ^ n := by
  unfold fermatInfTwoVarPoly
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
  simp only [if_true, if_neg (by omega : ¬ n = 0), if_neg (by omega : ¬ (0 = n))]
  ring

theorem fermatInfTwoVarPoly_coeff_of_pos_lt (n : Nat) (hn : 0 < n) {k : Nat}
    (hk0 : 0 < k) (hkn : k < n) : (fermatInfTwoVarPoly n).coeff k = 0 := by
  unfold fermatInfTwoVarPoly
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
  simp only [if_true, if_neg (by omega : ¬ k = 0), if_neg (by omega : ¬ k = n),
    if_neg (by omega : ¬ n = k)]
  ring

/-! ### Eisenstein 于素理想 (Y-1) ⊂ FermatK[Y] -/

/-- (Y-1) 是素理想。 -/
theorem fermatCoeffPrimeIdeal :
    (Ideal.span ({Polynomial.X - Polynomial.C (1 : FermatK)} : Set (Polynomial FermatK))).IsPrime :=
  (Ideal.span_singleton_prime (Polynomial.monic_X_sub_C (1 : FermatK)).ne_zero).mpr
    (Polynomial.prime_X_sub_C (1 : FermatK))

theorem fermatInfTwoVarPoly_isEisenstein (n : Nat) (hn : 0 < n) :
    (fermatInfTwoVarPoly n).IsEisensteinAt
      (Ideal.span ({Polynomial.X - Polynomial.C (1 : FermatK)} : Set (Polynomial FermatK))) := by
  refine Polynomial.Monic.isEisensteinAt_of_mem_of_notMem (fermatInfTwoVarPoly_monic n hn)
    fermatCoeffPrimeIdeal.ne_top ?_ ?_
  · intro k hk
    by_cases hk0 : k = 0
    · subst hk0
      rw [fermatInfTwoVarPoly_coeff_zero n hn, Ideal.mem_span_singleton]
      simpa using (dvd_neg.mpr (sub_dvd_pow_sub_pow (Polynomial.X : Polynomial FermatK)
        (Polynomial.C (1 : FermatK)) n))
    · have hpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hlt : k < n := by
        rw [← fermatInfTwoVarPoly_natDegree n]
        exact hk
      rw [fermatInfTwoVarPoly_coeff_of_pos_lt n hn hpos hlt]
      exact Ideal.zero_mem _
  · intro hmem
    rw [fermatInfTwoVarPoly_coeff_zero n hn, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hmem
    have hmem' : (Polynomial.X - Polynomial.C (1 : FermatK)) ^ 2 ∣
        (Polynomial.X ^ n - 1 : Polynomial FermatK) := by
      rw [show (1 - Polynomial.X ^ n : Polynomial FermatK)
        = -(Polynomial.X ^ n - 1) from by ring] at hmem
      exact dvd_neg.mp hmem
    have hdiv : Polynomial.X ^ 2 ∣
        ((Polynomial.X ^ n - 1 : Polynomial FermatK).comp (Polynomial.X + Polynomial.C (1 : FermatK))) :=
      (Polynomial.X_sub_C_pow_dvd_iff (t := (1 : FermatK)) (n := 2)
        (p := (Polynomial.X ^ n - 1 : Polynomial FermatK))).mp hmem'
    have hc1 : ((Polynomial.X ^ n - 1 : Polynomial FermatK).comp
        (Polynomial.X + Polynomial.C (1 : FermatK))).coeff 1 = 0 :=
      Polynomial.X_pow_dvd_iff.mp hdiv 1 (by norm_num)
    have hq : ((Polynomial.X ^ n - 1 : Polynomial FermatK).comp
        (Polynomial.X + Polynomial.C (1 : FermatK))) = (Polynomial.X + 1) ^ n - 1 := by
      simp [Polynomial.C_1]
    rw [hq] at hc1
    have hcoeff : ((Polynomial.X + 1 : Polynomial FermatK) ^ n - 1).coeff 1 = (n : FermatK) := by
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_add_one_pow, Polynomial.coeff_one]
      simp
    rw [hcoeff] at hc1
    exact (Nat.cast_ne_zero.mpr hn.ne') hc1

theorem fermatInfTwoVarPoly_irreducible (n : Nat) (hn : 0 < n) :
    Irreducible (fermatInfTwoVarPoly n) :=
  (fermatInfTwoVarPoly_isEisenstein n hn).irreducible fermatCoeffPrimeIdeal
    (Polynomial.Monic.isPrimitive (fermatInfTwoVarPoly_monic n hn))
    (by rw [fermatInfTwoVarPoly_natDegree n]; exact hn)

/-! ### 运输到 MvPolynomial (Fin 2) FermatK -/

/-- 一次 finSuccEquiv 后的多项式：`X^n + C(Y)^n - 1` over FermatK[Y]。 -/
noncomputable def fermatInfSuccPoly (n : Nat) : Polynomial (MvPolynomial (Fin 1) FermatK) :=
  1 + Polynomial.X ^ n - Polynomial.C (MvPolynomial.X 0) ^ n

theorem finSucc_fermatInfPoly (n : Nat) :
    MvPolynomial.finSuccEquiv FermatK 1 (fermatInfPoly n) = fermatInfSuccPoly n := by
  have h1 : MvPolynomial.finSuccEquiv FermatK 1 (MvPolynomial.X 1 : MvPolynomial (Fin 2) FermatK)
      = Polynomial.C (MvPolynomial.X 0) := by
    simpa using MvPolynomial.finSuccEquiv_X_succ (R := FermatK) (n := 1) (j := (0 : Fin 1))
  have h2 : MvPolynomial.finSuccEquiv FermatK 1 (MvPolynomial.X 0 : MvPolynomial (Fin 2) FermatK)
      = Polynomial.X := MvPolynomial.finSuccEquiv_X_zero (R := FermatK) (n := 1)
  unfold fermatInfPoly fermatInfSuccPoly
  simp only [map_add, map_sub, map_pow, map_one, h1, h2]

theorem mapAlgEquiv_fermatInfSuccPoly (n : Nat) :
    Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv FermatK (Fin 1)) (fermatInfSuccPoly n)
      = fermatInfTwoVarPoly n := by
  have hY : (↑(MvPolynomial.uniqueAlgEquiv FermatK (Fin 1)) :
      MvPolynomial (Fin 1) FermatK →+* Polynomial FermatK) (MvPolynomial.X 0) = Polynomial.X := by
    simp [MvPolynomial.uniqueAlgEquiv]
  unfold fermatInfSuccPoly fermatInfTwoVarPoly
  simp only [Polynomial.coe_mapAlgEquiv, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_pow, Polynomial.map_one, Polynomial.map_C, Polynomial.map_X, hY]
  rw [Polynomial.C_sub, Polynomial.C_1, Polynomial.C_pow]
  ring

theorem fermatInfSuccPoly_irreducible (n : Nat) (hn : 0 < n) : Irreducible (fermatInfSuccPoly n) := by
  have h : Irreducible
      (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv FermatK (Fin 1)) (fermatInfSuccPoly n)) := by
    rw [mapAlgEquiv_fermatInfSuccPoly n]
    exact fermatInfTwoVarPoly_irreducible n hn
  exact (MulEquiv.irreducible_iff
    (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv FermatK (Fin 1)))).mp h

theorem fermatInfPoly_irreducible (n : Nat) (hn : 0 < n) :
    Irreducible (fermatInfPoly n) := by
  have h : Irreducible (MvPolynomial.finSuccEquiv FermatK 1 (fermatInfPoly n)) := by
    rw [finSucc_fermatInfPoly n]
    exact fermatInfSuccPoly_irreducible n hn
  exact (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv FermatK 1)).mp h

theorem fermatInfPoly_prime (n : Nat) (hn : 0 < n) : Prime (fermatInfPoly n) :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp (fermatInfPoly_irreducible n hn)

theorem fermatInfPoly_ne_zero (n : Nat) (hn : 0 < n) : fermatInfPoly n ≠ 0 :=
  (fermatInfPoly_irreducible n hn).ne_zero

/-- 主理想 (F) 是素理想。 -/
theorem fermatInfIdeal_isPrime (n : Nat) (hn : 0 < n) : (fermatInfIdeal n).IsPrime :=
  (Ideal.span_singleton_prime (fermatInfPoly_ne_zero n hn)).mpr (fermatInfPoly_prime n hn)

/-! ### 整性：R n 是整环 -/

/-- route §2.4 的整性：曲线环 R n = FermatK[x,y]/(x^n+y^n-1) 是整环。 -/
theorem fermatInfRing_isDomain (n : Nat) (hn : 0 < n) : IsDomain (fermatInfRing n) :=
  (Ideal.Quotient.isDomain_iff_prime (fermatInfIdeal n)).mpr
    (fermatInfIdeal_isPrime n hn)

#print axioms fermatInfTwoVarPoly_monic
#print axioms fermatInfTwoVarPoly_coeff_zero
#print axioms fermatInfTwoVarPoly_isEisenstein
#print axioms fermatInfTwoVarPoly_irreducible
#print axioms finSucc_fermatInfPoly
#print axioms mapAlgEquiv_fermatInfSuccPoly
#print axioms fermatInfPoly_irreducible
#print axioms fermatInfPoly_prime
#print axioms fermatInfIdeal_isPrime
#print axioms fermatInfRing_isDomain


/-! ### 从 k̄[u,v]/(G) 运输到 (R2 n) ⊗[ℚ] k̄ -/

theorem map_secondEquation_eq (n : Nat) :
    MvPolynomial.map (algebraMap ℚ FermatK) (secondEquation n) = fermatInfPoly n := by
  simp [secondEquation, fermatInfPoly]

theorem map_secondIdeal_eq (n : Nat) :
    Ideal.map (MvPolynomial.map (algebraMap ℚ FermatK)) (Ideal.span {secondEquation n})
      = fermatInfIdeal n := by
  rw [Ideal.map_span, Set.image_singleton, map_secondEquation_eq]
  rfl

/-- (R2 n) ⊗[ℚ] k̄ ≅ k̄[u,v]/(1+u^n-v^n)。 -/
noncomputable def chartKbarInfEquiv (n : Nat) :
    Mzk1G1FermatSecondChartActual.R2 n ⊗[ℚ] FermatK ≃ₐ[ℚ] fermatInfRing n := by
  refine (Algebra.TensorProduct.quotientTensorEquiv (R := ℚ) (S := ℚ)
    (A := MvPolynomial (Fin 2) ℚ) (T := FermatK)
    (I := Ideal.span {secondEquation n})).trans ?_
  refine Ideal.quotientEquivAlg _ _ Mzk1G1ChartKbarActual.ambientEquiv ?_
  rw [Ideal.map_map, Mzk1G1ChartKbarActual.ambientEquiv_comp_algebraMap, map_secondIdeal_eq]

/-- **∞-chart 的 k̄ 上整性**：IsDomain ((R2 n) ⊗[ℚ] k̄)。 -/
theorem chartKbarInf_isDomain (n : Nat) (hn : 0 < n) :
    IsDomain (Mzk1G1FermatSecondChartActual.R2 n ⊗[ℚ] FermatK) :=
  (chartKbarInfEquiv n).toRingEquiv.isDomain_iff.mpr (fermatInfRing_isDomain n hn)

#print axioms fermatInfRing_isDomain
#print axioms chartKbarInfEquiv
#print axioms chartKbarInf_isDomain

end LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartInfKbarActual