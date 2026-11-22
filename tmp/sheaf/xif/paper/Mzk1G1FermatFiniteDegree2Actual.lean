/- G1-A：Fermat 两张仿射图在 ℚ[λ]（=ℚ[t]）上的实际环结构。
   基础：`Mzk1G1FermatChartRingActual2` 已 accepted 的 monic/power basis：
   `fermatU0Poly n = X^n - λ`、`fermatU1Poly n = X^n - (1-λ)`，以及
   `fermatU0Basis`/`fermatU1Basis`。
   本文件把第二个 monic 多项式 base change 到第一个环上再添根（"添单根"），得到
   A₀ = ℚ[λ][x,y]/(x^n-λ, y^n-(1-λ)) 的实际呈现，并给出
   * 显式自由基 {x^i y^j : 0 ≤ i,j < n}（两个 power basis 的 `Basis.smulTower`），
   * Module.Finite 与 rank = n²（对 ℚ[λ]），
   * ∞ 图 A∞ = ℚ[t][r,s]/(r^n-t, 1+s^n-r^n) 的同样结论及关系 s^n = t-1，
   * 关系 y^n = 1-λ（即 x^n+y^n=1）。
   不含 sorry/admit/axiom/PUnit/True/toy。 -/
import tmp.sheaf.xif.paper.Mzk1G1FermatChartSchemeActual
import tmp.sheaf.xif.paper.Mzk1G1FermatChartRingActual2
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.AlgebraTower
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatFiniteDegree2Actual
open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartRingActual2
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartSchemeActual

/-! ### 一般 monic 单根因子 -/

/-- `X^n - C c`：在 `ℚ[λ]` 上准备添一个 n 次单根。 -/
noncomputable def fermatRootPoly (n : Nat) (c : Polynomial ℚ) :
    Polynomial (Polynomial ℚ) :=
  X ^ n - C c

theorem fermatRootPoly_monic (n : Nat) (c : Polynomial ℚ) (hn : 0 < n) :
    (fermatRootPoly n c).Monic := by
  unfold fermatRootPoly
  apply monic_X_pow_sub
  calc (C c : Polynomial (Polynomial ℚ)).degree ≤ 0 := degree_C_le
    _ < n := by exact_mod_cast hn

theorem fermatRootPoly_natDegree (n : Nat) (c : Polynomial ℚ) :
    (fermatRootPoly n c).natDegree = n := by
  unfold fermatRootPoly
  exact natDegree_X_pow_sub_C

/-! ### 第一张图 U₀：A₀ = ℚ[λ][x]/(x^n-λ)[y]/(y^n-(1-λ)) -/

theorem fermatU0Poly_natDegree (n : Nat) : (fermatU0Poly n).natDegree = n := by
  rw [fermatU0Poly, natDegree_X_pow_sub_C]

theorem fermatU0Poly_degree_ne_zero (n : Nat) (hn : 0 < n) :
    (fermatU0Poly n).degree ≠ 0 := by
  rw [fermatU0Poly, degree_X_pow_sub_C hn]
  exact_mod_cast hn.ne'

/-- 第二个单根因子：把 `X^n - (1-λ)` base change 到 `ℚ[λ][x]/(x^n-λ)` 再添根。 -/
noncomputable def fermatA0Poly (n : Nat) : Polynomial (fermatU0Ring n) :=
  (fermatRootPoly n (1 - Polynomial.X)).map (AdjoinRoot.of (fermatU0Poly n))

theorem fermatA0Poly_monic (n : Nat) (hn : 0 < n) : (fermatA0Poly n).Monic := by
  unfold fermatA0Poly
  exact (fermatRootPoly_monic n (1 - Polynomial.X) hn).map _

theorem fermatA0Poly_natDegree (n : Nat) (hn : 0 < n) : (fermatA0Poly n).natDegree = n := by
  have hdeg : (fermatU0Poly n).degree ≠ 0 := fermatU0Poly_degree_ne_zero n hn
  unfold fermatA0Poly
  rw [natDegree_map_eq_of_injective (AdjoinRoot.of.injective_of_degree_ne_zero hdeg),
    fermatRootPoly_natDegree]

/-- A₀ 的实际呈现：`ℚ[λ][x]/(x^n-λ)[y]/(y^n-(1-λ))`。 -/
noncomputable abbrev fermatA0Ring (n : Nat) : Type := AdjoinRoot (fermatA0Poly n)

/-- `1, y, …, y^{n-1}` power basis（在 `ℚ[λ][x]/(x^n-λ)` 上）。 -/
noncomputable def fermatA0Basis (n : Nat) (hn : 0 < n) :
    Module.Basis (Fin n) (fermatU0Ring n) (fermatA0Ring n) :=
  (AdjoinRoot.powerBasis' (fermatA0Poly_monic n hn)).basis.reindex
    (finCongr (fermatA0Poly_natDegree n hn))

theorem fermatA0Ring_finite_over_U0 (n : Nat) (hn : 0 < n) :
    Module.Finite (fermatU0Ring n) (fermatA0Ring n) :=
  (fermatA0Poly_monic n hn).finite_adjoinRoot

/-- 显式自由基 `{x^i y^j : 0 ≤ i,j < n}`：两个 monic power basis 的 tower 积。 -/
noncomputable def fermatA0BasisTower (n : Nat) (hn : 0 < n) :
    Module.Basis (Fin n × Fin n) (Polynomial ℚ) (fermatA0Ring n) :=
  ((fermatU0Basis n hn).reindex (finCongr (fermatU0Poly_natDegree n))).smulTower
    (fermatA0Basis n hn)

/-- π 在 λ 图上的 rank/degree 读数：`n²`。 -/
theorem fermatA0Ring_finrank (n : Nat) (hn : 0 < n) :
    Module.finrank (Polynomial ℚ) (fermatA0Ring n) = n * n := by
  rw [Module.finrank_eq_card_basis (fermatA0BasisTower n hn)]
  simp [Fintype.card_prod]

theorem fermatA0Ring_finite (n : Nat) (hn : 0 < n) :
    Module.Finite (Polynomial ℚ) (fermatA0Ring n) :=
  Module.Finite.of_basis (fermatA0BasisTower n hn)

/-- A₀ 中的关系 `y^n = 1 - λ`（λ = x^n），即 `x^n + y^n = 1`。 -/
theorem fermatA0_root_pow (n : Nat) :
    (AdjoinRoot.root (fermatA0Poly n)) ^ n
      = 1 - AdjoinRoot.of (fermatA0Poly n)
          (AdjoinRoot.of (fermatU0Poly n) Polynomial.X) := by
  have h1 : (AdjoinRoot.root (fermatA0Poly n)) ^ n
      - AdjoinRoot.of (fermatA0Poly n)
          (AdjoinRoot.of (fermatU0Poly n) (1 - Polynomial.X)) = 0 := by
    have h : AdjoinRoot.mk (fermatA0Poly n)
        (X ^ n - C (AdjoinRoot.of (fermatU0Poly n) (1 - Polynomial.X))) = 0 := by
      rw [AdjoinRoot.mk_eq_zero]
      rw [fermatA0Poly, fermatRootPoly, Polynomial.map_sub, Polynomial.map_pow,
        Polynomial.map_X, Polynomial.map_C]
    simpa only [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] using h
  have h2 : AdjoinRoot.of (fermatA0Poly n) (AdjoinRoot.of (fermatU0Poly n) (1 - Polynomial.X))
      = 1 - AdjoinRoot.of (fermatA0Poly n) (AdjoinRoot.of (fermatU0Poly n) Polynomial.X) := by
    simp only [map_sub, map_one]
  rw [h2] at h1
  exact sub_eq_zero.mp h1

/-! ### 第二张图 U∞：A∞ = ℚ[t][r]/(r^n-t)[s]/(s^n-(t-1))，其中 1+s^n-r^n=0 -/

/-- ∞ 图的第二个单根因子：`s^n - (t-1)`，其中 `t = r^n` 是 `ℚ[t]` 的变量。 -/
noncomputable def fermatAInfPoly (n : Nat) : Polynomial (fermatU0Ring n) :=
  (fermatRootPoly n (Polynomial.X - 1)).map (AdjoinRoot.of (fermatU0Poly n))

theorem fermatAInfPoly_monic (n : Nat) (hn : 0 < n) : (fermatAInfPoly n).Monic := by
  unfold fermatAInfPoly
  exact (fermatRootPoly_monic n (Polynomial.X - 1) hn).map _

theorem fermatAInfPoly_natDegree (n : Nat) (hn : 0 < n) : (fermatAInfPoly n).natDegree = n := by
  have hdeg : (fermatU0Poly n).degree ≠ 0 := fermatU0Poly_degree_ne_zero n hn
  unfold fermatAInfPoly
  rw [natDegree_map_eq_of_injective (AdjoinRoot.of.injective_of_degree_ne_zero hdeg),
    fermatRootPoly_natDegree]

/-- A∞ 的实际呈现：`ℚ[t][r]/(r^n-t)[s]/(s^n-(t-1))`。 -/
noncomputable abbrev fermatAInfRing (n : Nat) : Type := AdjoinRoot (fermatAInfPoly n)

noncomputable def fermatAInfBasis (n : Nat) (hn : 0 < n) :
    Module.Basis (Fin n) (fermatU0Ring n) (fermatAInfRing n) :=
  (AdjoinRoot.powerBasis' (fermatAInfPoly_monic n hn)).basis.reindex
    (finCongr (fermatAInfPoly_natDegree n hn))

theorem fermatAInfRing_finite_over_U0 (n : Nat) (hn : 0 < n) :
    Module.Finite (fermatU0Ring n) (fermatAInfRing n) :=
  (fermatAInfPoly_monic n hn).finite_adjoinRoot

/-- ∞ 图的显式自由基 `{r^i s^j : 0 ≤ i,j < n}`。 -/
noncomputable def fermatAInfBasisTower (n : Nat) (hn : 0 < n) :
    Module.Basis (Fin n × Fin n) (Polynomial ℚ) (fermatAInfRing n) :=
  ((fermatU0Basis n hn).reindex (finCongr (fermatU0Poly_natDegree n))).smulTower
    (fermatAInfBasis n hn)

theorem fermatAInfRing_finrank (n : Nat) (hn : 0 < n) :
    Module.finrank (Polynomial ℚ) (fermatAInfRing n) = n * n := by
  rw [Module.finrank_eq_card_basis (fermatAInfBasisTower n hn)]
  simp [Fintype.card_prod]

theorem fermatAInfRing_finite (n : Nat) (hn : 0 < n) :
    Module.Finite (Polynomial ℚ) (fermatAInfRing n) :=
  Module.Finite.of_basis (fermatAInfBasisTower n hn)

/-- ∞ 图的关系 `s^n = t - 1`，其中 `t = r^n`（等价于 `1 + s^n - r^n = 0`）。 -/
theorem fermatAInf_root_pow (n : Nat) :
    (AdjoinRoot.root (fermatAInfPoly n)) ^ n
      = AdjoinRoot.of (fermatAInfPoly n)
          (AdjoinRoot.of (fermatU0Poly n) Polynomial.X) - 1 := by
  have h1 : (AdjoinRoot.root (fermatAInfPoly n)) ^ n
      - AdjoinRoot.of (fermatAInfPoly n)
          (AdjoinRoot.of (fermatU0Poly n) (Polynomial.X - 1)) = 0 := by
    have h : AdjoinRoot.mk (fermatAInfPoly n)
        (X ^ n - C (AdjoinRoot.of (fermatU0Poly n) (Polynomial.X - 1))) = 0 := by
      rw [AdjoinRoot.mk_eq_zero]
      rw [fermatAInfPoly, fermatRootPoly, Polynomial.map_sub, Polynomial.map_pow,
        Polynomial.map_X, Polynomial.map_C]
    simpa only [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] using h
  have h2 : AdjoinRoot.of (fermatAInfPoly n)
        (AdjoinRoot.of (fermatU0Poly n) (Polynomial.X - 1))
      = AdjoinRoot.of (fermatAInfPoly n) (AdjoinRoot.of (fermatU0Poly n) Polynomial.X) - 1 := by
    simp only [map_sub, map_one]
  rw [h2] at h1
  exact sub_eq_zero.mp h1

#print axioms fermatA0Poly_monic
#print axioms fermatA0Poly_natDegree
#print axioms fermatA0Ring_finite_over_U0
#print axioms fermatA0Ring_finrank
#print axioms fermatA0Ring_finite
#print axioms fermatA0_root_pow
#print axioms fermatAInfRing_finrank
#print axioms fermatAInfRing_finite
#print axioms fermatAInf_root_pow

end LeanFormal.IUT.XiFPaper.Mzk1G1FermatFiniteDegree2Actual