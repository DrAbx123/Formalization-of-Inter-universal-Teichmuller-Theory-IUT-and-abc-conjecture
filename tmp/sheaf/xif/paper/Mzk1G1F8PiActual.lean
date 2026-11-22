import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.NumberTheory.Height.NumberField
import tmp.sheaf.xif.paper.Mzk1G1F8LocalActual
import tmp.sheaf.xif.paper.Mzk1G1FermatOverlapActual
import tmp.sheaf.xif.paper.Mzk1G1FermatPiActual
import tmp.sheaf.xif.paper.Mzk1G1PsiAffineOverlapActual

/-! # F8 first equality on the chart-0 data (route §8.6 L838-848)

For a chart-0 point of the Fermat curve given by a ring hom `φ : Chart0Ring n →+* K`
satisfying `(φ x0)^n + (φ x1)^n = 1`, we prove the explicit comparison
`|h((φ x0)^n) - n h([φ x0 : φ x1 : 1])| <= n * finrank * log 2`.
By Henry's `chartMorphism0_comp`/`pi_ι0`, `(φ x0)^n` is the `λ`-coordinate of
`π(y)`, so this is the pointwise F8 estimate; the second equality with `h_ω`
will consume the A5/B3 line-bundle data.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.F8PiActual

open AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.F8LocalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiAffineOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatTwoChartGluingActual

variable {K : Type*} [Field K] [NumberField K]

private lemma bdd_above_fin {ι : Type*} [Fintype ι] (f : ι → ℝ) : BddAbove (Set.range f) :=
  (Set.finite_range f).bddAbove

/-- `sup` over `![a,1]` is bounded by `sup` over `![a,b,1]`. -/
private lemma sup_fin2_le_sup_fin3 {v : AbsoluteValue K ℝ} (a b : K) :
    (⨆ i : Fin 2, v (![a, 1] i)) ≤ ⨆ j : Fin 3, v (![a, b, 1] j) := by
  refine ciSup_le (fun i => ?_)
  fin_cases i
  · simpa using le_ciSup (bdd_above_fin (fun j : Fin 3 => v (![a, b, 1] j))) (0 : Fin 3)
  · simpa using le_ciSup (bdd_above_fin (fun j : Fin 3 => v (![a, b, 1] j))) (2 : Fin 3)

/-- Nonarchimedean bound of `sup` over `![a,b,1]` by `2 * sup` over `![a,1]`,
using `a^n + b^n = 1`. -/
private lemma sup_fin3_le_two_sup_fin2_nonarch {v : AbsoluteValue K ℝ}
    (hna : ∀ x y : K, v (x + y) ≤ max (v x) (v y)) {n : ℕ} (hn : n ≠ 0)
    {a b : K} (hrel : a ^ n + b ^ n = 1) :
    (⨆ j : Fin 3, v (![a, b, 1] j)) ≤ 2 * ⨆ i : Fin 2, v (![a, 1] i) := by
  set S : ℝ := ⨆ i : Fin 2, v (![a, 1] i)
  have hS0 : 0 ≤ S := Real.iSup_nonneg (fun i => AbsoluteValue.nonneg v _)
  have hva : v a ≤ S := by
    have := le_ciSup (bdd_above_fin (fun i : Fin 2 => v (![a, 1] i))) (0 : Fin 2)
    simpa [S] using this
  have hv1 : v (1 : K) ≤ S := by
    have := le_ciSup (bdd_above_fin (fun i : Fin 2 => v (![a, 1] i))) (1 : Fin 2)
    simpa [S] using this
  have hvb : v b ≤ S := by
    have h := fermat_local_nonarch (v := v) hna hn (x := a) (y := b) (z := 1)
      (by simpa using hrel)
    exact le_trans h (max_le hva hv1)
  refine ciSup_le (fun j => ?_)
  fin_cases j
  · have : v a ≤ 2 * S := by linarith
    simpa [S] using this
  · have : v b ≤ 2 * S := by linarith
    simpa [S] using this
  · have : v (1 : K) ≤ 2 * S := by linarith
    simpa [S] using this


/-- Nonarchimedean bound of `sup` over `![a,b,1]` by `sup` over `![a,1]` (no factor 2),
using `a^n + b^n = 1`. -/
private lemma sup_fin3_le_sup_fin2_nonarch {v : AbsoluteValue K ℝ}
    (hna : ∀ x y : K, v (x + y) ≤ max (v x) (v y)) {n : ℕ} (hn : n ≠ 0)
    {a b : K} (hrel : a ^ n + b ^ n = 1) :
    (⨆ j : Fin 3, v (![a, b, 1] j)) ≤ ⨆ i : Fin 2, v (![a, 1] i) := by
  set S : ℝ := ⨆ i : Fin 2, v (![a, 1] i)
  have hva : v a ≤ S := by
    have := le_ciSup (bdd_above_fin (fun i : Fin 2 => v (![a, 1] i))) (0 : Fin 2)
    simpa [S] using this
  have hv1 : v (1 : K) ≤ S := by
    have := le_ciSup (bdd_above_fin (fun i : Fin 2 => v (![a, 1] i))) (1 : Fin 2)
    simpa [S] using this
  have hvb : v b ≤ S := by
    have h := fermat_local_nonarch (v := v) hna hn (x := a) (y := b) (z := 1)
      (by simpa using hrel)
    exact le_trans h (max_le hva hv1)
  refine ciSup_le (fun j => ?_)
  fin_cases j
  · simpa [S] using hva
  · simpa [S] using hvb
  · simpa [S] using hv1

/-- Archimedean bound of `sup` over `![a,b,1]` by `2 * sup` over `![a,1]`,
using `a^n + b^n = 1`. -/
private lemma sup_fin3_le_two_sup_fin2_arch {v : AbsoluteValue K ℝ} {n : ℕ} (hn : 1 ≤ n)
    {a b : K} (hrel : a ^ n + b ^ n = 1) :
    (⨆ j : Fin 3, v (![a, b, 1] j)) ≤ 2 * ⨆ i : Fin 2, v (![a, 1] i) := by
  set S : ℝ := ⨆ i : Fin 2, v (![a, 1] i)
  have hS0 : 0 ≤ S := Real.iSup_nonneg (fun i => AbsoluteValue.nonneg v _)
  have hva : v a ≤ S := by
    have := le_ciSup (bdd_above_fin (fun i : Fin 2 => v (![a, 1] i))) (0 : Fin 2)
    simpa [S] using this
  have hv1 : v (1 : K) ≤ S := by
    have := le_ciSup (bdd_above_fin (fun i : Fin 2 => v (![a, 1] i))) (1 : Fin 2)
    simpa [S] using this
  have hvb : v b ≤ 2 * S := by
    have h := fermat_local_arch (v := v) hn (x := a) (y := b) (z := 1)
      (by simpa using hrel)
    have hmax : max (v a) (v (1 : K)) ≤ S := max_le hva hv1
    nlinarith
  refine ciSup_le (fun j => ?_)
  fin_cases j
  · have : v a ≤ 2 * S := by linarith
    simpa [S] using this
  · simpa [S] using hvb
  · have : v (1 : K) ≤ 2 * S := by linarith
    simpa [S] using this

/-- **F8 pointwise estimate** (route L846-848): for a chart-0 point with
`h_{O_Y(1)}` represented by `[a : b : 1]`, the height of `(φ x0)^n = π(y)`'s
`λ`-coordinate differs from `n * h_{O_Y(1)}` by at most `n * finrank * log 2`. -/
theorem f8_first_equality_chart0 (n : ℕ) (hn : 0 < n)
    (φ : Chart0Ring n →+* K)
    (hrel : (φ (x0 n)) ^ n + (φ (x1 n)) ^ n = 1) :
    |Height.logHeight₁ ((φ (x0 n)) ^ n)
      - (n : ℝ) * Height.logHeight ![(φ (x0 n)), (φ (x1 n)), 1]|
      ≤ (n : ℝ) * ((Module.finrank ℚ K : ℝ) * Real.log 2) := by
  set a : K := φ (x0 n) with ha
  set b : K := φ (x1 n) with hb
  have hrel' : a ^ n + b ^ n = 1 := hrel
  have hn0 : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  set F : ℝ := (Module.finrank ℚ K : ℝ) * Real.log 2 with hF
  have hF0 : 0 ≤ F := by
    rw [hF]
    positivity
  have h23 : Height.logHeight ![a, 1] ≤ Height.logHeight ![a, b, 1] + F := by
    refine logHeight_le_of_arch_two (u := (![a, 1] : Fin 2 → K))
      (w := (![a, b, 1] : Fin 3 → K)) ?_ ?_ ?_ ?_
    · intro h
      simpa using congrFun h 1
    · intro h
      simpa using congrFun h 2
    · intro v
      exact sup_fin2_le_sup_fin3 (v := v.val) a b
    · intro v
      have hS0 : 0 ≤ (⨆ j : Fin 3, v (![a, b, 1] j)) :=
        Real.iSup_nonneg (fun j => AbsoluteValue.nonneg v.1 _)
      exact le_trans (sup_fin2_le_sup_fin3 (v := v.1) a b)
        (le_mul_of_one_le_left hS0 (by norm_num))
  have h32 : Height.logHeight ![a, b, 1] ≤ Height.logHeight ![a, 1] + F := by
    refine logHeight_le_of_arch_two (u := (![a, b, 1] : Fin 3 → K))
      (w := (![a, 1] : Fin 2 → K)) ?_ ?_ ?_ ?_
    · intro h
      simpa using congrFun h 2
    · intro h
      simpa using congrFun h 1
    · intro v
      exact sup_fin3_le_sup_fin2_nonarch (v := v.val)
        (Height.AdmissibleAbsValues.isNonarchimedean v.val v.property) hn0 hrel'
    · intro v
      exact sup_fin3_le_two_sup_fin2_arch (v := v.1) hn hrel'
  have habs : |Height.logHeight ![a, 1] - Height.logHeight ![a, b, 1]| ≤ F := by
    rw [abs_sub_le_iff]
    exact ⟨by linarith, by linarith⟩
  have hpow : Height.logHeight₁ (a ^ n) = (n : ℝ) * Height.logHeight₁ a :=
    Height.logHeight₁_pow a n
  have ha1 : Height.logHeight₁ a = Height.logHeight ![a, 1] :=
    Height.logHeight₁_eq_logHeight a
  have hsub : Height.logHeight₁ (a ^ n) - (n : ℝ) * Height.logHeight ![a, b, 1]
      = (n : ℝ) * (Height.logHeight ![a, 1] - Height.logHeight ![a, b, 1]) := by
    rw [hpow, ha1]; ring
  rw [hsub, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))]
  exact mul_le_mul_of_nonneg_left habs (by positivity)

#print axioms f8_first_equality_chart0

/-! ## Scheme-level identification of `π(y)`'s chart coordinate -/

/-- For a chart-0 K-point `φ : Chart0Ring n →+* K`, the composition
`Spec.map φ ≫ fermatChart0ToCurve n ≫ pi n` factors through the chart morphism
with `λ`-coordinate `(φ (x0 n))^n`.  This identifies `h(π(y))` in F8 with
`Height.logHeight₁ ((φ x0)^n)`. -/
theorem pi_chart0_coordinate (n : ℕ) {k : Type} [Field k] [NumberField k]
    (φ : Chart0Ring n →+* k)
    (hφ : φ.comp (algebraMap ℚ (Chart0Ring n)) = algebraMap ℚ k) :
    CategoryTheory.CategoryStruct.comp (Spec.map (CommRingCat.ofHom φ))
      (CategoryTheory.CategoryStruct.comp (fermatChart0ToCurve n) (pi n))
      = Mzk1G1ProjectiveLineTransitionActual.chartMorphism0 (R := k) ((φ (x0 n)) ^ n) := by
  rw [pi_ι0]
  show CategoryTheory.CategoryStruct.comp (Spec.map (CommRingCat.ofHom φ))
      (Mzk1G1ProjectiveLineTransitionActual.chartMorphism0 (R := Chart0Ring n) (x0 n ^ n))
      = Mzk1G1ProjectiveLineTransitionActual.chartMorphism0 (R := k) ((φ (x0 n)) ^ n)
  rw [chartMorphism0_comp (A := Chart0Ring n) (B := k) φ hφ (x0 n ^ n)]
  rw [map_pow]
#print axioms pi_chart0_coordinate

/-! ## Scheme-level corollary: `h(π(y))` versus `h_{O_Y(1)}(y)` -/

/-- The chart-0 height of a point of `P¹` in the `λ`-chart. -/
def p1ChartHeight {k : Type*} [Field k] [NumberField k] (a : k) : ℝ := Height.logHeight₁ a

/-- Scheme-level F8 first equality: for the chart-0 point `y = Spec.map (ofHom φ)`,
`h(π(y)) = p1ChartHeight ((φ x0)^n)` by `pi_chart0_coordinate`, and this differs from
`n * h_{O_Y(1)}(y)` (with `h_{O_Y(1)}(y) = Height.logHeight ![φ x0, φ x1, 1]`) by at most
`n * finrank * log 2`. -/
theorem f8_pi_height_chart0 (n : ℕ) (hn : 0 < n) {k : Type} [Field k] [NumberField k]
    (φ : Chart0Ring n →+* k)
    (hφ : φ.comp (algebraMap ℚ (Chart0Ring n)) = algebraMap ℚ k)
    (hrel : (φ (x0 n)) ^ n + (φ (x1 n)) ^ n = 1) :
    |p1ChartHeight ((φ (x0 n)) ^ n)
      - (n : ℝ) * Height.logHeight ![(φ (x0 n)), (φ (x1 n)), 1]|
      ≤ (n : ℝ) * ((Module.finrank ℚ k : ℝ) * Real.log 2) := by
  have h := f8_first_equality_chart0 n hn φ hrel
  simpa [p1ChartHeight] using h

#print axioms f8_pi_height_chart0

end LeanFormal.IUT.XiFPaper.F8PiActual
end