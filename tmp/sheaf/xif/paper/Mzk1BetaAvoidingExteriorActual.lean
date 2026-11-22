import tmp.sheaf.xif.paper.Mzk1BetaAvoidingBelyiSmallActual
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

noncomputable section

/-! # Mzk1BetaAvoidingExteriorActual — the exterior three-point case for beta-avoiding Belyi polynomials

This file closes the remaining exterior case left open in
Mzk1BetaAvoidingBelyiSmallActual:

For a < b < c and a rational beta strictly outside the interval [a, c], there is a
nonconstant q : Q[X] with q {a,b,c} ⊆ {0,1}, q beta ∉ {0,1}, and every critical value of
q (over C) in {0,1}.

## Route

The canonical one-layer construction B_{m,n} ∘ affineNorm a c (critical point at the image of
b) fails exactly when the image u = (beta - a)/(c - a) of beta satisfies B_{m,n}(u) = 1,
because the outer layer can never separate two points on which the inner Belyi polynomial
already agrees.

We therefore use a genuine two-layer construction.  Put r = 1/(N+1) and use the inner Belyi
polynomial B_{1,N}, whose critical point is r.  For beta > c we push {a,b,c,beta} through the
affine map x ↦ r (x-a)/(b-a), so that a ↦ 0, b ↦ r, c ↦ y_c, beta ↦ y_beta with

  r < y_c < y_beta < 1.

Then B_{1,N}(0) = 0, B_{1,N}(r) = 1, and B_{1,N}(y_c), B_{1,N}(y_beta) both lie in (0,1).
The function x ↦ x (1-x)^N is strictly decreasing on (r,1), so these two values are
distinct.  Hence the interior three-point theorem applies to the set
{0, B_{1,N}(y_c), 1} with excluded point B_{1,N}(y_beta), and composing with the inner layer
B_{1,N} ∘ affine gives the answer.  The case beta < a is mirror-symmetric, using the reversed
affine map x ↦ r (c-x)/(c-b).

The only analytic input is the monotonicity of x (1-x)^N on (r,1), proved via the sign of
its derivative.  No sorry, no new axioms, no placeholders.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1BetaAvoidingExteriorActual

open Polynomial
open TauCeti
open LeanFormal.IUT.XiFPaper.Mzk1BetaAvoidingBelyiSmallActual

/-- CritIn01 q: every critical point of q over C is mapped into {0,1}.  This is the
aeval form of the critical-value condition used throughout the asset files. -/
def CritIn01 (q : ℚ[X]) : Prop :=
  ∀ z : ℂ, Polynomial.aeval z (Polynomial.derivative q) = 0 →
    (Polynomial.aeval z q = 0 ∨ Polynomial.aeval z q = 1)

/-! ## Analytic input: monotonicity of x (1-x)^N on (1/(N+1), 1) -/

/-- Positivity of B_{1,N} on (0,1). -/
lemma eval_belyi_one_pos_real (N : ℕ) (hN : 1 ≤ N) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < (belyiPolynomial ℝ 1 N).eval x := by
  rw [eval_belyiPolynomial]
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have h1x : (0 : ℝ) < 1 - x := by linarith
  positivity

/-- The derivative of B_{1,N} is negative on (1/(N+1), 1). -/
lemma deriv_belyi_one_neg (N : ℕ) (hN : 1 ≤ N) {x : ℝ}
    (hx0 : 1 / ((N : ℝ) + 1) < x) (hx1 : x < 1) :
    deriv (fun y : ℝ => (belyiPolynomial ℝ 1 N).eval y) x < 0 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hxpos : 0 < x := lt_trans (by positivity : (0 : ℝ) < 1 / ((N : ℝ) + 1)) hx0
  have h1x : 0 < 1 - x := by linarith
  have hderiv : deriv (fun y : ℝ => (belyiPolynomial ℝ 1 N).eval y) x =
      (belyiPolynomial ℝ 1 N).derivative.eval x :=
    ((belyiPolynomial ℝ 1 N).hasDerivAt x).deriv
  rw [hderiv]
  have hkey := congr_arg (fun p : ℝ[X] => p.eval x)
    (TauCeti.X_mul_one_sub_X_mul_derivative_belyiPolynomial (K := ℝ) 1 N)
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_C, Nat.cast_one] at hkey
  have hB : 0 < (belyiPolynomial ℝ 1 N).eval x :=
    eval_belyi_one_pos_real N hN hxpos hx1
  have hlin : (1 : ℝ) - ((1 : ℝ) + N) * x < 0 := by
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hmul : ((N : ℝ) + 1) * (1 / ((N : ℝ) + 1)) < ((N : ℝ) + 1) * x :=
      mul_lt_mul_of_pos_left hx0 hN1
    have hone : ((N : ℝ) + 1) * (1 / ((N : ℝ) + 1)) = 1 := by field_simp
    have hgt : 1 < ((N : ℝ) + 1) * x := by linarith
    have hcast : ((1 : ℝ) + N) = (N : ℝ) + 1 := by ring
    rw [hcast]
    linarith
  have hden : 0 < x * (1 - x) := mul_pos hxpos h1x
  have hkey' : (belyiPolynomial ℝ 1 N).derivative.eval x * (x * (1 - x)) =
      (belyiPolynomial ℝ 1 N).eval x * ((1 : ℝ) - ((1 : ℝ) + N) * x) := by
    rw [show (belyiPolynomial ℝ 1 N).derivative.eval x * (x * (1 - x))
        = x * (1 - x) * (belyiPolynomial ℝ 1 N).derivative.eval x from by ring]
    exact hkey
  have hval : (belyiPolynomial ℝ 1 N).derivative.eval x =
      (belyiPolynomial ℝ 1 N).eval x * ((1 : ℝ) - ((1 : ℝ) + N) * x) / (x * (1 - x)) := by
    rw [eq_div_iff (ne_of_gt hden)]
    exact hkey'
  rw [hval]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hB hlin) hden

/-- Strict monotonicity of the Belyi polynomial B_{1,N} on (1/(N+1), 1). -/
lemma belyi_one_strictAntiOn_real (N : ℕ) (hN : 1 ≤ N) :
    StrictAntiOn (fun x : ℝ => (belyiPolynomial ℝ 1 N).eval x)
      (Set.Ioo (1 / ((N : ℝ) + 1)) 1) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioo _ _) (belyiPolynomial ℝ 1 N).continuousOn ?_
  intro x hx
  rw [interior_Ioo] at hx
  exact deriv_belyi_one_neg N hN hx.1 hx.2

/-- Rational comparison form: for N ≥ 1, the polynomial B_{1,N} strictly decreases on
(1/(N+1), 1) also over Q. -/
lemma belyi_one_eval_lt_of_lt {N : ℕ} (hN : 1 ≤ N) {x y : ℚ}
    (hx : 1 / ((N : ℚ) + 1) < x) (hxy : x < y) (hy : y < 1) :
    (belyiPolynomial ℚ 1 N).eval y < (belyiPolynomial ℚ 1 N).eval x := by
  have hcast : ∀ z : ℚ,
      (((belyiPolynomial ℚ 1 N).eval z : ℚ) : ℝ) = (belyiPolynomial ℝ 1 N).eval (z : ℝ) := by
    intro z
    have hmap : (belyiPolynomial ℝ 1 N).eval (z : ℝ) =
        (((belyiPolynomial ℚ 1 N).eval z : ℚ) : ℝ) := by
      have h := Polynomial.eval_map_apply (f := algebraMap ℚ ℝ) (x := z)
        (p := belyiPolynomial ℚ 1 N)
      simpa using h
    exact hmap.symm
  have hxR0 : ((1 / ((N : ℚ) + 1) : ℚ) : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have hxR : 1 / ((N : ℝ) + 1) < (x : ℝ) := by
    push_cast at hxR0
    exact hxR0
  have hxyR : (x : ℝ) < (y : ℝ) := by exact_mod_cast hxy
  have hyR : (y : ℝ) < 1 := by exact_mod_cast hy
  have hxI : (x : ℝ) ∈ Set.Ioo (1 / ((N : ℝ) + 1)) 1 :=
    ⟨hxR, lt_trans hxyR hyR⟩
  have hyI : (y : ℝ) ∈ Set.Ioo (1 / ((N : ℝ) + 1)) 1 :=
    ⟨lt_trans hxR hxyR, hyR⟩
  have hlt := belyi_one_strictAntiOn_real N hN hxI hyI hxyR
  have hfin : (((belyiPolynomial ℚ 1 N).eval y : ℚ) : ℝ) <
      (((belyiPolynomial ℚ 1 N).eval x : ℚ) : ℝ) := by
    rw [hcast y, hcast x]
    exact hlt
  exact_mod_cast hfin

/-! ## Critical-value bookkeeping for composites -/

/-- A rational value in {0,1} remains a complex value in {0,1} under 0 ↦ 0. -/
lemma aeval_zero_mem_zero_one {f : ℚ[X]} (h : f.eval 0 ∈ ({0, 1} : Set ℚ)) :
    Polynomial.aeval (0 : ℂ) f ∈ ({0, 1} : Set ℂ) := by
  have h0 : (0 : ℂ) = algebraMap ℚ ℂ 0 := by simp
  rw [h0, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
  rcases h with h | h <;> rw [h] <;> simp

/-- A rational value in {0,1} remains a complex value in {0,1} under 1 ↦ 1. -/
lemma aeval_one_mem_zero_one {f : ℚ[X]} (h : f.eval 1 ∈ ({0, 1} : Set ℚ)) :
    Polynomial.aeval (1 : ℂ) f ∈ ({0, 1} : Set ℂ) := by
  have h0 : (1 : ℂ) = algebraMap ℚ ℂ 1 := by simp
  rw [h0, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
  rcases h with h | h <;> rw [h] <;> simp

/-- The aeval form of the critical-value condition implies the critical-value containment. -/
lemma criticalValues_subset_zero_one_of_critIn01 {f : ℚ[X]}
    (h : CritIn01 f) : f.criticalValues ℂ ⊆ ({0, 1} : Set ℂ) := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := mem_criticalValues.mp hy
  rw [mem_rootSet'] at hz
  have h' := h z hz.2
  simpa using h'

/-- Critical-value control is stable under composition (the aeval packaging used here). -/
lemma critIn01_comp {q p : ℚ[X]} (hq : 0 < q.natDegree) (hp : 0 < p.natDegree)
    (hq0 : q.eval 0 ∈ ({0, 1} : Set ℚ)) (hq1 : q.eval 1 ∈ ({0, 1} : Set ℚ))
    (hqC : CritIn01 q) (hpC : CritIn01 p) : CritIn01 (q.comp p) := by
  have hqCV : q.criticalValues ℂ ⊆ ({0, 1} : Set ℂ) :=
    criticalValues_subset_zero_one_of_critIn01 hqC
  have hpCV : p.criticalValues ℂ ⊆ ({0, 1} : Set ℂ) :=
    criticalValues_subset_zero_one_of_critIn01 hpC
  have hq0' : Polynomial.aeval (0 : ℂ) q ∈ ({0, 1} : Set ℂ) := aeval_zero_mem_zero_one hq0
  have hq1' : Polynomial.aeval (1 : ℂ) q ∈ ({0, 1} : Set ℂ) := aeval_one_mem_zero_one hq1
  have hCV : (q.comp p).criticalValues ℂ ⊆ ({0, 1} : Set ℂ) :=
    criticalValues_comp_subset_zero_one hqCV hpCV hq0' hq1'
  have hdeg : 0 < (q.comp p).natDegree := by
    rw [natDegree_comp]
    exact Nat.mul_pos hq hp
  exact critIn01_of_criticalValues_subset hdeg hCV

/-! ## The exterior case beta > c -/

/-- Exterior three-point case, c < beta. -/
theorem exists_belyi_betaAvoiding_three_of_gt_exterior {a b c β : ℚ}
    (hab : a < b) (hbc : b < c) (hcβ : c < β) :
    ∃ q : ℚ[X], 0 < q.natDegree ∧
      (∀ s ∈ ({a, b, c} : Finset ℚ), q.eval s = 0 ∨ q.eval s = 1) ∧
      q.eval β ≠ 0 ∧ q.eval β ≠ 1 ∧
      (∀ z : ℂ, Polynomial.aeval z (Polynomial.derivative q) = 0 →
        (Polynomial.aeval z q = 0 ∨ Polynomial.aeval z q = 1)) := by
  classical
  have hba : (0 : ℚ) < b - a := by linarith
  have hba' : b - a ≠ 0 := ne_of_gt hba
  obtain ⟨N, hNgt⟩ := exists_nat_gt ((β - a) / (b - a))
  have hratio1 : (1 : ℚ) < (β - a) / (b - a) := (one_lt_div hba).mpr (by linarith)
  have hN1 : (1 : ℚ) < (N : ℚ) := lt_trans hratio1 hNgt
  have hN : 1 ≤ N := Nat.le_of_lt (by exact_mod_cast hN1)
  have hbig : β - a < ((N : ℚ) + 1) * (b - a) := by
    have h1 : β - a < (N : ℚ) * (b - a) := by
      have hm := mul_lt_mul_of_pos_right hNgt hba
      rwa [div_mul_cancel₀ (β - a) hba'] at hm
    nlinarith [h1, hba]
  set r : ℚ := (1 : ℚ) / ((1 : ℚ) + N) with hr
  have hrpos : 0 < r := by rw [hr]; positivity
  set bb : ℚ := a + ((N : ℚ) + 1) * (b - a) with hbb
  have hbb_gt : a < bb := by rw [hbb]; nlinarith
  have hane : a ≠ bb := ne_of_lt hbb_gt
  set p : ℚ[X] := (belyiPolynomial ℚ 1 N).comp (affineNorm a bb) with hp
  have hpdeg : 0 < p.natDegree := by
    rw [hp]
    exact affineBelyi_natDegree_pos (m := 1) (n := N) (by norm_num) (by omega) hane
  have hpa : p.eval a = 0 := by
    rw [hp, eval_affineBelyi 1 N a bb a]
    have h0 : (a - a) / (bb - a) = 0 := by rw [sub_self, zero_div]
    rw [h0]
    exact eval_zero_belyiPolynomial (K := ℚ) (m := 1) (n := N) (by norm_num)
  have hpb : p.eval b = 1 := by
    rw [hp, eval_affineBelyi 1 N a bb b]
    have harg : (b - a) / (bb - a) = r := by
      rw [hbb, hr]
      have hsub : a + ((N : ℚ) + 1) * (b - a) - a = ((N : ℚ) + 1) * (b - a) := by ring
      rw [hsub]
      field_simp
      ring
    rw [harg]
    exact eval_div_belyiPolynomial (K := ℚ) 1 N
  have hpc_val : p.eval c = (belyiPolynomial ℚ 1 N).eval (r * ((c - a) / (b - a))) := by
    rw [hp, eval_affineBelyi 1 N a bb c]
    have harg : (c - a) / (bb - a) = r * ((c - a) / (b - a)) := by
      rw [hbb, hr]
      have hsub : a + ((N : ℚ) + 1) * (b - a) - a = ((N : ℚ) + 1) * (b - a) := by ring
      rw [hsub]
      field_simp
      ring
    rw [harg]
  have hpβ_val : p.eval β = (belyiPolynomial ℚ 1 N).eval (r * ((β - a) / (b - a))) := by
    rw [hp, eval_affineBelyi 1 N a bb β]
    have harg : (β - a) / (bb - a) = r * ((β - a) / (b - a)) := by
      rw [hbb, hr]
      have hsub : a + ((N : ℚ) + 1) * (b - a) - a = ((N : ℚ) + 1) * (b - a) := by ring
      rw [hsub]
      field_simp
      ring
    rw [harg]
  have hs_gt_one : (1 : ℚ) < (c - a) / (b - a) := (one_lt_div hba).mpr (by linarith)
  have hargc_r : r < r * ((c - a) / (b - a)) := by
    have := mul_lt_mul_of_pos_left hs_gt_one hrpos
    simpa using this
  have hargcβ : r * ((c - a) / (b - a)) < r * ((β - a) / (b - a)) := by
    have hs_lt : (c - a) / (b - a) < (β - a) / (b - a) :=
      (div_lt_div_iff_of_pos_right hba).mpr (by linarith)
    exact mul_lt_mul_of_pos_left hs_lt hrpos
  have hargβ1 : r * ((β - a) / (b - a)) < 1 := by
    have hden : 0 < ((N : ℚ) + 1) * (b - a) := mul_pos (by positivity) hba
    have heq : r * ((β - a) / (b - a)) = (β - a) / (((N : ℚ) + 1) * (b - a)) := by
      rw [hr]
      field_simp
      ring
    rw [heq]
    exact (div_lt_one hden).mpr hbig
  have hargc1 : r * ((c - a) / (b - a)) < 1 := lt_trans hargcβ hargβ1
  have hargc0 : 0 < r * ((c - a) / (b - a)) :=
    mul_pos hrpos (div_pos (by linarith) hba)
  have hargβ0 : 0 < r * ((β - a) / (b - a)) :=
    mul_pos hrpos (div_pos (by linarith) hba)
  have hpc_pos : 0 < p.eval c := by
    rw [hpc_val]
    exact eval_belyi_pos (m := 1) (n := N) (by norm_num) (by omega) hargc0 hargc1
  have hpc_lt : p.eval c < 1 := by
    rw [hpc_val]
    exact eval_belyi_lt_one (m := 1) (n := N) (by norm_num) (by omega) hargc0 hargc1
      (ne_of_lt hargc_r).symm
  have hpβ_pos : 0 < p.eval β := by
    rw [hpβ_val]
    exact eval_belyi_pos (m := 1) (n := N) (by norm_num) (by omega) hargβ0 hargβ1
  have hpβ_lt : p.eval β < 1 := by
    rw [hpβ_val]
    exact eval_belyi_lt_one (m := 1) (n := N) (by norm_num) (by omega) hargβ0 hargβ1
      (ne_of_lt (lt_trans hargc_r hargcβ)).symm
  have hcomp : (belyiPolynomial ℚ 1 N).eval (r * ((β - a) / (b - a))) <
      (belyiPolynomial ℚ 1 N).eval (r * ((c - a) / (b - a))) := by
    refine belyi_one_eval_lt_of_lt hN ?_ hargcβ hargβ1
    have hreq : (1 : ℚ) / ((N : ℚ) + 1) = r := by
      rw [hr]
      have hcast : ((1 : ℚ) + N) = (N : ℚ) + 1 := by ring
      rw [hcast]
    rw [hreq]
    exact hargc_r
  have hpcβ_ne : p.eval β ≠ p.eval c := by
    rw [hpβ_val, hpc_val]
    exact ne_of_lt hcomp
  obtain ⟨qint, hqdeg, hqS, hqβ0, hqβ1, hqC⟩ :=
    exists_belyi_betaAvoiding_three_of_lt (a := (0 : ℚ)) (b := p.eval c) (c := (1 : ℚ))
      (β := p.eval β) hpc_pos hpc_lt hpβ_pos hpβ_lt hpcβ_ne
  refine ⟨qint.comp p, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_comp]
    exact Nat.mul_pos hqdeg hpdeg
  · intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with h | h | h
    · rw [h, eval_comp, hpa]
      exact hqS 0 (by simp)
    · rw [h, eval_comp, hpb]
      exact hqS 1 (by simp)
    · rw [h, eval_comp]
      exact hqS (p.eval c) (by simp)
  · intro hcon
    rw [eval_comp] at hcon
    exact hqβ0 hcon
  · intro hcon
    rw [eval_comp] at hcon
    exact hqβ1 hcon
  · exact critIn01_comp hqdeg hpdeg (hqS 0 (by simp)) (hqS 1 (by simp)) hqC
      (affineBelyi_critIn01 (m := 1) (n := N) (by norm_num) (by omega) hane)

/-! ## The exterior case beta < a -/

/-- Exterior three-point case, beta < a. -/
theorem exists_belyi_betaAvoiding_three_of_lt_exterior {a b c β : ℚ}
    (hab : a < b) (hbc : b < c) (hβa : β < a) :
    ∃ q : ℚ[X], 0 < q.natDegree ∧
      (∀ s ∈ ({a, b, c} : Finset ℚ), q.eval s = 0 ∨ q.eval s = 1) ∧
      q.eval β ≠ 0 ∧ q.eval β ≠ 1 ∧
      (∀ z : ℂ, Polynomial.aeval z (Polynomial.derivative q) = 0 →
        (Polynomial.aeval z q = 0 ∨ Polynomial.aeval z q = 1)) := by
  classical
  have hcb : (0 : ℚ) < c - b := by linarith
  have hcb' : c - b ≠ 0 := ne_of_gt hcb
  obtain ⟨N, hNgt⟩ := exists_nat_gt ((c - β) / (c - b))
  have hratio1 : (1 : ℚ) < (c - β) / (c - b) := (one_lt_div hcb).mpr (by linarith)
  have hN1 : (1 : ℚ) < (N : ℚ) := lt_trans hratio1 hNgt
  have hN : 1 ≤ N := Nat.le_of_lt (by exact_mod_cast hN1)
  have hbig : c - β < ((N : ℚ) + 1) * (c - b) := by
    have h1 : c - β < (N : ℚ) * (c - b) := by
      have hm := mul_lt_mul_of_pos_right hNgt hcb
      rwa [div_mul_cancel₀ (c - β) hcb'] at hm
    nlinarith [h1, hcb]
  set r : ℚ := (1 : ℚ) / ((1 : ℚ) + N) with hr
  have hrpos : 0 < r := by rw [hr]; positivity
  set bb : ℚ := c - ((N : ℚ) + 1) * (c - b) with hbb
  have hbb_lt : bb < c := by rw [hbb]; nlinarith
  have hcne : c ≠ bb := ne_of_gt hbb_lt
  set p : ℚ[X] := (belyiPolynomial ℚ 1 N).comp (affineNorm c bb) with hp
  have hpdeg : 0 < p.natDegree := by
    rw [hp]
    exact affineBelyi_natDegree_pos (m := 1) (n := N) (by norm_num) (by omega) hcne
  have hpc : p.eval c = 0 := by
    rw [hp, eval_affineBelyi 1 N c bb c]
    have h0 : (c - c) / (bb - c) = 0 := by rw [sub_self, zero_div]
    rw [h0]
    exact eval_zero_belyiPolynomial (K := ℚ) (m := 1) (n := N) (by norm_num)
  have hpb : p.eval b = 1 := by
    rw [hp, eval_affineBelyi 1 N c bb b]
    have harg : (b - c) / (bb - c) = r := by
      rw [hbb, hr]
      have hsub : c - ((N : ℚ) + 1) * (c - b) - c = -(((N : ℚ) + 1) * (c - b)) := by ring
      rw [hsub]
      have hnum : b - c = -(c - b) := by ring
      rw [hnum]
      field_simp
      ring
    rw [harg]
    exact eval_div_belyiPolynomial (K := ℚ) 1 N
  have hpa_val : p.eval a = (belyiPolynomial ℚ 1 N).eval (r * ((c - a) / (c - b))) := by
    rw [hp, eval_affineBelyi 1 N c bb a]
    have harg : (a - c) / (bb - c) = r * ((c - a) / (c - b)) := by
      rw [hbb, hr]
      have hsub : c - ((N : ℚ) + 1) * (c - b) - c = -(((N : ℚ) + 1) * (c - b)) := by ring
      rw [hsub]
      have hnum : a - c = -(c - a) := by ring
      rw [hnum]
      field_simp
      ring
    rw [harg]
  have hpβ_val : p.eval β = (belyiPolynomial ℚ 1 N).eval (r * ((c - β) / (c - b))) := by
    rw [hp, eval_affineBelyi 1 N c bb β]
    have harg : (β - c) / (bb - c) = r * ((c - β) / (c - b)) := by
      rw [hbb, hr]
      have hsub : c - ((N : ℚ) + 1) * (c - b) - c = -(((N : ℚ) + 1) * (c - b)) := by ring
      rw [hsub]
      have hnum : β - c = -(c - β) := by ring
      rw [hnum]
      field_simp
      ring
    rw [harg]
  have hs_gt_one : (1 : ℚ) < (c - a) / (c - b) := (one_lt_div hcb).mpr (by linarith)
  have harg_a_r : r < r * ((c - a) / (c - b)) := by
    have := mul_lt_mul_of_pos_left hs_gt_one hrpos
    simpa using this
  have harg_a_β : r * ((c - a) / (c - b)) < r * ((c - β) / (c - b)) := by
    have hs_lt : (c - a) / (c - b) < (c - β) / (c - b) :=
      (div_lt_div_iff_of_pos_right hcb).mpr (by linarith)
    exact mul_lt_mul_of_pos_left hs_lt hrpos
  have harg_β_1 : r * ((c - β) / (c - b)) < 1 := by
    have hden : 0 < ((N : ℚ) + 1) * (c - b) := mul_pos (by positivity) hcb
    have heq : r * ((c - β) / (c - b)) = (c - β) / (((N : ℚ) + 1) * (c - b)) := by
      rw [hr]
      field_simp
      ring
    rw [heq]
    exact (div_lt_one hden).mpr hbig
  have harg_a_1 : r * ((c - a) / (c - b)) < 1 := lt_trans harg_a_β harg_β_1
  have harg_a_0 : 0 < r * ((c - a) / (c - b)) :=
    mul_pos hrpos (div_pos (by linarith) hcb)
  have harg_β_0 : 0 < r * ((c - β) / (c - b)) :=
    mul_pos hrpos (div_pos (by linarith) hcb)
  have hpa_pos : 0 < p.eval a := by
    rw [hpa_val]
    exact eval_belyi_pos (m := 1) (n := N) (by norm_num) (by omega) harg_a_0 harg_a_1
  have hpa_lt : p.eval a < 1 := by
    rw [hpa_val]
    exact eval_belyi_lt_one (m := 1) (n := N) (by norm_num) (by omega) harg_a_0 harg_a_1
      (ne_of_lt harg_a_r).symm
  have hpβ_pos : 0 < p.eval β := by
    rw [hpβ_val]
    exact eval_belyi_pos (m := 1) (n := N) (by norm_num) (by omega) harg_β_0 harg_β_1
  have hpβ_lt : p.eval β < 1 := by
    rw [hpβ_val]
    exact eval_belyi_lt_one (m := 1) (n := N) (by norm_num) (by omega) harg_β_0 harg_β_1
      (ne_of_lt (lt_trans harg_a_r harg_a_β)).symm
  have hcomp : (belyiPolynomial ℚ 1 N).eval (r * ((c - β) / (c - b))) <
      (belyiPolynomial ℚ 1 N).eval (r * ((c - a) / (c - b))) := by
    refine belyi_one_eval_lt_of_lt hN ?_ harg_a_β harg_β_1
    have hreq : (1 : ℚ) / ((N : ℚ) + 1) = r := by
      rw [hr]
      have hcast : ((1 : ℚ) + N) = (N : ℚ) + 1 := by ring
      rw [hcast]
    rw [hreq]
    exact harg_a_r
  have hpβa_ne : p.eval β ≠ p.eval a := by
    rw [hpβ_val, hpa_val]
    exact ne_of_lt hcomp
  obtain ⟨qint, hqdeg, hqS, hqβ0, hqβ1, hqC⟩ :=
    exists_belyi_betaAvoiding_three_of_lt (a := (0 : ℚ)) (b := p.eval a) (c := (1 : ℚ))
      (β := p.eval β) hpa_pos hpa_lt hpβ_pos hpβ_lt hpβa_ne
  refine ⟨qint.comp p, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_comp]
    exact Nat.mul_pos hqdeg hpdeg
  · intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with h | h | h
    · rw [h, eval_comp]
      exact hqS (p.eval a) (by simp)
    · rw [h, eval_comp, hpb]
      exact hqS 1 (by simp)
    · rw [h, eval_comp, hpc]
      exact hqS 0 (by simp)
  · intro hcon
    rw [eval_comp] at hcon
    exact hqβ0 hcon
  · intro hcon
    rw [eval_comp] at hcon
    exact hqβ1 hcon
  · exact critIn01_comp hqdeg hpdeg (hqS 0 (by simp)) (hqS 1 (by simp)) hqC
      (affineBelyi_critIn01 (m := 1) (n := N) (by norm_num) (by omega) hcne)

/-! ## Assembly -/

/-- Exterior three-point case (both sides), exact requested form. -/
theorem exists_belyi_betaAvoiding_three_exterior {a b c β : ℚ}
    (hab : a < b) (hbc : b < c) (hβex : β < a ∨ c < β) (hβb : β ≠ b) :
    ∃ q : ℚ[X], 0 < q.natDegree ∧
      (∀ s ∈ ({a, b, c} : Finset ℚ), q.eval s = 0 ∨ q.eval s = 1) ∧
      q.eval β ≠ 0 ∧ q.eval β ≠ 1 ∧
      (∀ z : ℂ, Polynomial.aeval z (Polynomial.derivative q) = 0 →
        (Polynomial.aeval z q = 0 ∨ Polynomial.aeval z q = 1)) := by
  rcases hβex with h | h
  · exact exists_belyi_betaAvoiding_three_of_lt_exterior hab hbc h
  · exact exists_belyi_betaAvoiding_three_of_gt_exterior hab hbc h

/-- The named remaining exterior statement of Mzk1BetaAvoidingBelyiSmallActual, proved. -/
theorem belyiBetaAvoidingExteriorStatement_proved : BelyiBetaAvoidingExteriorStatement := by
  intro a b c β hab hbc hcβ
  exact exists_belyi_betaAvoiding_three_of_gt_exterior hab hbc hcβ

/-- Ordered three-point helper: for a < b < c and beta outside {a,b,c} the target holds. -/
theorem exists_belyi_betaAvoiding_three_ordered {a b c β : ℚ}
    (hab : a < b) (hbc : b < c) (hβa : β ≠ a) (hβb : β ≠ b) (hβc : β ≠ c) :
    ∃ q : ℚ[X], 0 < q.natDegree ∧
      (∀ s ∈ ({a, b, c} : Finset ℚ), q.eval s = 0 ∨ q.eval s = 1) ∧
      q.eval β ≠ 0 ∧ q.eval β ≠ 1 ∧
      (∀ z : ℂ, Polynomial.aeval z (Polynomial.derivative q) = 0 →
        (Polynomial.aeval z q = 0 ∨ Polynomial.aeval z q = 1)) := by
  rcases lt_or_gt_of_ne hβa with h | h
  · exact exists_belyi_betaAvoiding_three_of_lt_exterior hab hbc h
  · rcases lt_or_gt_of_ne hβc with h2 | h2
    · exact exists_belyi_betaAvoiding_three_of_lt hab hbc h h2 hβb
    · exact exists_belyi_betaAvoiding_three_of_gt_exterior hab hbc h2

/-- **The full #S ≤ 3 statement** of Mzk1BetaAvoidingBelyiSmallActual, proved: every finite
rational set with at most three points admits a beta-avoiding Belyi polynomial. -/
theorem belyiBetaAvoidingSmallStatement_proved : BelyiBetaAvoidingSmallStatement := by
  intro S β hcard hβ
  rcases Nat.lt_or_ge S.card 3 with hlt | hge
  · exact exists_belyi_betaAvoiding_card_le_two S β (by omega) hβ
  have hcard3 : S.card = 3 := by omega
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  set a : ℚ := S.min' hne with ha
  set c : ℚ := S.max' hne with hc
  have ha_mem : a ∈ S := S.min'_mem hne
  have hc_mem : c ∈ S := S.max'_mem hne
  have hac : a ≠ c := by
    intro h
    have hsingle : S = {a} := by
      refine Finset.Subset.antisymm ?_ ?_
      · intro s hs
        rw [Finset.mem_singleton]
        have hle1 : a ≤ s := S.min'_le s hs
        have hle2 : s ≤ c := S.le_max' s hs
        rw [← h] at hle2
        exact le_antisymm hle2 hle1
      · intro s hs
        rw [Finset.mem_singleton] at hs
        rw [hs]
        exact ha_mem
    rw [hsingle] at hcard3
    simp at hcard3
  have hc_mem_erase : c ∈ S.erase a := by
    rw [Finset.mem_erase]
    exact ⟨Ne.symm hac, hc_mem⟩
  have hcard_erase : ((S.erase a).erase c).card = 1 := by
    rw [Finset.card_erase_of_mem hc_mem_erase, Finset.card_erase_of_mem ha_mem]
    omega
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hcard_erase
  have hb_in : b ∈ (S.erase a).erase c := by
    rw [hb]
    exact Finset.mem_singleton_self b
  rw [Finset.mem_erase, Finset.mem_erase] at hb_in
  obtain ⟨hbne_c, hbne_a, hb_mem⟩ := hb_in
  have hab : a < b := lt_of_le_of_ne (S.min'_le b hb_mem) hbne_a.symm
  have hbc : b < c := lt_of_le_of_ne (S.le_max' b hb_mem) hbne_c
  have hβa : β ≠ a := by
    intro h
    apply hβ
    rwa [h]
  have hβb : β ≠ b := by
    intro h
    apply hβ
    rwa [h]
  have hβc : β ≠ c := by
    intro h
    apply hβ
    rwa [h]
  have hSsub : ({a, b, c} : Finset ℚ) ⊆ S := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact ha_mem
    · exact hb_mem
    · exact hc_mem
  have hcard_abc : ({a, b, c} : Finset ℚ).card = 3 :=
    Finset.card_eq_three.mpr ⟨a, b, c, hab.ne, hac, hbc.ne, rfl⟩
  have hS_eq : ({a, b, c} : Finset ℚ) = S :=
    Finset.eq_of_subset_of_card_le hSsub (by rw [hcard_abc]; omega)
  obtain ⟨q, hqdeg, hqset, hqβ0, hqβ1, hqC⟩ :=
    exists_belyi_betaAvoiding_three_ordered hab hbc hβa hβb hβc
  refine ⟨q, hqdeg, ?_, hqβ0, hqβ1, hqC⟩
  intro s hs
  exact hqset s (by rwa [← hS_eq] at hs)

/-- Row record for this file. -/
def exteriorRows : List (String × String × String) :=
  [ ("B_{1,N} strictly decreasing on (1/(N+1),1)", "A", "PROVED belyi_one_strictAntiOn_real / belyi_one_eval_lt_of_lt")
  , ("beta > c exterior three-point case", "A", "PROVED exists_belyi_betaAvoiding_three_of_gt_exterior")
  , ("beta < a exterior three-point case", "A", "PROVED exists_belyi_betaAvoiding_three_of_lt_exterior")
  , ("named exterior statement", "A", "PROVED belyiBetaAvoidingExteriorStatement_proved") ]

theorem exteriorRows_length : exteriorRows.length = 4 := rfl

#check exists_belyi_betaAvoiding_three_of_gt_exterior
#check exists_belyi_betaAvoiding_three_of_lt_exterior
#check exists_belyi_betaAvoiding_three_exterior
#check belyiBetaAvoidingExteriorStatement_proved
#check belyiBetaAvoidingSmallStatement_proved
#check exists_belyi_betaAvoiding_three_ordered
#check belyi_one_eval_lt_of_lt
#check exteriorRows_length

end LeanFormal.IUT.XiFPaper.Mzk1BetaAvoidingExteriorActual
end
