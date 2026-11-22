import tmp.sheaf.xif.paper.Mzk1BetaAvoidingBelyiSmallActual
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

noncomputable section

/-! # Mzk1BetaAvoidingFoldActual — beta-avoiding rational Belyi for ALL finite S (fold induction)

This file implements the fold-induction argument of coord/ProblemA_FoldSkeleton.lean
with complete proofs: no sorry, no placeholders, no new axioms.

The target (BetaAvoidingAt S β) is: for every finite S ⊆ ℚ and every β ∉ S
there is a nonconstant q ∈ ℚ[X] with q(S) ⊆ {0,1}, q(β) ∉ {0,1}, and every
complex critical value of q in {0,1}.

Route (as in the skeleton):

1. Enlarge S by rational auxiliary points so that β is interior
   (exists_interior_superset).
2. Induction invariant InteriorGood S β: β ∉ S, points of S on both sides of
   β, and there is q with q(S) ⊆ {0,1}, 0 < q β < 1, CV01 q.
   * The fold step (fold_step) picks a = min S, b = second smallest point,
     c = max S with b < β < c, maps by an affine normalisation and applies
     B_{m,n} with (b-a)/(c-a) = m/(m+n).  On [r,1] (r = m/(m+n)) the Belyi
     polynomial is strictly decreasing, which gives injectivity on S \ {a},
     g a = g c = 0, g b = 1, 0 < g β < 1 and the strict card drop.
   * interiorGood_of_fold pulls the recursive solution back along g.
   * interiorGood_base handles #S ≤ 2 by a degree-one affine map, whose
     derivative is a nonzero constant, so CV01 is vacuous.
3. betaAvoiding_all assembles the result.

All analytic inputs (monotonicity of B_{m,n} on [m/(m+n), 1], value at the
critical point, critical-value containment) are proved or reused from the
green assets Mzk1BetaAvoidingBelyiSmallActual / TauCeti.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1BetaAvoidingFoldActual

open Polynomial
open TauCeti
open LeanFormal.IUT.XiFPaper.Mzk1BetaAvoidingBelyiSmallActual

/-! ## Statements -/

/-- All C-point critical values of q lie in {0,1}. -/
def CV01 (q : ℚ[X]) : Prop :=
  ∀ z : ℂ, aeval z (derivative q) = 0 → (aeval z q = 0 ∨ aeval z q = 1)

/-- Target for one pair: BelyiBetaAvoidingSmallStatement without the card bound. -/
def BetaAvoidingAt (S : Finset ℚ) (β : ℚ) : Prop :=
  ∃ q : ℚ[X], 0 < q.natDegree ∧ (∀ s ∈ S, q.eval s = 0 ∨ q.eval s = 1) ∧
    q.eval β ≠ 0 ∧ q.eval β ≠ 1 ∧ CV01 q

/-- Induction invariant: beta is not in S and has points of S on both sides. -/
def Interior (S : Finset ℚ) (β : ℚ) : Prop :=
  β ∉ S ∧ (∃ a ∈ S, a < β) ∧ (∃ c ∈ S, β < c)

/-- Conclusion carried by the induction: the value at beta is strictly inside (0,1). -/
def InteriorGood (S : Finset ℚ) (β : ℚ) : Prop :=
  ∃ q : ℚ[X], 0 < q.natDegree ∧ (∀ s ∈ S, q.eval s = 0 ∨ q.eval s = 1) ∧
    0 < q.eval β ∧ q.eval β < 1 ∧ CV01 q

/-- Fold data: a = min S, c = max S, b = second smallest point, and b < beta < c. -/
structure FoldTriple (S : Finset ℚ) (β a b c : ℚ) : Prop where
  ha : a ∈ S
  hb : b ∈ S
  hc : c ∈ S
  hmin : ∀ s ∈ S, a ≤ s
  hmax : ∀ s ∈ S, s ≤ c
  hgap : ∀ s ∈ S, s = a ∨ b ≤ s
  hab : a < b
  hbβ : b < β
  hβc : β < c

/-! ## 1. The Belyi polynomial on [r, 1] -/

/-- Strict decrease on [r,1], r = m/(m+n).  Derivative:
X (1-X) B' = B (m - (m+n) X); on (r,1) both X (1-X) and B are positive while
m - (m+n) X is negative. -/
theorem belyi_strictAntiOn_real (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    StrictAntiOn (fun x : ℝ => (belyiPolynomial ℝ m n).eval x)
      (Set.Icc ((m : ℝ) / ((m : ℝ) + n)) 1) := by
  have hmpos : 0 < m := by omega
  have hnpos : 0 < n := by omega
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hden : (0 : ℝ) < (m : ℝ) + n := by positivity
  have hr0 : 0 < (m : ℝ) / ((m : ℝ) + n) := div_pos hmR hden
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _) (belyiPolynomial ℝ m n).continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  obtain ⟨hxr, hx1⟩ := hx
  have hxpos : 0 < x := lt_trans hr0 hxr
  have h1x : 0 < 1 - x := by linarith
  have hxmul : 0 < x * (1 - x) := mul_pos hxpos h1x
  rw [Polynomial.deriv]
  have hkey := congr_arg (fun p : ℝ[X] => p.eval x)
    (TauCeti.X_mul_one_sub_X_mul_derivative_belyiPolynomial (K := ℝ) m n)
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_C] at hkey
  have hkey' : (belyiPolynomial ℝ m n).derivative.eval x * (x * (1 - x)) =
      (belyiPolynomial ℝ m n).eval x * ((m : ℝ) - ((m : ℝ) + n) * x) := by
    rw [show (belyiPolynomial ℝ m n).derivative.eval x * (x * (1 - x))
        = x * (1 - x) * (belyiPolynomial ℝ m n).derivative.eval x from by ring]
    exact hkey
  have hB : 0 < (belyiPolynomial ℝ m n).eval x := by
    rw [TauCeti.eval_belyiPolynomial]
    have hc : (0 : ℝ) <
        ((m : ℝ) + n) ^ (m + n) / ((m : ℝ) ^ m * (n : ℝ) ^ n) :=
      div_pos (pow_pos hden _) (mul_pos (pow_pos hmR m) (pow_pos hnR n))
    exact mul_pos (mul_pos hc (pow_pos hxpos m)) (pow_pos h1x n)
  have hlin : ((m : ℝ) - ((m : ℝ) + n) * x) < 0 := by
    have hmul := mul_lt_mul_of_pos_left hxr hden
    have h1 : ((m : ℝ) + n) * ((m : ℝ) / ((m : ℝ) + n)) = (m : ℝ) := by
      field_simp
    linarith
  have hval : (belyiPolynomial ℝ m n).derivative.eval x =
      (belyiPolynomial ℝ m n).eval x * ((m : ℝ) - ((m : ℝ) + n) * x) /
        (x * (1 - x)) := by
    rw [eq_div_iff (ne_of_gt hxmul)]
    exact hkey'
  rw [hval]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hB hlin) hxmul

/-- Cast of the rational Belyi value to the real one. -/
lemma belyi_eval_cast (m n : ℕ) (z : ℚ) :
    (((belyiPolynomial ℚ m n).eval z : ℚ) : ℝ) = (belyiPolynomial ℝ m n).eval (z : ℝ) := by
  have h : (belyiPolynomial ℝ m n).eval (z : ℝ) =
      (((belyiPolynomial ℚ m n).eval z : ℚ) : ℝ) := by
    rw [← TauCeti.map_belyiPolynomial (algebraMap ℚ ℝ) m n]
    exact Polynomial.eval_map_apply (p := belyiPolynomial ℚ m n)
      (f := algebraMap ℚ ℝ) (x := z)
  exact h.symm

/-- Rational form of the strict decrease. -/
theorem belyi_eval_lt_of_lt {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) {x y : ℚ}
    (hx : (m : ℚ) / ((m : ℚ) + n) ≤ x) (hxy : x < y) (hy : y ≤ 1) :
    (belyiPolynomial ℚ m n).eval y < (belyiPolynomial ℚ m n).eval x := by
  have hxR0 : (((m : ℚ) / ((m : ℚ) + n) : ℚ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hxR : (m : ℝ) / ((m : ℝ) + n) ≤ (x : ℝ) := by
    push_cast at hxR0
    exact hxR0
  have hxyR : (x : ℝ) < (y : ℝ) := by exact_mod_cast hxy
  have hyR : (y : ℝ) ≤ 1 := by exact_mod_cast hy
  have hxI : (x : ℝ) ∈ Set.Icc ((m : ℝ) / ((m : ℝ) + n)) 1 :=
    ⟨hxR, le_of_lt (lt_of_lt_of_le hxyR hyR)⟩
  have hyI : (y : ℝ) ∈ Set.Icc ((m : ℝ) / ((m : ℝ) + n)) 1 :=
    ⟨le_trans hxR hxyR.le, hyR⟩
  have hlt := belyi_strictAntiOn_real m n hm hn hxI hyI hxyR
  have hfin : (((belyiPolynomial ℚ m n).eval y : ℚ) : ℝ) <
      (((belyiPolynomial ℚ m n).eval x : ℚ) : ℝ) := by
    rw [belyi_eval_cast m n y, belyi_eval_cast m n x]
    exact hlt
  exact_mod_cast hfin

/-- B(r) = 1. -/
theorem belyi_eval_rho {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (belyiPolynomial ℚ m n).eval ((m : ℚ) / ((m : ℚ) + n)) = 1 := by
  simp

/-- C-point critical values of B_{m,n} are in {0,1}. -/
theorem belyi_cv01 (m n : ℕ) : CV01 (belyiPolynomial ℚ m n) := by
  by_cases hmn : m + n = 0
  · have hm0 : m = 0 := by omega
    have hn0 : n = 0 := by omega
    subst hm0
    subst hn0
    intro z hz
    right
    have hone : belyiPolynomial ℚ 0 0 = 1 := by
      simp [TauCeti.belyiPolynomial]
    rw [hone]
    simp
  · have hdeg : 0 < (belyiPolynomial ℚ m n).natDegree := by
      rw [TauCeti.natDegree_belyiPolynomial]
      omega
    exact critIn01_of_criticalValues_subset hdeg
      (TauCeti.criticalValues_belyiPolynomial_subset ℂ m n)

/-! ## 2. Closure of CV01 -/

/-- Precomposition with an affine map adds no critical point. -/
theorem cv01_comp_affine {q : ℚ[X]} (hq : CV01 q) (u v : ℚ) (hu : u ≠ 0) :
    CV01 (q.comp (C u * X + C v)) := by
  intro z hz
  have hderiv : derivative (q.comp (C u * X + C v)) =
      (derivative q).comp (C u * X + C v) * C u := by
    rw [derivative_comp]
    simp
    ring
  have huC : algebraMap ℚ ℂ u ≠ 0 := by
    intro hzero
    apply hu
    have h1 : algebraMap ℚ ℂ u = algebraMap ℚ ℂ (0 : ℚ) := by rw [hzero, map_zero]
    exact (algebraMap ℚ ℂ).injective h1
  have hz' : aeval z ((derivative q).comp (C u * X + C v)) = 0 := by
    have h := hz
    rw [hderiv] at h
    simp only [map_mul, aeval_C] at h
    exact (mul_eq_zero.mp h).resolve_right huC
  have hz'' : aeval (aeval z (C u * X + C v)) (derivative q) = 0 := by
    rw [aeval_comp] at hz'
    exact hz'
  have hq' := hq _ hz''
  simpa [aeval_comp] using hq'

/-- Composition law for CV01. -/
theorem cv01_comp {q g : ℚ[X]} (hq : CV01 q) (hg : CV01 g)
    (h0 : q.eval 0 = 0 ∨ q.eval 0 = 1) (h1 : q.eval 1 = 0 ∨ q.eval 1 = 1) :
    CV01 (q.comp g) := by
  intro z hz
  rw [aeval_comp]
  have hderiv : aeval z (derivative (q.comp g)) =
      aeval (aeval z g) (derivative q) * aeval z (derivative g) := by
    rw [derivative_comp]
    simp only [map_mul, aeval_comp]
    ring
  rw [hderiv] at hz
  have hq0 : aeval (0 : ℂ) q = 0 ∨ aeval (0 : ℂ) q = 1 := by
    have hval : aeval (0 : ℂ) q = ((q.eval 0 : ℚ) : ℂ) := by
      have h := aeval_algebraMap_apply_eq_algebraMap_eval (A := ℂ) (R := ℚ) (0 : ℚ) q
      simpa using h
    rw [hval]
    rcases h0 with h | h
    · left; rw [h]; norm_num
    · right; rw [h]; norm_num
  have hq1 : aeval (1 : ℂ) q = 0 ∨ aeval (1 : ℂ) q = 1 := by
    have hval : aeval (1 : ℂ) q = ((q.eval 1 : ℚ) : ℂ) := by
      have h := aeval_algebraMap_apply_eq_algebraMap_eval (A := ℂ) (R := ℚ) (1 : ℚ) q
      simpa using h
    rw [hval]
    rcases h1 with h | h
    · left; rw [h]; norm_num
    · right; rw [h]; norm_num
  rcases mul_eq_zero.mp hz with h | h
  · exact hq (aeval z g) h
  · rcases hg z h with hgz | hgz
    · rw [hgz]; exact hq0
    · rw [hgz]; exact hq1

/-! ## 3. The fold step -/

/-- One fold. -/
theorem fold_step {S : Finset ℚ} {β a b c : ℚ} (hβ : β ∉ S) (T : FoldTriple S β a b c) :
    ∃ g : ℚ[X], 0 < g.natDegree ∧ CV01 g ∧
      (S.image (fun s => g.eval s)).card < S.card ∧
      (0 : ℚ) ∈ S.image (fun s => g.eval s) ∧
      (1 : ℚ) ∈ S.image (fun s => g.eval s) ∧
      0 < g.eval β ∧ g.eval β < 1 ∧
      g.eval β ∉ S.image (fun s => g.eval s) := by
  classical
  have hab : a < b := T.hab
  have hbβ : b < β := T.hbβ
  have hβc : β < c := T.hβc
  have hbc : b < c := lt_trans hbβ hβc
  have haβ : a < β := lt_trans hab hbβ
  have hac : a < c := lt_trans hab hbc
  have hacne : a ≠ c := hac.ne
  have hca : 0 < c - a := by linarith
  have hca_ne : c - a ≠ 0 := hca.ne'
  have hbca : 0 < (b - a) / (c - a) := div_pos (by linarith) hca
  have hbca1 : (b - a) / (c - a) < 1 := by
    rw [div_lt_one hca]
    linarith
  obtain ⟨m, n, hm, hn, hmn_eq⟩ := Rat.exists_eq_div_add_of_pos_of_lt_one hbca hbca1
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have hmn_eq' : (m : ℚ) / ((m : ℚ) + n) = (b - a) / (c - a) := by
    simpa using hmn_eq.symm
  set g : ℚ[X] := (belyiPolynomial ℚ m n).comp (affineNorm a c) with hg
  have hgdeg : 0 < g.natDegree :=
    affineBelyi_natDegree_pos (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn) hacne
  have hgcv : CV01 g := affineBelyi_critIn01 hm1 hn1 hacne
  have hga : g.eval a = 0 := by
    rw [hg, eval_affineBelyi]
    have h0 : (a - a) / (c - a) = 0 := by rw [sub_self, zero_div]
    rw [h0]
    exact eval_zero_belyiPolynomial hm n
  have hgc : g.eval c = 0 := by
    rw [hg, eval_affineBelyi, div_self hca_ne]
    exact eval_one_belyiPolynomial m hn
  have hgb : g.eval b = 1 := by
    rw [hg, eval_affineBelyi, hmn_eq]
    simp
  have huβ0 : 0 < (β - a) / (c - a) := div_pos (by linarith) hca
  have huβ1 : (β - a) / (c - a) < 1 := by
    rw [div_lt_one hca]
    linarith
  have huβne : (β - a) / (c - a) ≠ (m : ℚ) / ((m : ℚ) + n) := by
    intro heq
    apply hβ
    have h1 : (β - a) / (c - a) = (b - a) / (c - a) := by rw [heq, hmn_eq']
    have h2 : β - a = b - a := by
      have h4 := congrArg (fun t : ℚ => t * (c - a)) h1
      field_simp at h4
      exact h4
    have h4 : β = b := by linarith
    rw [h4]
    exact T.hb
  have hgβpos : 0 < g.eval β := by
    rw [hg, eval_affineBelyi]
    exact eval_belyi_pos (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn) huβ0 huβ1
  have hgβlt : g.eval β < 1 := by
    rw [hg, eval_affineBelyi]
    exact eval_belyi_lt_one (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)
      huβ0 huβ1 huβne
  have hβnot : g.eval β ∉ S.image (fun s => g.eval s) := by
    intro hmem
    obtain ⟨s, hs, hgs⟩ := Finset.mem_image.mp hmem
    have hgβval : g.eval β =
        (belyiPolynomial ℚ m n).eval ((β - a) / (c - a)) := by
      rw [hg, eval_affineBelyi]
    have hgsval : g.eval s =
        (belyiPolynomial ℚ m n).eval ((s - a) / (c - a)) := by
      rw [hg, eval_affineBelyi]
    rcases T.hgap s hs with hsa | hbs
    · rw [hsa, hga] at hgs
      linarith
    · have hsβ : s ≠ β := by
        intro h
        exact hβ (h ▸ hs)
      have hsc : s ≤ c := T.hmax s hs
      rcases lt_or_gt_of_ne hsβ with hslt | hsgt
      · have hrle : (m : ℚ) / ((m : ℚ) + n) ≤ (s - a) / (c - a) := by
          rw [hmn_eq']
          exact div_le_div_of_nonneg_right (by linarith : b - a ≤ s - a) hca.le
        have hsβlt : (s - a) / (c - a) < (β - a) / (c - a) :=
          div_lt_div_of_pos_right (by linarith : s - a < β - a) hca
        have huβ1' : (β - a) / (c - a) ≤ 1 := le_of_lt huβ1
        have hlt := belyi_eval_lt_of_lt hm1 hn1 hrle hsβlt huβ1'
        rw [hgβval, hgsval] at hgs
        linarith
      · have hrleβ : (m : ℚ) / ((m : ℚ) + n) ≤ (β - a) / (c - a) := by
          rw [hmn_eq']
          exact div_le_div_of_nonneg_right (by linarith : b - a ≤ β - a) hca.le
        have hβs : (β - a) / (c - a) < (s - a) / (c - a) :=
          div_lt_div_of_pos_right (by linarith : β - a < s - a) hca
        have hs1 : (s - a) / (c - a) ≤ 1 := by
          rw [div_le_one hca]
          linarith
        have hlt := belyi_eval_lt_of_lt hm1 hn1 hrleβ hβs hs1
        rw [hgβval, hgsval] at hgs
        linarith
  have hcard : (S.image (fun s => g.eval s)).card < S.card := by
    have hmemc : g.eval c ∈ (S.erase a).image (fun s => g.eval s) :=
      Finset.mem_image_of_mem (f := fun s => g.eval s) (a := c)
        (Finset.mem_erase.mpr ⟨hac.ne', T.hc⟩)
    have hmem0 : g.eval a ∈ (S.erase a).image (fun s => g.eval s) := by
      simpa [hga, hgc] using hmemc
    have himg : S.image (fun s => g.eval s) = (S.erase a).image (fun s => g.eval s) := by
      have hS : S = insert a (S.erase a) := (Finset.insert_erase T.ha).symm
      conv_lhs => rw [hS]
      rw [Finset.image_insert]
      exact Finset.insert_eq_of_mem hmem0
    have h1 := Finset.card_image_le (s := S.erase a) (f := fun s => g.eval s)
    have h2 := Finset.card_erase_of_mem T.ha
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨a, T.ha⟩
    rw [himg]
    omega
  exact ⟨g, hgdeg, hgcv, hcard, by rw [← hga]; exact Finset.mem_image_of_mem _ T.ha,
    by rw [← hgb]; exact Finset.mem_image_of_mem _ T.hb, hgβpos, hgβlt, hβnot⟩

/-- The image pair is again interior. -/
theorem interior_image_of_fold {S : Finset ℚ} {β : ℚ} {g : ℚ[X]}
    (h0 : (0 : ℚ) ∈ S.image (fun s => g.eval s))
    (h1 : (1 : ℚ) ∈ S.image (fun s => g.eval s))
    (hpos : 0 < g.eval β) (hlt : g.eval β < 1)
    (hnot : g.eval β ∉ S.image (fun s => g.eval s)) :
    Interior (S.image (fun s => g.eval s)) (g.eval β) :=
  ⟨hnot, ⟨0, h0, hpos⟩, ⟨1, h1, hlt⟩⟩

/-- Pull the conclusion back along one fold. -/
theorem interiorGood_of_fold {S : Finset ℚ} {β : ℚ} {g : ℚ[X]}
    (hdeg : 0 < g.natDegree) (hcv : CV01 g)
    (h0 : (0 : ℚ) ∈ S.image (fun s => g.eval s))
    (h1 : (1 : ℚ) ∈ S.image (fun s => g.eval s))
    (hrec : InteriorGood (S.image (fun s => g.eval s)) (g.eval β)) :
    InteriorGood S β := by
  obtain ⟨q, hqdeg, hqS, hqpos, hqlt, hqcv⟩ := hrec
  have hq0 : q.eval 0 = 0 ∨ q.eval 0 = 1 := by
    obtain ⟨s, hs, hgs⟩ := Finset.mem_image.mp h0
    have h := hqS (g.eval s) (Finset.mem_image_of_mem _ hs)
    rwa [hgs] at h
  have hq1 : q.eval 1 = 0 ∨ q.eval 1 = 1 := by
    obtain ⟨s, hs, hgs⟩ := Finset.mem_image.mp h1
    have h := hqS (g.eval s) (Finset.mem_image_of_mem _ hs)
    rwa [hgs] at h
  refine ⟨q.comp g, ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_comp]
    exact Nat.mul_pos hqdeg hdeg
  · intro s hs
    rw [eval_comp]
    exact hqS (g.eval s) (Finset.mem_image_of_mem _ hs)
  · rw [eval_comp]
    exact hqpos
  · rw [eval_comp]
    exact hqlt
  · exact cv01_comp hqcv hcv hq0 hq1

/-! ## 4. Choosing the triple, mirror, base case -/

/-- For |S| >= 3 and beta interior, either S or -S admits a fold triple. -/
theorem exists_foldTriple_or_neg {S : Finset ℚ} {β : ℚ} (hI : Interior S β)
    (h3 : 3 ≤ S.card) :
    (∃ a b c, FoldTriple S β a b c) ∨
      (∃ a b c, FoldTriple (S.image (fun s => -s)) (-β) a b c) := by
  classical
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha, hmin⟩ : ∃ a ∈ S, ∀ s ∈ S, a ≤ s :=
    ⟨S.min' hne, Finset.min'_mem S hne, fun s hs => S.min'_le s hs⟩
  obtain ⟨c, hc, hmax⟩ : ∃ c ∈ S, ∀ s ∈ S, s ≤ c :=
    ⟨S.max' hne, Finset.max'_mem S hne, fun s hs => S.le_max' s hs⟩
  obtain ⟨u, huS, huβ⟩ := hI.2.1
  obtain ⟨v, hvS, hβv⟩ := hI.2.2
  have hβc : β < c := lt_of_lt_of_le hβv (hmax v hvS)
  have haβ : a < β := lt_of_le_of_lt (hmin u huS) huβ
  have hne2 : (S.erase a).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hc1 := Finset.card_erase_of_mem ha
    rw [hempty] at hc1
    simp at hc1
    omega
  obtain ⟨b, hbE, hminE⟩ : ∃ b ∈ S.erase a, ∀ s ∈ S.erase a, b ≤ s :=
    ⟨(S.erase a).min' hne2, Finset.min'_mem _ hne2, fun s hs => Finset.min'_le _ s hs⟩
  have hb : b ∈ S := (Finset.mem_erase.mp hbE).2
  have hbne : b ≠ a := (Finset.mem_erase.mp hbE).1
  have hab : a < b := lt_of_le_of_ne (hmin b hb) hbne.symm
  have hgap : ∀ s ∈ S, s = a ∨ b ≤ s := by
    intro s hs
    by_cases h : s = a
    · exact Or.inl h
    · exact Or.inr (hminE s (Finset.mem_erase.mpr ⟨h, hs⟩))
  have hbc : b < c := by
    rcases lt_or_ge b c with h | h
    · exact h
    · exfalso
      have hsub : S ⊆ ({a, b} : Finset ℚ) := by
        intro s hs
        rcases hgap s hs with hsa | hbs
        · simp [hsa]
        · have hsc : s ≤ c := hmax s hs
          have hsb : s = b := le_antisymm (le_trans hsc h) hbs
          simp [hsb]
      have hcard2 : S.card ≤ 2 := by
        have hle := Finset.card_le_card hsub
        have hpair : ({a, b} : Finset ℚ).card ≤ 2 := by
          have := Finset.card_insert_le a ({b} : Finset ℚ)
          simpa using this
        omega
      omega
  by_cases hbβ : b < β
  · refine Or.inl ⟨a, b, c, ?_⟩
    exact ⟨ha, hb, hc, hmin, hmax, hgap, hab, hbβ, hβc⟩
  · have hβb : β < b := lt_of_le_of_ne (le_of_not_gt hbβ) (by
      intro h
      exact hI.1 (h ▸ hb))
    have hne3 : (S.erase c).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      have hc1 := Finset.card_erase_of_mem hc
      rw [hempty] at hc1
      simp at hc1
      omega
    obtain ⟨c2, hc2E, hmaxE⟩ : ∃ c2 ∈ S.erase c, ∀ s ∈ S.erase c, s ≤ c2 :=
      ⟨(S.erase c).max' hne3, Finset.max'_mem _ hne3, fun s hs => Finset.le_max' _ s hs⟩
    have hc2 : c2 ∈ S := (Finset.mem_erase.mp hc2E).2
    have hc2ne : c2 ≠ c := (Finset.mem_erase.mp hc2E).1
    have hc2c : c2 < c := lt_of_le_of_ne (hmax c2 hc2) hc2ne
    have hbc2 : b ≤ c2 := hmaxE b (Finset.mem_erase.mpr ⟨hbc.ne, hb⟩)
    have hβc2 : β < c2 := lt_of_lt_of_le hβb hbc2
    refine Or.inr ⟨-c, -c2, -a, ?_⟩
    refine ⟨Finset.mem_image_of_mem _ hc, Finset.mem_image_of_mem _ hc2,
      Finset.mem_image_of_mem _ ha, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro s hs
      obtain ⟨s0, hs0, rfl⟩ := Finset.mem_image.mp hs
      exact neg_le_neg (hmax s0 hs0)
    · intro s hs
      obtain ⟨s0, hs0, rfl⟩ := Finset.mem_image.mp hs
      exact neg_le_neg (hmin s0 hs0)
    · intro s hs
      obtain ⟨s0, hs0, rfl⟩ := Finset.mem_image.mp hs
      by_cases h : s0 = c
      · exact Or.inl (by rw [h])
      · exact Or.inr (neg_le_neg (hmaxE s0 (Finset.mem_erase.mpr ⟨h, hs0⟩)))
    · exact neg_lt_neg hc2c
    · exact neg_lt_neg hβc2
    · exact neg_lt_neg haβ

/-- Mirror. -/
theorem interiorGood_of_neg {S : Finset ℚ} {β : ℚ}
    (h : InteriorGood (S.image (fun s => -s)) (-β)) : InteriorGood S β := by
  obtain ⟨q, hdeg, hqS, hqpos, hqlt, hqcv⟩ := h
  have hneg : (C (-1) * X + C (0 : ℚ) : ℚ[X]) = -X := by simp
  refine ⟨q.comp (-X), ?_, ?_, ?_, ?_, ?_⟩
  · rw [natDegree_comp, natDegree_neg, natDegree_X, Nat.mul_one]
    exact hdeg
  · intro s hs
    rw [eval_comp]
    simpa using hqS (-s) (Finset.mem_image_of_mem _ hs)
  · rw [eval_comp]
    simpa using hqpos
  · rw [eval_comp]
    simpa using hqlt
  · have hcv : CV01 (q.comp (C (-1) * X + C (0 : ℚ))) :=
      cv01_comp_affine hqcv (-1) 0 (by norm_num)
    simpa [hneg] using hcv

/-- Mirror preserves the invariant. -/
theorem interior_neg {S : Finset ℚ} {β : ℚ} (hI : Interior S β) :
    Interior (S.image (fun s => -s)) (-β) := by
  obtain ⟨hβS, ⟨a, haS, haβ⟩, ⟨c, hcS, hβc⟩⟩ := hI
  refine ⟨?_, ⟨-c, Finset.mem_image_of_mem _ hcS, by linarith⟩,
    ⟨-a, Finset.mem_image_of_mem _ haS, by linarith⟩⟩
  intro hmem
  obtain ⟨s, hsS, hseq⟩ := Finset.mem_image.mp hmem
  apply hβS
  have h1 : s = β := by linarith
  rwa [← h1]

/-- Base case: #S ≤ 2 with β interior is a degree-one affine map. -/
theorem interiorGood_base {S : Finset ℚ} {β : ℚ} (hI : Interior S β) (h2 : S.card ≤ 2) :
    InteriorGood S β := by
  classical
  obtain ⟨hβS, ⟨a, haS, haβ⟩, ⟨c, hcS, hβc⟩⟩ := hI
  have hac : a < c := lt_trans haβ hβc
  have hacne : a ≠ c := hac.ne
  have hca_ne : c - a ≠ 0 := sub_ne_zero.mpr hac.ne'
  have hSsub : ({a, c} : Finset ℚ) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact haS
    · exact hcS
  have hSeq : S = ({a, c} : Finset ℚ) := by
    refine (Finset.eq_of_subset_of_card_le hSsub ?_).symm
    rw [Finset.card_pair hacne]
    exact h2
  refine ⟨affineNorm a c, ?_, ?_, ?_, ?_, ?_⟩
  · rw [affineNorm_natDegree hacne]
    norm_num
  · intro s hs
    rw [hSeq] at hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with hsa | hsc
    · left
      rw [hsa, affineNorm_eval]
      simp
    · right
      rw [hsc, affineNorm_eval, div_self (sub_ne_zero.mpr hac.ne')]
  · rw [affineNorm_eval]
    exact div_pos (by linarith) (by linarith)
  · rw [affineNorm_eval, div_lt_one (by linarith : (0 : ℚ) < c - a)]
    linarith
  · intro z hz
    exfalso
    have hderiv : derivative (affineNorm a c) = C ((c - a)⁻¹) := by
      rw [affineNorm]
      simp
    rw [hderiv, aeval_C] at hz
    have hne : ((c - a)⁻¹ : ℚ) ≠ 0 := inv_ne_zero hca_ne
    have hneC : algebraMap ℚ ℂ ((c - a)⁻¹) ≠ 0 := by
      intro hzero
      apply hne
      have h1 : algebraMap ℚ ℂ ((c - a)⁻¹) = algebraMap ℚ ℂ (0 : ℚ) := by
        rw [hzero, map_zero]
      exact (algebraMap ℚ ℂ).injective h1
    exact hneC hz

/-! ## 5. Induction and the general statement -/

/-- Main induction on a card bound. -/
theorem interiorGood_of_interior :
    ∀ (n : ℕ) (S : Finset ℚ) (β : ℚ), S.card ≤ n → Interior S β → InteriorGood S β := by
  intro n
  induction n with
  | zero =>
    intro S β hcard hI
    obtain ⟨a, ha, -⟩ := hI.2.1
    have hSempty : S = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [hSempty] at ha
    simp at ha
  | succ n ih =>
    intro S β hcard hI
    by_cases h2 : S.card ≤ 2
    · exact interiorGood_base hI h2
    · have h3 : 3 ≤ S.card := by omega
      rcases exists_foldTriple_or_neg hI h3 with ⟨a, b, c, hT⟩ | ⟨a, b, c, hT⟩
      · obtain ⟨g, hgdeg, hgcv, hgcard, hg0, hg1, hgpos, hglt, hgnim⟩ :=
          fold_step hI.1 hT
        have hcard' : (S.image (fun s => g.eval s)).card ≤ n := by omega
        have hI' : Interior (S.image (fun s => g.eval s)) (g.eval β) :=
          interior_image_of_fold hg0 hg1 hgpos hglt hgnim
        exact interiorGood_of_fold hgdeg hgcv hg0 hg1 (ih _ _ hcard' hI')
      · obtain ⟨g, hgdeg, hgcv, hgcard, hg0, hg1, hgpos, hglt, hgnim⟩ :=
          fold_step (interior_neg hI).1 hT
        have hcardT : (S.image (fun s => -s)).card = S.card := by
          rw [Finset.card_image_iff]
          intro x _ y _ hxy
          exact neg_injective hxy
        have hcard' : ((S.image (fun s => -s)).image (fun s => g.eval s)).card ≤ n := by
          omega
        have hI' : Interior ((S.image (fun s => -s)).image (fun s => g.eval s))
            (g.eval (-β)) :=
          interior_image_of_fold hg0 hg1 hgpos hglt hgnim
        have hrec := ih _ _ hcard' hI'
        have hgoodT : InteriorGood (S.image (fun s => -s)) (-β) :=
          interiorGood_of_fold hgdeg hgcv hg0 hg1 hrec
        exact interiorGood_of_neg hgoodT

/-- Auxiliary points. -/
theorem exists_interior_superset (S : Finset ℚ) (β : ℚ) (hβ : β ∉ S) :
    ∃ T : Finset ℚ, S ⊆ T ∧ Interior T β := by
  refine ⟨insert (β - 1) (insert (β + 1) S), ?_, ?_⟩
  · intro s hs
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hs)
  · refine ⟨?_, ?_, ?_⟩
    · simp only [Finset.mem_insert]
      intro h
      rcases h with h | h | h
      · linarith
      · linarith
      · exact hβ h
    · exact ⟨β - 1, by simp, by linarith⟩
    · exact ⟨β + 1, by simp, by linarith⟩

/-- Same q works for a subset. -/
theorem betaAvoidingAt_of_interiorGood {S T : Finset ℚ} {β : ℚ} (hST : S ⊆ T)
    (h : InteriorGood T β) : BetaAvoidingAt S β := by
  obtain ⟨q, hdeg, hqT, hpos, hlt, hcv⟩ := h
  exact ⟨q, hdeg, fun s hs => hqT s (hST hs), ne_of_gt hpos, ne_of_lt hlt, hcv⟩

/-- **Problem A for every finite S.** -/
theorem betaAvoiding_all (S : Finset ℚ) (β : ℚ) (hβ : β ∉ S) : BetaAvoidingAt S β := by
  obtain ⟨T, hST, hI⟩ := exists_interior_superset S β hβ
  exact betaAvoidingAt_of_interiorGood hST (interiorGood_of_interior T.card T β le_rfl hI)

end LeanFormal.IUT.XiFPaper.Mzk1BetaAvoidingFoldActual
end