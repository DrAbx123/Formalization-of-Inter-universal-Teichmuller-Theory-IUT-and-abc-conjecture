import tmp.sheaf.xif.paper.Mzk1BetaAvoidingBelyiSmallActual
import Mathlib.Tactic

/-! # Problem A skeleton — beta-avoiding rational Belyi for ALL finite S (fold induction)

SKELETON ONLY.  Every proof except the final assembly is `sorry`.  NOT compiled.
Kept outside `tmp/sheaf/xif/paper` on purpose, so the citable checker and the watchdog
queue never see it.  Source: coord/OPEN-HARD-PROBLEMS.md, Problem A.

Argument.
1. Enlarge S by rational auxiliary points so that beta has points of S on both sides.
   A q that works for the larger set works for S.
2. Fold step (|S| >= 3).  a = min S, c = max S, b = second smallest point, with b < beta
   (otherwise mirror by x |-> -x).  A affine with A a = 0, A c = 1, r = A b = m/(m+n),
   g = B_{m,n} o A.  No point of A(S) lies in (0,r), and B is strictly decreasing on
   [r,1].  So g is injective on (S inter [b,c)) union {beta}, g a = g c = 0, g b = 1,
   0 < g beta < 1, and |g(S)| = |S| - 1.  The invariant is preserved.
3. |S| = 2: affine map.  Compose the steps; critical values stay in {0,1} because
   0 and 1 belong to every intermediate set.

Why beta must be interior: for s1 < beta < s2 with q(s_i) in {0,1} and all critical
values in {0,1}, an interior extremum on [s1,s2] forces 0 < q(beta) < 1.  So the
induction carries `0 < q beta < 1`, not just `q beta notin {0,1}`.

Reusable existing assets (names as read on 2026-11-10):
* TauCeti: `belyiPolynomial`, `eval_belyiPolynomial`, `natDegree_belyiPolynomial`,
  `criticalValues_belyiPolynomial_subset`, `criticalValues_comp_subset`.
* `Mzk1BelyiCanonicalActual`: `belyi_eval_zero`, `belyi_eval_one`, `belyi_natDegree_pos`.
* `Mzk1BelyiCvBridgeActual.belyiPolynomial_critIn01` (C-point critical values).
* `Mzk1BetaAvoidingExteriorActual.belyi_one_strictAntiOn_real` (template: the (1,N) case
  of `belyi_strictAntiOn_real` below).
* `Mzk1GChoiceIntegrationActual.rat_rep` (r in (0,1) is m/(m+n) with m,n >= 1).
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ProblemAFoldSkeleton

open Polynomial
open TauCeti

/-! ## Statements -/

/-- All C-point critical values of `q` lie in {0,1}. -/
def CV01 (q : ℚ[X]) : Prop :=
  ∀ z : ℂ, aeval z (derivative q) = 0 → (aeval z q = 0 ∨ aeval z q = 1)

/-- Target for one pair: `BelyiBetaAvoidingSmallStatement` without the card bound. -/
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

/-- Strict decrease on [r,1], r = m/(m+n).
Proof: derivative is c * x^(m-1) * (1-x)^(n-1) * (m - (m+n) x) < 0 on (r,1);
`strictAntiOn_of_deriv_neg`.  Generalises the existing (1,N) lemma. -/
theorem belyi_strictAntiOn_real (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    StrictAntiOn (fun x : ℝ => (belyiPolynomial ℝ m n).eval x)
      (Set.Icc ((m : ℝ) / ((m : ℝ) + n)) 1) := by
  sorry

/-- Rational form.  Proof: cast to R and use `belyi_strictAntiOn_real`. -/
theorem belyi_eval_lt_of_lt {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) {x y : ℚ}
    (hx : (m : ℚ) / ((m : ℚ) + n) ≤ x) (hxy : x < y) (hy : y ≤ 1) :
    (belyiPolynomial ℚ m n).eval y < (belyiPolynomial ℚ m n).eval x := by
  sorry

/-- B(r) = 1.  Proof: `eval_belyiPolynomial` and field arithmetic. -/
theorem belyi_eval_rho {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (belyiPolynomial ℚ m n).eval ((m : ℚ) / ((m : ℚ) + n)) = 1 := by
  sorry

/-- C-point critical values of B_{m,n} are in {0,1}.  Proof: existing bridge lemma. -/
theorem belyi_cv01 (m n : ℕ) : CV01 (belyiPolynomial ℚ m n) := by
  sorry

/-! ## 2. Closure of `CV01` -/

/-- Precomposition with an affine map adds no critical point.
Proof: derivative_comp; the inner derivative is the nonzero constant u. -/
theorem cv01_comp_affine {q : ℚ[X]} (hq : CV01 q) (u v : ℚ) (hu : u ≠ 0) :
    CV01 (q.comp (C u * X + C v)) := by
  sorry

/-- Composition law.  Proof: (q o g)' z = g' z * q' (g z); if g' z = 0 then
g z is 0 or 1 and `h0`/`h1` apply; otherwise `hq` at g z. -/
theorem cv01_comp {q g : ℚ[X]} (hq : CV01 q) (hg : CV01 g)
    (h0 : q.eval 0 = 0 ∨ q.eval 0 = 1) (h1 : q.eval 1 = 0 ∨ q.eval 1 = 1) :
    CV01 (q.comp g) := by
  sorry

/-! ## 3. The fold step -/

/-- One fold.  g := (belyiPolynomial Q m n).comp (C (c-a)⁻¹ * X + C (-(a/(c-a)))),
with (m,n) from `rat_rep` applied to r = (b-a)/(c-a).
Proof: every s in S is a or lies in [b,c] (`hgap`), so A s is 0 or lies in [r,1];
`belyi_eval_lt_of_lt` gives injectivity on [r,1] and 0 < g beta < 1; g a = g c = 0
gives the strict card drop. -/
theorem fold_step {S : Finset ℚ} {β a b c : ℚ} (hβ : β ∉ S) (T : FoldTriple S β a b c) :
    ∃ g : ℚ[X], 0 < g.natDegree ∧ CV01 g ∧
      (S.image (fun s => g.eval s)).card < S.card ∧
      (0 : ℚ) ∈ S.image (fun s => g.eval s) ∧
      (1 : ℚ) ∈ S.image (fun s => g.eval s) ∧
      0 < g.eval β ∧ g.eval β < 1 ∧
      g.eval β ∉ S.image (fun s => g.eval s) := by
  sorry

/-- The image pair is again interior.  Proof: 0 and 1 are the two witnesses. -/
theorem interior_image_of_fold {S : Finset ℚ} {β : ℚ} {g : ℚ[X]}
    (h0 : (0 : ℚ) ∈ S.image (fun s => g.eval s))
    (h1 : (1 : ℚ) ∈ S.image (fun s => g.eval s))
    (hpos : 0 < g.eval β) (hlt : g.eval β < 1)
    (hnot : g.eval β ∉ S.image (fun s => g.eval s)) :
    Interior (S.image (fun s => g.eval s)) (g.eval β) := by
  sorry

/-- Pull the conclusion back along one fold.  Proof: q.comp g; `natDegree_comp`;
`cv01_comp` with q 0, q 1 in {0,1} from `h0`, `h1`. -/
theorem interiorGood_of_fold {S : Finset ℚ} {β : ℚ} {g : ℚ[X]}
    (hdeg : 0 < g.natDegree) (hcv : CV01 g)
    (h0 : (0 : ℚ) ∈ S.image (fun s => g.eval s))
    (h1 : (1 : ℚ) ∈ S.image (fun s => g.eval s))
    (hrec : InteriorGood (S.image (fun s => g.eval s)) (g.eval β)) :
    InteriorGood S β := by
  sorry

/-! ## 4. Choosing the triple, mirror, base case -/

/-- For |S| >= 3 and beta interior, the second smallest point is left of beta either in S
or in -S.  Proof: a = S.min', b = (S.erase a).min', c = S.max'.  If b < beta take
(a,b,c).  Otherwise beta < b, so the second largest point of S is right of beta, which is
the same statement for -S and -beta. -/
theorem exists_foldTriple_or_neg {S : Finset ℚ} {β : ℚ} (hI : Interior S β)
    (h3 : 3 ≤ S.card) :
    (∃ a b c, FoldTriple S β a b c) ∨
      (∃ a b c, FoldTriple (S.image (fun s => -s)) (-β) a b c) := by
  sorry

/-- Mirror.  Proof: replace q by q.comp (-X); `cv01_comp_affine` with u = -1. -/
theorem interiorGood_of_neg {S : Finset ℚ} {β : ℚ}
    (h : InteriorGood (S.image (fun s => -s)) (-β)) : InteriorGood S β := by
  sorry

/-- Mirror preserves the invariant. -/
theorem interior_neg {S : Finset ℚ} {β : ℚ} (hI : Interior S β) :
    Interior (S.image (fun s => -s)) (-β) := by
  sorry

/-- Base case.  Proof: card <= 2 and beta interior give two points a < beta < c with every
point of S equal to a or c; q = C (c-a)⁻¹ * X + C (-(a/(c-a))) has no critical point. -/
theorem interiorGood_base {S : Finset ℚ} {β : ℚ} (hI : Interior S β) (h2 : S.card ≤ 2) :
    InteriorGood S β := by
  sorry

/-! ## 5. Induction and the general statement -/

/-- Main induction on a card bound.  Proof: induction n.  If card <= 2 use
`interiorGood_base`.  Otherwise `exists_foldTriple_or_neg`; in the first case
`fold_step` + `interior_image_of_fold` + IH + `interiorGood_of_fold`; in the second
case the same for -S, -beta (card of the image is <= card S), then `interiorGood_of_neg`. -/
theorem interiorGood_of_interior :
    ∀ (n : ℕ) (S : Finset ℚ) (β : ℚ), S.card ≤ n → Interior S β → InteriorGood S β := by
  sorry

/-- Auxiliary points.  Proof: T = insert (beta - 1) (insert (beta + 1) S). -/
theorem exists_interior_superset (S : Finset ℚ) (β : ℚ) (hβ : β ∉ S) :
    ∃ T : Finset ℚ, S ⊆ T ∧ Interior T β := by
  sorry

/-- Same q works for a subset; 0 < q beta < 1 gives the two inequalities. -/
theorem betaAvoidingAt_of_interiorGood {S T : Finset ℚ} {β : ℚ} (hST : S ⊆ T)
    (h : InteriorGood T β) : BetaAvoidingAt S β := by
  sorry

/-- **Problem A for every finite S.** -/
theorem betaAvoiding_all (S : Finset ℚ) (β : ℚ) (hβ : β ∉ S) : BetaAvoidingAt S β := by
  obtain ⟨T, hST, hI⟩ := exists_interior_superset S β hβ
  exact betaAvoidingAt_of_interiorGood hST (interiorGood_of_interior T.card T β le_rfl hI)

end LeanFormal.IUT.XiFPaper.ProblemAFoldSkeleton
end
