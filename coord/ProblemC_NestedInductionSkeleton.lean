import Mathlib

/-! # Problem C skeleton — nested induction of [Mzk1] Lemma 2.4 without Galois-stable sets

SKELETON ONLY.  Every proof is `sorry`.  NOT compiled.  Kept outside
`tmp/sheaf/xif/paper` on purpose.  Source: coord/OPEN-HARD-PROBLEMS.md, Problem C;
paper lines 163-206.

Changes against the paper's bookkeeping.
1. Measure (D, N): D = largest degree over Q of a point of S, N = number of points of
   degree D, lexicographic.  It replaces (m(S), d(S)).
2. No Galois-stable set.  At each step add the conjugates of alpha0 to S:
   S1 = S union roots(f0), S' = f0(S1) union f0(roots f0').  Every point of degree D in S'
   is the image of a point of degree D in S that is not a root of f0, so
   N(S') <= N(S1) - D <= N(S) - 1.  Only two facts are used: deg f0(alpha) <= deg alpha,
   and critical values have degree <= D - 1.
3. No infinite Galois descent.  For beta in a number field F the map is
   phi_Q o (x - beta); the Q-construction never mentions F.
4. Avoidance with the universal constant C = 4: after normalisation all roots of f0 are
   in the closed unit disk, so |f0| <= 2^d there, the roots of f0' are there too
   (Gauss-Lucas), and |f0(beta)| >= 3^d.
5. Induction principle carries an invariant and uses one fixed measure.

Not done here: the map layer (polynomials and Moebius maps on P^1 with critical-value
tracking, point at infinity kept in S, pole of each Moebius map added back) and the
final assembly against `PaperScopeLemma24Actual.PaperScopeLemma24Statement`, whose
definition was not read.

Existing assets to reuse (names from the hand-off notes, signatures not checked):
`valueDegreeDrop_proved`, `fieldDegreeDrop_proved`, `s3135_criticalPoint_degree_drop`,
CV composition law, `Mzk1MoebiusP1QbarActual`.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ProblemCNestedInductionSkeleton

open Polynomial
open Classical

abbrev Qbar : Type := AlgebraicClosure ℚ

/-! ## 1. Measure -/

/-- Degree over Q of an algebraic number. -/
def degQ (α : Qbar) : ℕ := (minpoly ℚ α).natDegree

/-- Largest degree of a point of S. -/
def maxDeg (S : Finset Qbar) : ℕ := S.sup degQ

/-- Number of points of S of largest degree. -/
def numMax (S : Finset Qbar) : ℕ := (S.filter (fun α => degQ α = maxDeg S)).card

/-! ## 2. Degree facts -/

/-- A Q-polynomial value has no larger degree: Q(f(alpha)) is inside Q(alpha). -/
theorem degQ_aeval_le (f : ℚ[X]) (α : Qbar) : degQ (aeval α f) ≤ degQ α := by
  sorry

/-- Critical values of f0 = minpoly alpha0 have degree < deg alpha0.
Proof: existing `valueDegreeDrop_proved`. -/
theorem degQ_critValue_lt (α0 ξ : Qbar)
    (hξ : aeval ξ (derivative (minpoly ℚ α0)) = 0) :
    degQ (aeval ξ (minpoly ℚ α0)) < degQ α0 := by
  sorry

/-- A rational Moebius map preserves the degree: Q(N(alpha)) = Q(alpha). -/
theorem degQ_moebius (a b c d : ℚ) (hdet : a * d - b * c ≠ 0) (α : Qbar)
    (hden : (c : Qbar) * α + (d : Qbar) ≠ 0) :
    degQ (((a : Qbar) * α + (b : Qbar)) / ((c : Qbar) * α + (d : Qbar))) = degQ α := by
  sorry

/-! ## 3. One step of the induction -/

/-- Conjugates of alpha0: the roots of f0. -/
def conjSet (α0 : Qbar) : Finset Qbar := ((minpoly ℚ α0).aroots Qbar).toFinset

/-- Critical points of f0. -/
def critSet (α0 : Qbar) : Finset Qbar :=
  ((derivative (minpoly ℚ α0)).aroots Qbar).toFinset

/-- S' = f0(S union conjugates) union f0(critical points). -/
def stepSet (S : Finset Qbar) (α0 : Qbar) : Finset Qbar :=
  ((S ∪ conjSet α0).image (fun α => aeval α (minpoly ℚ α0))) ∪
    (critSet α0).image (fun ξ => aeval ξ (minpoly ℚ α0))

/-- The largest degree does not grow.  Proof: `degQ_aeval_le`, `degQ_critValue_lt`,
and conjugates have the degree of alpha0. -/
theorem maxDeg_stepSet_le (S : Finset Qbar) (α0 : Qbar) (hα0 : α0 ∈ S)
    (hmax : degQ α0 = maxDeg S) : maxDeg (stepSet S α0) ≤ maxDeg S := by
  sorry

/-- If the largest degree stays, the number of points attaining it drops.
Proof: a point of degree D in S' is f0(alpha) with alpha in S of degree D and not a
root of f0 (roots go to 0, of degree 1 < D; critical values have degree < D); alpha0
itself is a root, so at most numMax S - 1 sources remain; `Finset.card_image_le`. -/
theorem numMax_stepSet_lt (S : Finset Qbar) (α0 : Qbar) (hα0 : α0 ∈ S)
    (hmax : degQ α0 = maxDeg S) (h2 : 2 ≤ degQ α0)
    (hsame : maxDeg (stepSet S α0) = maxDeg S) :
    numMax (stepSet S α0) < numMax S := by
  sorry

/-- Lexicographic decrease of (maxDeg, numMax). -/
theorem measure_stepSet_lt (S : Finset Qbar) (α0 : Qbar) (hα0 : α0 ∈ S)
    (hmax : degQ α0 = maxDeg S) (h2 : 2 ≤ degQ α0) :
    Prod.Lex (· < ·) (· < ·)
      (maxDeg (stepSet S α0), numMax (stepSet S α0)) (maxDeg S, numMax S) := by
  sorry

/-! ## 4. Avoidance over C with the universal constant 4 -/

/-- Monic with all roots in the closed unit disk: |f| <= 2^d on the disk.
Proof: product form over the roots; each factor has norm <= 2. -/
theorem norm_eval_le_two_pow (f : ℂ[X]) (hf : f.Monic)
    (hroots : ∀ a ∈ f.roots, ‖a‖ ≤ 1) {x : ℂ} (hx : ‖x‖ ≤ 1) :
    ‖f.eval x‖ ≤ 2 ^ f.natDegree := by
  sorry

/-- Same hypothesis: |f(beta)| >= 3^d for |beta| >= 4. -/
theorem three_pow_le_norm_eval (f : ℂ[X]) (hf : f.Monic)
    (hroots : ∀ a ∈ f.roots, ‖a‖ ≤ 1) {β : ℂ} (hβ : 4 ≤ ‖β‖) :
    (3 : ℝ) ^ f.natDegree ≤ ‖f.eval β‖ := by
  sorry

/-- Gauss-Lucas: the critical points are in the same disk. -/
theorem derivative_roots_in_disk (f : ℂ[X]) (hroots : ∀ a ∈ f.roots, ‖a‖ ≤ 1) :
    ∀ ξ ∈ f.derivative.roots, ‖ξ‖ ≤ 1 := by
  sorry

/-- Avoidance: f(beta) differs from every value of f on the closed unit disk, hence from
f(S) and from all critical values. -/
theorem eval_ne_of_disk (f : ℂ[X]) (hf : f.Monic) (hdeg : 1 ≤ f.natDegree)
    (hroots : ∀ a ∈ f.roots, ‖a‖ ≤ 1) {β γ : ℂ} (hβ : 4 ≤ ‖β‖) (hγ : ‖γ‖ ≤ 1) :
    f.eval β ≠ f.eval γ := by
  sorry

/-! ## 5. Induction principle with an invariant and a fixed measure -/

/-- Well-founded induction on a lexicographic N x N measure, restricted to admissible
states.  `base` is asked only where the first component is at most 1 (all points
rational); `step` only on admissible states and must return an admissible state. -/
theorem induction_with_invariant {σ : Type*} (μ : σ → ℕ × ℕ) (Inv Goal : σ → Prop)
    (base : ∀ s, Inv s → (μ s).1 ≤ 1 → Goal s)
    (step : ∀ s, Inv s → 1 < (μ s).1 →
      ∃ s', Inv s' ∧ Prod.Lex (· < ·) (· < ·) (μ s') (μ s) ∧ (Goal s' → Goal s)) :
    ∀ s, Inv s → Goal s := by
  sorry

end LeanFormal.IUT.XiFPaper.ProblemCNestedInductionSkeleton
end
