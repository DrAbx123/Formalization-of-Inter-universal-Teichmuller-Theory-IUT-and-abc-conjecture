import Mathlib

/-! # Problem B skeleton — [Mzk1] Lemma 2.3 as one explicit rational Moebius map

SKELETON ONLY.  Every proof is `sorry`.  NOT compiled.  Kept outside
`tmp/sheaf/xif/paper` on purpose.  Source: coord/OPEN-HARD-PROBLEMS.md, Problem B;
paper lines 136-143 and 181-186.

Map.  N(x) = C*eps / (lam - x), lam = beta + eps, with eps rational and
(C+1)*eps <= dist(beta, S).  Then
* N(beta) = C exactly,
* |N(alpha)| <= 1 for alpha in S,
* N(infinity) = 0, and the pole lam is not in S.
The only estimate is one reverse triangle inequality:
|lam - alpha| >= |alpha - beta| - eps >= C*eps.

This merges Lemma 2.3 with the "multiply by a positive rational" step of lines 184-186.
When beta is rational, all coefficients are rational.

Bridge to existing assets (not referenced here; names not checked): the matrix of N is
(0, C*eps; -1, lam), to be fed to `Mzk1MoebiusP1CActual.MoebiusData`; a Moebius map has
no critical point and preserves the degree over Q of every point.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ProblemBLemma23Skeleton

/-- A positive rational eps with (C+1)*eps below every distance from beta to S.
Proof: `Finset.induction` taking the min of two rationals, with `exists_rat_btwn` for one
point; no `Finset.min'` needed. -/
theorem exists_eps (S : Finset ℂ) (β : ℂ) (hβ : β ∉ S) (C : ℚ) (hC : 0 < C) :
    ∃ ε : ℚ, 0 < ε ∧ ∀ α ∈ S, (((C + 1) * ε : ℚ) : ℝ) ≤ ‖α - β‖ := by
  sorry

/-- Reverse triangle inequality at the pole lam = beta + eps. -/
theorem pole_dist (β α : ℂ) (C ε : ℚ) (hε : 0 < ε)
    (h : (((C + 1) * ε : ℚ) : ℝ) ≤ ‖α - β‖) :
    ((C * ε : ℚ) : ℝ) ≤ ‖(β + (ε : ℂ)) - α‖ := by
  sorry

/-- The normalising map on finite points: N(x) = C*eps / (beta + eps - x). -/
def normMoebius (C ε : ℚ) (β x : ℂ) : ℂ :=
  ((C * ε : ℚ) : ℂ) / ((β + (ε : ℂ)) - x)

/-- N(beta) = C exactly. -/
theorem normMoebius_beta (C ε : ℚ) (hε : ε ≠ 0) (β : ℂ) :
    normMoebius C ε β β = (C : ℂ) := by
  sorry

/-- |N(alpha)| <= 1.  Proof: `pole_dist` and `div_le_one`. -/
theorem norm_normMoebius_le_one (β α : ℂ) (C ε : ℚ) (hC : 0 < C) (hε : 0 < ε)
    (h : (((C + 1) * ε : ℚ) : ℝ) ≤ ‖α - β‖) :
    ‖normMoebius C ε β α‖ ≤ 1 := by
  sorry

/-- **Normalisation used in the 2.4 step**: Lemma 2.3 and the rational scaling in one
statement.  The pole is outside S, beta goes to C, S goes into the closed unit disk. -/
theorem lemma23_normalization (S : Finset ℂ) (β : ℂ) (hβ : β ∉ S) (C : ℚ) (hC : 0 < C) :
    ∃ ε : ℚ, 0 < ε ∧ (β + (ε : ℂ)) ∉ S ∧ normMoebius C ε β β = (C : ℂ) ∧
      ∀ α ∈ S, ‖normMoebius C ε β α‖ ≤ 1 := by
  sorry

/-- **The paper's literal Lemma 2.3** for f(x) = 1/(x - lam), with lam rational when beta
is.  Proof: lam = beta + eps from `exists_eps`; |alpha - lam| >= C * |beta - lam|. -/
theorem lemma23_paper (S : Finset ℂ) (β : ℚ) (hβ : (β : ℂ) ∉ S) (C : ℚ) (hC : 0 < C) :
    ∃ lam : ℚ, lam ≠ β ∧ (lam : ℂ) ∉ S ∧
      ∀ α ∈ S, (C : ℝ) * ‖(α - (lam : ℂ))⁻¹‖ ≤ ‖((β : ℂ) - (lam : ℂ))⁻¹‖ := by
  sorry

end LeanFormal.IUT.XiFPaper.ProblemBLemma23Skeleton
end
