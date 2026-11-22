import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

/-! # Mzk1Lemma23Actual — [Mzk1] Lemma 2.3 (separation of collections of points, finite complex case)

STEP 0 prior-art: corpus papers/motizuki_corpus/text/Noncritical Belyi Maps.txt
Lemma 2.3 lines 136-142; no LeanFormal complex/Belyi infrastructure; Mathlib
Complex norm and Finset inf available.

PAPER: finite S subset P^1(C), C>0, beta in C minus S: exists lambda in C with
f(x)=1/(x-lambda) satisfying f(beta) != 0,inf; f(alpha) != inf;
|f(beta)| >= C*|f(alpha)| for all alpha in S.  (Rational lambda when beta rational
is a separate refinement, see reduction plan.)

CHOICE: lambda = beta + eps with eps = d/(2*(C+1)), d = min_{alpha in S} |alpha-beta|.

LABEL: proven class-A fragment (finite complex case). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma23Actual

/-- The minimal distance from beta to the finite set S (1 if S is empty). -/
noncomputable def minDist (S : Finset ℂ) (β : ℂ) : ℝ :=
  if h : S.Nonempty then S.inf' h (fun α => dist α β) else 1

/-- The explicit epsilon for lambda = beta + epsilon. -/
noncomputable def eps (S : Finset ℂ) (β : ℂ) (C : ℝ) : ℝ :=
  minDist S β / (2 * (C + 1))

/-- The explicit lambda: beta + eps. -/
noncomputable def lam (S : Finset ℂ) (β : ℂ) (C : ℝ) : ℂ :=
  β + (eps S β C : ℂ)

/-- With beta outside S the minimal distance is positive. -/
theorem minDist_pos (S : Finset ℂ) (β : ℂ) (hβ : β ∉ S) : 0 < minDist S β := by
  classical
  unfold minDist
  split_ifs with hS
  · have : 0 < S.inf' hS (fun α => dist α β) := by
      rw [Finset.lt_inf'_iff]
      intro α hα
      exact dist_pos.mpr (by intro h; exact hβ (h ▸ hα))
    exact this
  · norm_num

/-- eps is positive when C > 0. -/
theorem eps_pos (S : Finset ℂ) (β : ℂ) (C : ℝ) (hβ : β ∉ S) (hC : 0 < C) :
    0 < eps S β C := by
  unfold eps
  exact div_pos (minDist_pos S β hβ) (by nlinarith)

/-- Key inequality: C * eps <= dist alpha lambda for every alpha in S. -/
theorem dist_alpha_lam_ge (S : Finset ℂ) (β : ℂ) (C : ℝ) (hβ : β ∉ S) (hC : 0 < C)
    {α : ℂ} (hα : α ∈ S) :
    C * eps S β C ≤ dist α (lam S β C) := by
  classical
  have hpos : 0 < eps S β C := eps_pos S β C hβ hC
  have hd : minDist S β ≤ dist α β := by
    unfold minDist
    rw [dif_pos ⟨α, hα⟩]
    exact Finset.inf'_le _ hα
  have htri : dist α β ≤ dist α (lam S β C) + dist (lam S β C) β := dist_triangle _ _ _
  have hdist : dist (lam S β C) β = eps S β C := by
    unfold lam
    rw [dist_eq_norm]
    have : β + (eps S β C : ℂ) - β = (eps S β C : ℂ) := by ring
    rw [this]
    norm_cast
    exact abs_of_nonneg hpos.le
  have hmain : dist α (lam S β C) ≥ minDist S β - eps S β C := by
    linarith [htri, hdist, hd, dist_comm (lam S β C) β]
  have hfrac : C * eps S β C ≤ minDist S β - eps S β C := by
    unfold eps
    have hC1 : 0 < C + 1 := by nlinarith
    have hdpos : 0 < minDist S β := minDist_pos S β hβ
    rw [div_eq_mul_inv, mul_inv]
    field_simp [hC1.ne']
    nlinarith
  linarith

#check minDist_pos
#check eps_pos
#check dist_alpha_lam_ge

end LeanFormal.IUT.XiFPaper.Mzk1Lemma23Actual
end