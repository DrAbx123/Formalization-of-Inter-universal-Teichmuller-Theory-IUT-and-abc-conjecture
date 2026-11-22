/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A866 hull: D_exact lower bound for L7

L7 shape: (1 - 1/l)*log p <= D_exact, where D_exact is the paper-normalized
weighted hull datum (sum weights.h.log p plus an arch addend).  From the tame
hull packet each place contributes (1 - 1/e)*log p with e >= l, and weights
>= 1; hence each term is at least (1 - 1/l)*log p.  Summing and adding a
nonnegative arch term gives the L7 lower bound. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1DExactFromHullActual

open scoped BigOperators

/-- D_exact without arch. -/
def DExact {ι : Type*} [Fintype ι] (w h logp : ι → ℝ) : ℝ :=
  ∑ v, w v * h v * logp v

/-- D_exact with a nonnegative arch addend. -/
def DExactWithArch {ι : Type*} [Fintype ι] (w h logp : ι → ℝ) (arch : ℝ) : ℝ :=
  DExact w h logp + arch

/-- Single term lower bound: weights >= 1, heights >= c, log p >= 0. -/
theorem term_ge (w h logp c : ℝ) (hw : 1 ≤ w) (hh : c ≤ h) (hc0 : 0 ≤ c)
    (hl : 0 ≤ logp) :
    c * logp ≤ w * h * logp := by
  have hh0 : 0 ≤ h := le_trans hc0 hh
  have hwh : h ≤ w * h := by
    have := mul_le_mul_of_nonneg_right hw hh0
    simpa using this
  have hcoef : c ≤ w * h := le_trans hh hwh
  exact mul_le_mul_of_nonneg_right hcoef hl

/-- Tame height 1 - 1/e is at least 1 - 1/l when l <= e (positive). -/
theorem tame_height_ge (l e : ℝ) (hl : 0 < l) (hle : l ≤ e) :
    1 - 1 / l ≤ 1 - 1 / e := by
  have he : 0 < e := lt_of_lt_of_le hl hle
  have h : 1 / e ≤ 1 / l := one_div_le_one_div_of_le hl hle
  linarith

/-- L7 per-place form: tame height with e >= l, weight >= 1. -/
theorem L7_term (w logp l e : ℝ) (hw : 1 ≤ w) (hl : 1 ≤ l) (hle : l ≤ e)
    (hlogp : 0 ≤ logp) :
    (1 - 1 / l) * logp ≤ w * (1 - 1 / e) * logp := by
  have hlpos : 0 < l := lt_of_lt_of_le zero_lt_one hl
  have hc0 : 0 ≤ 1 - 1 / l := by
    have h : 1 / l ≤ 1 := by rw [div_le_one hlpos]; exact hl
    linarith
  exact term_ge w (1 - 1 / e) logp (1 - 1 / l) hw
    (tame_height_ge l e hlpos hle) hc0 hlogp

/-- L7 global form: summing per-place bounds bounds D_exact from below. -/
theorem L7_global {ι : Type*} [Fintype ι] (w h logp : ι → ℝ) (l : ℝ)
    (hl : 0 < l)
    (hterm : ∀ v, (1 - 1 / l) * logp v ≤ w v * h v * logp v) :
    (∑ v, (1 - 1 / l) * logp v) ≤ DExact w h logp := by
  unfold DExact
  exact Finset.sum_le_sum fun v _ => hterm v

/-- L7 with arch: a nonnegative arch addend does not hurt. -/
theorem L7_with_arch {ι : Type*} [Fintype ι] (w h logp : ι → ℝ) (l arch : ℝ)
    (hl : 0 < l) (harch : 0 ≤ arch)
    (hterm : ∀ v, (1 - 1 / l) * logp v ≤ w v * h v * logp v) :
    (∑ v, (1 - 1 / l) * logp v) ≤ DExactWithArch w h logp arch := by
  unfold DExactWithArch
  have h := L7_global w h logp l hl hterm
  linarith

def l7Rows : List (String × String × String) :=
  [ ("D_exact", "Σ weights.h.log p", "DEF (DExact)"),
    ("D_exact+arch", "D_exact + arch", "DEF (DExactWithArch)"),
    ("per-term", "w>=1, h>=c, logp>=0 => c logp <= w h logp", "PROVED (term_ge)"),
    ("tame height", "l<=e => 1-1/l <= 1-1/e", "PROVED (tame_height_ge)"),
    ("L7 per-place", "tame e>=l, w>=1 => (1-1/l)logp <= w(1-1/e)logp", "PROVED (L7_term)"),
    ("L7 global", "sum of per-place bounds <= D_exact", "PROVED (L7_global)"),
    ("L7 arch", "arch>=0 => same lower bound for D_exact+arch", "PROVED (L7_with_arch)"),
    ("remaining", "identify D_exact with actual hull/procession data", "GAP (L5 object identification)") ]

theorem l7Rows_length : l7Rows.length = 8 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1DExactFromHullActual.L7_term
#print axioms LeanFormal.IUT.XiFPaper.Mzk1DExactFromHullActual.L7_global
#print axioms LeanFormal.IUT.XiFPaper.Mzk1DExactFromHullActual.L7_with_arch

end LeanFormal.IUT.XiFPaper.Mzk1DExactFromHullActual

end