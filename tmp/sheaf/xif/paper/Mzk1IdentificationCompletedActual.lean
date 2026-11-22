/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A832 hull: sSup radius step and different normalization

Part 1: the `sSup` step of `logShellRadius <= paperB + correction` is abstract
order theory: a pointwise bound on `-ordp y` for `y` in the log-shell gives
the same bound on `sSup`.  The remaining input is the pointwise bound, which
comes from the green containment `log(O^×) ⊆ β·R`, `||β|| = p^paperB` and the
`(2p)^-1` scaling correction `1 + [p=2]`.

Part 2: the integer different lower bound `v_K(d) >= e-1` (from
`different ⊇ (π^(e-1))`) is NOT in the repo; it is left as an explicit input.
With paper normalization `d = v/n` and `n = e*f`, `d >= (e-1)/(e*f)`, which is
WEAKER than `1 - 1/e = (e-1)/e` by the factor `f`; equality holds iff `f = 1`.
This factor is the exact normalization discrepancy for fact 2. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1IdentificationCompletedActual

/-- `sSup` step: pointwise `f y <= B` on `S` bounds `sSup (f '' S)`. -/
theorem sSup_image_le_of_pointwise {α : Type*} (S : Set α) (f : α → ℝ) (B : ℝ)
    (h : ∀ y ∈ S, f y ≤ B) (hbdd : BddAbove (f '' S)) (hS : S.Nonempty) :
    sSup (f '' S) ≤ B := by
  rw [csSup_le_iff hbdd (hS.image f)]
  rintro _ ⟨y, hy, rfl⟩
  exact h y hy

/-- `logShellRadius` = `sSup (−ordp '' logShell)`; the radius bound follows
from the pointwise bound. -/
def logShellRadiusFrom (ordp : α → ℝ) (logShell : Set α) : ℝ := sSup ((fun y => -ordp y) '' logShell)

theorem logShellRadius_le_of_pointwise {α : Type*} (ordp : α → ℝ) (logShell : Set α)
    (B : ℝ) (h : ∀ y ∈ logShell, -ordp y ≤ B)
    (hbdd : BddAbove ((fun y => -ordp y) '' logShell)) (hS : logShell.Nonempty) :
    logShellRadiusFrom ordp logShell ≤ B := by
  unfold logShellRadiusFrom
  exact sSup_image_le_of_pointwise logShell (fun y => -ordp y) B h hbdd hS

/-- Different integer lower bound input: `v >= e - 1`.  This is the standard
`different ⊇ (π^(e-1))` fact; it is an explicit input here (not in repo). -/
def DifferentIntegerLower (v e : ℝ) : Prop := e - 1 ≤ v

theorem different_paperOrder_fraction (v e n : ℝ) (he : 0 < e) (hn : n = e)
    (h : DifferentIntegerLower v e) : v / n ≥ (e - 1) / e := by
  unfold DifferentIntegerLower at h
  rw [hn]
  field_simp [ne_of_gt he]
  linarith

/-- General normalization `n = e*f`: the lower bound is `(e-1)/(e*f)`. -/
theorem different_paperOrder_fraction_general (v e f : ℝ) (he : 0 < e) (hf : 1 ≤ f)
    (h : e - 1 ≤ v) :
    (e - 1) / (e * f) ≤ v / (e * f) := by
  apply div_le_div_of_nonneg_right h (by positivity)

/-- Comparison with paper `1 - 1/e`: `(e-1)/(e*f) <= (e-1)/e`, with exact gap
`(e-1)(f-1)/(e*f)`.  So fact 2 with paper normalization `1-1/e` requires
`f = 1` (or a different paper different normalization). -/
theorem different_normalization_gap (e f : ℝ) (he1 : 1 ≤ e) (hf : 1 ≤ f) :
    (e - 1) / e - (e - 1) / (e * f) = (e - 1) * (f - 1) / (e * f) := by
  have he : 0 < e := lt_of_lt_of_le zero_lt_one he1
  field_simp [ne_of_gt he, ne_of_gt (mul_pos he (lt_of_lt_of_le zero_lt_one hf))]

theorem different_fraction_le_one_sub_inv (e f : ℝ) (he1 : 1 ≤ e) (hf : 1 ≤ f) :
    (e - 1) / (e * f) ≤ 1 - 1 / e := by
  have he : 0 < e := lt_of_lt_of_le zero_lt_one he1
  have hgap := different_normalization_gap e f he1 hf
  have hnonneg : 0 ≤ (e - 1) * (f - 1) / (e * f) := by positivity
  have heq : 1 - 1 / e = (e - 1) / e := by field_simp [ne_of_gt he]
  rw [heq]
  linarith [hgap, hnonneg]

def identRows : List (String × String × String) :=
  [ ("sSup step", "pointwise -ordp y <= B => sSup <= B", "PROVED (sSup_image_le_of_pointwise / logShellRadius_le_of_pointwise)"),
    ("radius pointwise input", "-ordp y <= paperB + (1+[p=2]) from green containment/norm", "INPUT (green cited: unitLogLattice_subset_..., norm_logShellPaperBetaElement)"),
    ("different integer lower", "v >= e-1 from different ⊇ (pi^(e-1))", "INPUT (not in repo)"),
    ("different n=e normalization", "v/e >= (e-1)/e = 1-1/e", "PROVED (different_paperOrder_fraction)"),
    ("general n=e*f", "v/(e f) >= (e-1)/(e f)", "PROVED (different_paperOrder_fraction_general)"),
    ("normalization gap", "(e-1)/e - (e-1)/(e f) = (e-1)(f-1)/(e f) >=0", "PROVED (different_normalization_gap)"),
    ("fact 2 condition", "paper 1-1/e needs f=1; otherwise the lower bound is weaker by factor f", "NORMALIZATION DIFFERENCE") ]

theorem identRows_length : identRows.length = 7 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1IdentificationCompletedActual.sSup_image_le_of_pointwise
#print axioms LeanFormal.IUT.XiFPaper.Mzk1IdentificationCompletedActual.logShellRadius_le_of_pointwise
#print axioms LeanFormal.IUT.XiFPaper.Mzk1IdentificationCompletedActual.different_normalization_gap

end LeanFormal.IUT.XiFPaper.Mzk1IdentificationCompletedActual

end