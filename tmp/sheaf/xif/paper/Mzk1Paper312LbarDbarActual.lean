/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A792 hull: merge framework `paper312_of_Lbar_Dbar_bound`

This file contains the *framework only*: it assumes the per-place
inequality

  `qcoef_i <= logIdx_i + diff_i`   (A790 reduction; abc's arithmetic),

sums it over the bad places to

  `A <= Lbar + Dbar`   (`A = sum qcoef_i`, `Lbar = sum logIdx_i`,
                         `Dbar = sum diff_i`),

and concludes the paper 3.12 comparison

  `qReading <= thetaLog`   with `qReading = -A` and `thetaLog = Lbar + Dbar`.

The paper dictionary `thetaLog = Lbar + Dbar` (scaled hull log-volume = index
log plus paper different correction) is the remaining identification; the
per-place arithmetic is abc's `Mzk1PerPlaceInequalityActual`. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1Paper312LbarDbarActual

/-- Per-place inequality over an arbitrary finite bad-place index. -/
def PerPlaceInequality {ι : Type*} (qcoef logIdx diff : ι → ℝ) : Prop :=
  ∀ i, qcoef i ≤ logIdx i + diff i

/-- Summing the per-place inequality gives the global `A <= Lbar + Dbar`. -/
theorem perPlace_to_LbarDbar {ι : Type*} [Fintype ι]
    (qcoef logIdx diff : ι → ℝ)
    (h : PerPlaceInequality qcoef logIdx diff) :
    (∑ i, qcoef i) ≤ (∑ i, logIdx i) + (∑ i, diff i) := by
  calc
    (∑ i, qcoef i) ≤ ∑ i, (logIdx i + diff i) := Finset.sum_le_sum fun i _ => h i
    _ = (∑ i, logIdx i) + (∑ i, diff i) := Finset.sum_add_distrib

/-- **Paper 3.12 from the global bound**: if `qReading = -A`, the scaled θ-hull
log-volume is `thetaLog = Lbar + Dbar`, and `A <= Lbar + Dbar`, then the
paper comparison `qReading <= thetaLog` holds. -/
theorem paper312_of_Lbar_Dbar_bound
    (A Lbar Dbar qReading thetaLog : ℝ)
    (hq : qReading = -A)
    (hθ : thetaLog = Lbar + Dbar)
    (hA : 0 ≤ A)
    (hglobal : A ≤ Lbar + Dbar) :
    qReading ≤ thetaLog := by
  rw [hq, hθ]
  linarith

/-- Combined: per-place inequalities and the paper dictionary imply the paper
comparison. -/
theorem paper312_of_perPlace_and_dictionary
    {ι : Type*} [Fintype ι] (qcoef logIdx diff : ι → ℝ)
    (qReading thetaLog : ℝ)
    (hper : PerPlaceInequality qcoef logIdx diff)
    (hq : qReading = -(∑ i, qcoef i))
    (hθ : thetaLog = (∑ i, logIdx i) + (∑ i, diff i))
    (hA : 0 ≤ ∑ i, qcoef i) :
    qReading ≤ thetaLog := by
  have hglobal := perPlace_to_LbarDbar qcoef logIdx diff hper
  rw [hq, hθ]
  linarith

def mergeRows : List (String × String × String) :=
  [ ("per-place", "qcoef_i <= logIdx_i + diff_i (A790 reduction)", "FRAMEWORK (abc arithmetic pending)"),
    ("summation", "sum per-place => A <= Lbar + Dbar", "PROVED (perPlace_to_LbarDbar)"),
    ("paper comparison", "qReading = -A, thetaLog = Lbar+Dbar, A<=Lbar+Dbar => qReading<=thetaLog", "PROVED (paper312_of_Lbar_Dbar_bound)"),
    ("combined", "per-place + paper dictionary => paper comparison", "PROVED (paper312_of_perPlace_and_dictionary)"),
    ("remaining dictionary", "thetaLog = Lbar + Dbar (scaled hull log = index log + diff)", "IDENTIFICATION GAP"),
    ("remaining arithmetic", "per-place qcoef=(f/[F:Q])logp/(2l) <= logIdx+diff with A/B bounds", "abc Mzk1PerPlaceInequalityActual") ]

theorem mergeRows_length : mergeRows.length = 6 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1Paper312LbarDbarActual.perPlace_to_LbarDbar
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Paper312LbarDbarActual.paper312_of_Lbar_Dbar_bound
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Paper312LbarDbarActual.paper312_of_perPlace_and_dictionary

end LeanFormal.IUT.XiFPaper.Mzk1Paper312LbarDbarActual

end