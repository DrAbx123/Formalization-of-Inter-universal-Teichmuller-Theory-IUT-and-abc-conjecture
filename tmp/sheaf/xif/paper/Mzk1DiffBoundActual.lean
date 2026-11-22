/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A783 hull: paper-normalized `diff_v` and its lower bound

Paper normalization at a bad finite place (cf. IUT IV, Prop. 1.3 / 1.4):

  `diff_v = log N(diff_v) − torsion_v + arch_v`,

where `log N(diff_v) = −d_v · log p` (`d_v = localDifferentPaperOrder`, green
`norm_differentGenerator_eq_prime_rpow_neg_paperOrder` /
`localNormOrder_differentGenerator_eq_paperOrder`), `torsion_v` is the
`r/n` torsion-unit correction, and `arch_v = log(sqrt 2 * pi)` is the
archimedean contribution.  Green different bounds:
`localDifferentPaperOrder_le_degree_padicVal` and the A/B exponents of
`IntegralLogShellSharpBounds`.  The exact instantiated lower bound is the
remaining analytic input; the arithmetic implication to
`Lbar + Dbar − A >= 0` is proved below. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1DiffBoundActual

/-- Abstract paper-normalized `diff_v`: different log minus torsion plus arch. -/
def diffV (logNormDiff torsion arch : ℝ) : ℝ := logNormDiff - torsion + arch

/-- Concrete finite-place form: `−order · log p − torsion + arch`. -/
def diffVPaper (order logp torsion arch : ℝ) : ℝ :=
  -(order * logp) - torsion + arch

theorem diffVPaper_eq (order logp torsion arch : ℝ) :
    diffVPaper order logp torsion arch = -order * logp - torsion + arch := by
  unfold diffVPaper
  ring

/-- A lower bound for `diff_v` transfers to the paper different log. -/
theorem diffV_ge_of_order_bound {order logp torsion arch lb : ℝ}
    (h : lb ≤ -order * logp - torsion + arch) :
    lb ≤ diffVPaper order logp torsion arch := by
  unfold diffVPaper
  linarith

/-- **Final arithmetic step**: if `diff_v >= lb` and `0 <= Lbar + lb - A`, then
`0 <= Lbar + Dbar - A`. -/
theorem LbarDbarA_nonneg_of_diffBound
    (Lbar Dbar A lb : ℝ) (hD : lb ≤ Dbar)
    (h : 0 ≤ Lbar + lb - A) :
    0 ≤ Lbar + Dbar - A := by
  linarith

/-- Same with the explicit `diffVPaper` lower bound. -/
theorem LbarDbarA_nonneg_of_diffVPaper_bound
    (Lbar Dbar A order logp torsion arch lb : ℝ)
    (hD : lb ≤ Dbar)
    (hlb : lb ≤ diffVPaper order logp torsion arch)
    (h : 0 ≤ Lbar + lb - A) :
    0 ≤ Lbar + Dbar - A := by
  linarith

def diffRows : List (String × String × String) :=
  [ ("diff_v definition", "diff_v = log N(diff_v) - torsion_v + arch_v", "DEF (diffV / diffVPaper)"),
    ("different log", "log N(diff_v) = -localDifferentPaperOrder * log p", "GREEN (LocalDifferentNormOrder; docstring)"),
    ("torsion term", "torsion_v = r/n (unit-torsion correction)", "PAPER TERM (explicit parameter)"),
    ("arch term", "arch_v = log(sqrt 2 * pi)", "PAPER TERM (explicit parameter)"),
    ("different upper bound", "d_v <= d_T + padicVal + 1/e (localDifferentPaperOrder_le_degree_padicVal)", "GREEN"),
    ("A/B exponents", "logShellPaperAExponent / BExponent bounds (IntegralLogShellSharpBounds)", "GREEN"),
    ("Lbar + Dbar - A >= 0", "follows from diff_v lower bound lb and 0 <= Lbar + lb - A", "PROVED conditional (LbarDbarA_nonneg_of_diffBound)"),
    ("remaining gap", "instantiate lb from the green different/A-B bounds with the actual torsion/arch terms", "EXPLICIT PARAMETER") ]

theorem diffRows_length : diffRows.length = 8 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1DiffBoundActual.diffVPaper_eq
#print axioms LeanFormal.IUT.XiFPaper.Mzk1DiffBoundActual.LbarDbarA_nonneg_of_diffBound
#print axioms LeanFormal.IUT.XiFPaper.Mzk1DiffBoundActual.LbarDbarA_nonneg_of_diffVPaper_bound

end LeanFormal.IUT.XiFPaper.Mzk1DiffBoundActual

end