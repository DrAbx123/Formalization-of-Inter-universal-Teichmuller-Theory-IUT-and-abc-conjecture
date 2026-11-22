/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A785 hull: paper-normalized `diff_v` — sign analysis

ROUTES §6.1 paper normalization (odd p, n = [K_v:Q_p], e ramification index,
r/n torsion correction):

  `log μ(I_v) = (1 + [p=2] − 1/e − r/n) · log p`.

The residue-cardinality formula for `logShellIntegerIndex` gives
`log index_v = f_v · exponent_v · log p` (`IndexResidueFormula`; f residue degree).
Define

  `diffV = log μ(I_v) − (1/(2l))·log index_v`  (paper-normalized difference).

Findings:
1. `diffV = ((1+[p=2]−1/e−r/n) − f·exponent/(2l))·log p`.
2. For the model Q_p(zeta_p) (p odd, e=p-1, r=1, n=p-1, f=1, exponent=1)
   `log μ = ((p−3)/(p−1))·log p`, so `diffV = ((p−3)/(p−1) − 1/(2l))·log p`;
   this is positive for p large and l large, but can be negative for small p/l:
   `diff_v >= 0` is NOT a universal consequence of the formulas.
3. Correct replacement condition: `diffV >= 0 ↔ log index_v <= (2l)·log μ(I_v)`;
   i.e. the paper bound is `Dbar <= (2l)·(log μ(I_v))` at each place, not an
   unconditional nonnegativity of the different/unit correction.  The green
   A/B exponents (`logShellPaperAExponent`, `logShellPaperBExponent`,
   `logShellPaperExponent_sum_mul_log_le_three_add_log`) bound the residue
   exponent from above; combined with the paper μ formula they give the
   correct one-sided condition, not `diff_v >= 0` in general. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1DiffNonnegActual

/-- Paper-normalized log shell volume (ROUTES §6.1). -/
def paperShellLogMu (p e r n : ℝ) : ℝ :=
  (1 + (if p = 2 then 1 else 0 : ℝ) - 1 / e - r / n) * Real.log p

/-- Residue-cardinality log of `logShellIntegerIndex`: `f · exponent · log p`. -/
def logShellIndex (f exponent logp : ℝ) : ℝ := f * exponent * logp

/-- Paper-normalized `diff_v`: shell volume minus the `1/(2l)` index term. -/
def diffV (p e r n f exponent logp l : ℝ) : ℝ :=
  paperShellLogMu p e r n - (1 / (2 * l)) * logShellIndex f exponent logp

theorem diffV_formula (p e r n f exponent logp l : ℝ) :
    diffV p e r n f exponent logp l =
      (1 + (if p = 2 then 1 else 0 : ℝ) - 1 / e - r / n) * Real.log p -
        (1 / (2 * l)) * (f * exponent * logp) := rfl

/-- `diff_v >= 0` is exactly the one-sided index bound. -/
theorem diffV_nonneg_iff_index_bound
    (p e r n f exponent logp l : ℝ) (hl : 0 < l) :
    0 ≤ diffV p e r n f exponent logp l ↔
      (1 / (2 * l)) * logShellIndex f exponent logp ≤ paperShellLogMu p e r n := by
  unfold diffV
  constructor <;> intro h <;> linarith

/-- **Negative instance**: for the `Q_p(zeta_p)` model with `p = 5`, `l = 1/2`
(abstract parameter choice), `diff_v = (1/2 − 1)·log 5 < 0`; hence `diff_v >= 0`
is not a universal consequence of the paper formulas. -/
theorem diffV_negative_instance :
    diffV 5 4 1 4 1 1 (Real.log 5) (1 / 2) = -(1 / 2) * Real.log 5 := by
  unfold diffV paperShellLogMu logShellIndex
  norm_num
  ring

theorem diffV_negative_instance_neg :
    diffV 5 4 1 4 1 1 (Real.log 5) (1 / 2) < 0 := by
  rw [diffV_negative_instance]
  have h : 0 < Real.log 5 := Real.log_pos (by norm_num)
  nlinarith

/-- Correct paper condition: the per-place required lower bound on the index log
(`Dbar_v >= ...`) rather than `diff_v >= 0`. -/
def paperIndexBound (p e r n l : ℝ) : ℝ :=
  (2 * l) * paperShellLogMu p e r n

theorem diffV_nonneg_iff_Dbar
    (p e r n f exponent logp l : ℝ) (hl : 0 < l) :
    0 ≤ diffV p e r n f exponent logp l ↔
      logShellIndex f exponent logp ≤ paperIndexBound p e r n l := by
  rw [diffV_nonneg_iff_index_bound p e r n f exponent logp l hl]
  unfold paperIndexBound
  constructor <;> intro h <;>
    field_simp [ne_of_gt hl] at h ⊢ <;> linarith

def diffRows : List (String × String × String) :=
  [ ("paper log mu", "log mu(I_v) = (1+[p=2]-1/e-r/n)*log p", "DEF (paperShellLogMu)"),
    ("log index", "log index_v = f_v*exponent_v*log p (residue-card exponent)", "DEF (logShellIndex; IndexResidueFormula)"),
    ("diff_v", "diff_v = log mu - (1/(2l)) log index", "DEF"),
    ("general identity", "diff_v >= 0 iff (1/(2l)) log index <= log mu", "PROVED (diffV_nonneg_iff_index_bound)"),
        ("negative instance", "p=5, l=1/2 model: diff_v = -(1/2)log 5 < 0 ⇒ diff_v>=0 not universal", "PROVED (diffV_negative_instance_neg)"),
    ("correct replacement", "per-place condition: log index_v <= 2l*log mu(I_v)", "PROVED equivalence (diffV_nonneg_iff_Dbar)"),
    ("A/B bounds", "green logShellPaperAExponent/BExponent bound index from above; used to prove the one-sided condition, not diff>=0", "GREEN (cited; not re-exported here)") ]

theorem diffRows_length : diffRows.length = 7 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1DiffNonnegActual.diffV_nonneg_iff_index_bound
#print axioms LeanFormal.IUT.XiFPaper.Mzk1DiffNonnegActual.diffV_negative_instance_neg
#print axioms LeanFormal.IUT.XiFPaper.Mzk1DiffNonnegActual.diffV_nonneg_iff_Dbar

end LeanFormal.IUT.XiFPaper.Mzk1DiffNonnegActual

end