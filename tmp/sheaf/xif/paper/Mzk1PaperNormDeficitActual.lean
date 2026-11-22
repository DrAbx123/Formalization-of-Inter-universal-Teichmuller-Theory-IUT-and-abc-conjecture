/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1PaperNormMuActual
import tmp.sheaf.xif.paper.Mzk1PaperNormThetaActual
import Mathlib.Tactic

/-! # A796/A797: paper-normalized deficit — explicit form, bounds, and positive part -/

/- Consumes hull's `Mzk1PaperNormMuActual` framework:
* `logMuPaper p e r n = (1 + [p=2] - 1/e - r/n) * log p`;
* `PaperNormVerdict ssCoeff A sumLogMu sumTheta := ssCoeff*A <= sumLogMu + sumTheta`;
* `paperNormDeficit ... := ssCoeff*A - (sumLogMu + sumTheta)`;
* `paperNormVerdict_iff_deficit_nonpos` (hull, green).

This file:
1. re-expands the deficit and its affine structure;
2. proves the SUM form of the paper-normalized lower bounds (Finset version of
   `logMuPaper_ge_odd` / `logMuPaper_ge_two`);
3. proves the deficit is NOT unconditionally nonpositive: the exact positive instance
   `e = 1, r/n = 1` gives `logMuPaper = -log p`, and with `sumTheta = 0`, `ssCoeff*A = 1`
   the deficit equals `1 + log p > 0`.  Whether `e = 1, r/n = 1` is realizable in C3
   Theta-data is NOT decided here — that is the paper 3.12 positive-part gap.

No claim of equivalence with Szpiro-6 is made here.  Strength warning: this is the
paper-NORMALIZED model inequality, not lana SSIneq and not ABC. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperNormDeficitActual

open LeanFormal.IUT.XiFPaper.Mzk1PaperNormMuActual

/-- The deficit is `ssCoeff*A - (sumLogMu + sumTheta)` (definition restated). -/
theorem deficit_expansion (ssCoeff A sumLogMu sumTheta : ℝ) :
    paperNormDeficit ssCoeff A sumLogMu sumTheta =
      ssCoeff * A - sumLogMu - sumTheta := by
  unfold paperNormDeficit
  ring

/-- The verdict is exactly nonpositivity of the deficit (re-exported). -/
theorem verdict_iff_deficit_nonpos (ssCoeff A sumLogMu sumTheta : ℝ) :
    PaperNormVerdict ssCoeff A sumLogMu sumTheta ↔
      paperNormDeficit ssCoeff A sumLogMu sumTheta ≤ 0 :=
  paperNormVerdict_iff_deficit_nonpos ssCoeff A sumLogMu sumTheta

/-- Sum form of the odd-p paper lower bound: if every place has `p_i != 2`, then
`sum_i (1 - 1/e_i - r_i/n_i)*log p_i <= sum_i logMuPaper`. -/
theorem sum_logMuPaper_ge_odd {ι : Type*} (s : Finset ι) (p e r n : ι → ℝ)
    (hp2 : ∀ i ∈ s, p i ≠ 2) (hlog : ∀ i ∈ s, 0 ≤ Real.log (p i)) :
    (∑ i ∈ s, (1 - 1 / e i - r i / n i) * Real.log (p i)) ≤
      ∑ i ∈ s, logMuPaper (p i) (e i) (r i) (n i) :=
  Finset.sum_le_sum fun i hi => logMuPaper_ge_odd (p i) (e i) (r i) (n i) (hp2 i hi) (hlog i hi)

/-- Sum form of the p=2 lower bound. -/
theorem sum_logMuPaper_ge_two {ι : Type*} (s : Finset ι) (p e r n : ι → ℝ)
    (hp2 : ∀ i ∈ s, p i = 2) (hlog : ∀ i ∈ s, 0 ≤ Real.log (p i)) :
    (∑ i ∈ s, (2 - 1 / e i - r i / n i) * Real.log (p i)) ≤
      ∑ i ∈ s, logMuPaper (p i) (e i) (r i) (n i) :=
  Finset.sum_le_sum fun i hi => logMuPaper_ge_two (p i) (e i) (r i) (n i) (hp2 i hi) (hlog i hi)

/-- **Positive part**: at `e = 1`, `r/n = 1`, odd `p`, `logMuPaper = -log p`. -/
theorem logMuPaper_e1_rn1 (p : ℝ) (hp2 : p ≠ 2) :
    logMuPaper p 1 1 1 = -Real.log p := by
  unfold logMuPaper paperMuCoeff
  rw [if_neg hp2]
  ring

/-- **The deficit can be strictly positive** (so the verdict is NOT unconditional):
with `ssCoeff*A = 1`, `sumLogMu = -log 3`, `sumTheta = 0`, the deficit is `1 + log 3 > 0`. -/
theorem deficit_pos_witness :
    0 < paperNormDeficit 1 1 (-Real.log 3) 0 := by
  unfold paperNormDeficit
  have h : 0 < Real.log 3 := Real.log_pos (by norm_num)
  nlinarith

/-- Conditional closure: if the per-place paper-normalized terms dominate the
`ssCoeff*A` budget, the verdict holds (immediate from the definition). -/
theorem verdict_of_budget {ssCoeff A sumLogMu sumTheta : ℝ}
    (h : ssCoeff * A ≤ sumLogMu + sumTheta) :
    PaperNormVerdict ssCoeff A sumLogMu sumTheta :=
  h

/-! ### A798: expanded deficit, different-term reading, and Szpiro-6 link -/

open LeanFormal.IUT.XiFPaper.Mzk1PaperNormThetaActual

/-- Expanded deficit: `ΣlogMu = diff - arch + torsion`, `Σtheta = c_lana*A` gives
`deficit = ssCoeff*A - diff + arch - torsion - c_lana*A` (algebra). -/
theorem deficit_expanded_form (ssCoeff A diff arch torsion cLana : ℝ) :
    ssCoeff * A - ((diff - arch + torsion) + cLana * A) =
      ssCoeff * A - diff + arch - torsion - cLana * A := by ring

/-- **Deficit nonpositivity** rewritten as the explicit inequality
`(ssCoeff - c_lana)*A + arch - torsion <= diff`. -/
theorem deficit_nonpos_iff (ssCoeff A diff arch torsion cLana : ℝ) :
    ssCoeff * A - diff + arch - torsion - cLana * A ≤ 0 ↔
      (ssCoeff - cLana) * A + arch - torsion ≤ diff := by
  have h : (ssCoeff - cLana) * A = ssCoeff * A - cLana * A := by ring
  rw [h]
  constructor <;> intro hh <;> linarith

/-- **Honest counterexample boundary**: when the different term is trivial (`diff = 0`),
with `ssCoeff = 1`, `c_lana = 0`, `A = 1`, `arch = torsion = 0` the deficit is `1 > 0`,
so `deficit <= 0` REQUIRES a nontrivial different/arch/torsion contribution. -/
theorem deficit_pos_no_diff : 0 < (1 : ℝ) * 1 - 0 + 0 - 0 - 0 := by norm_num

/-! ### A798/A805: sign convention note on a Szpiro-type link

The deficit inequality `deficit <= 0` (i.e. `ssCoeff*A <= sumLogMu + sumTheta`) yields,
after substituting `sumLogMu = diff - arch + torsion`, the inequality
`(ssCoeff - cLana)*A + arch - torsion <= diff`.
If additionally `diff = logq - S` (S = 6(logd+logf)+C), then this gives a LOWER bound
`S <= logq + ...`; it does NOT give the Szpiro-6 upper bound `logq <= S`.  The upper-bound
direction requires the REVERSED inequality on the left side (and is not what the paper
verdict asserts).  Hence no machine equivalence with Szpiro-6 is claimed here; the honest
statement is: `deficit <= 0` is equivalent to the explicit inequality `deficit_nonpos_iff`
above, a different (lower-bound) direction from Szpiro-6.  The paper-3.12 gap thus is NOT
reduced to Szpiro-6 in this file. -/
end LeanFormal.IUT.XiFPaper.Mzk1PaperNormDeficitActual
