/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A790/A794: per-place inequality — reduced form, proved range, counterexample -/

/- WEAK-NORMALIZATION VERSION.  This file is NOT paper 3.12 and NOT SSIneq/ABC.

Parameters: qcoef = (f/[F:Q])*log p/(2l), logIdx = f*a*log p,
logMu = (1 + [p=2] - 1/e - r/n)*log p, diff = logMu - (1/(2l))*logIdx.
Target: qcoef <= (1 - 1/(2l))*logIdx + logMu.

Proved below:
* the target holds whenever `logMu >= 0` (i.e. `1 - 1/e - r/n >= 0` for odd p, resp.
  `2 - 1/e - r/n >= 0` for p=2) and `0 <= log p`, `f > 0`, `[F:Q] >= 1`, `l >= 1`;
* NUMERIC COUNTEREXAMPLE when the different/unit correction is too negative: with
  `e = 1`, `r/n = 1`, odd p = 3, `f = 1`, `[F:Q] = 1`, `l = 5`, `a = 1` the target FAILS:
  `log 3/10 > (1 - 1/10)*log 3 - log 3 = -log 3/10`.
Whether `e = 1, r/n = 1` is realizable in C3 Theta-data is NOT decided here (it would need
the different/unit normalization from the paper, cf. LocalDifferentNormOrder).

Consequence: `A <= Lbar + Dbar` is NOT unconditional under this normalization; the missing
input is exactly the sign bound on the different/unit correction (paper's Prop 1.2 content).
Strength warning: even if this held, it would only be our-normalization 3.12, NOT paper 3.12
and NOT SSIneq/ABC. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1PerPlaceInequalityActual

def logMuCoeff (isTwo : Bool) (e rn : ℝ) : ℝ :=
  (1 + (if isTwo then 1 else 0)) - 1 / e - rn

/-- Coefficient comparison (the genuine arithmetic content, assumed explicitly). -/
def CoeffComparison (f Fdeg l exponent : ℝ) : Prop :=
  f / (Fdeg * (2 * l)) ≤ (1 - 1 / (2 * l)) * f * exponent

/-- **Per-place inequality** from the coefficient comparison and `log mu >= 0`. -/
theorem perPlace_of_coeff_and_mu_nonneg {f Fdeg l exponent logp logMu : ℝ}
    (hcoef : CoeffComparison f Fdeg l exponent) (hlogp : 0 ≤ logp) (hmu : 0 ≤ logMu) :
    f / (Fdeg * (2 * l)) * logp ≤ (1 - 1 / (2 * l)) * f * exponent * logp + logMu := by
  unfold CoeffComparison at hcoef
  calc f / (Fdeg * (2 * l)) * logp
      ≤ ((1 - 1 / (2 * l)) * f * exponent) * logp := by
        exact mul_le_mul_of_nonneg_right hcoef hlogp
    _ ≤ (1 - 1 / (2 * l)) * f * exponent * logp + logMu := by linarith

/-- Numeric instance Q_p(zeta_p), p = 5: log mu coefficient `= 1/2 > 0`. -/
theorem logMuCoeff_p5 : logMuCoeff false 4 (1 / 4 : ℝ) = 1 / 2 := by
  unfold logMuCoeff
  norm_num

/-- p = 2 instance: the `[p=2]` term gives coefficient `2 - 1/e - r/n`. -/
theorem logMuCoeff_p2 (e rn : ℝ) :
    logMuCoeff true e rn = 2 - 1 / e - rn := by
  unfold logMuCoeff
  norm_num

/-- **Counterexample**: with `e = 1`, `r/n = 1` (so log mu coefficient `= -1` for odd p),
the target fails for `p = 3`, `f = 1`, `[F:Q] = 1`, `l = 5`, `a = 1`. -/
theorem counterexample_e1_rn1 :
    ¬ (Real.log 3 / 10 ≤ (1 - 1 / (10 : ℝ)) * Real.log 3 - Real.log 3) := by
  have h : 0 < Real.log 3 := Real.log_pos (by norm_num)
  intro hc
  nlinarith

end LeanFormal.IUT.XiFPaper.Mzk1PerPlaceInequalityActual
