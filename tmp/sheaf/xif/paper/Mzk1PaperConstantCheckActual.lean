/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic
import tmp.sheaf.xif.paper.Mzk1S3137ComparisonArithmeticActual

/-!
# A527 paper constant check: |log q| normalization and the Theta-pilot coefficient

Paper anchors:
* IUT III, Corollary 3.12 (lines 10324-10353): the conclusion is `-|log(Theta)| >= -|log q|`
  (equivalently `C_Theta >= -1`), with `-|log Θ|` the procession-normalized mono-analytic
  log-volume (average over `j ∈ F_l^⋆`); no explicit constant is printed there.
* IUT IV, Theorem 1.10 (lines 1255-1385):
  - line 1358-1360: `|log(q)| = 1/(2l) * log(q)` (the normalization of the q-pilot);
  - lines 1363-1375: `C_Theta = (l+1)/(4*|log(q)|) * { (1 + 12*d_mod/l)(log(d_Ftpd) +
    log(f_Ftpd)) + 10*(e*_mod*l + eta_prm) - 1/6*(1 - 12/l^2)*log(q) } - 1`.

Consequences checked in Lean below:
1. `paperCTheta_ge_neg_one_iff`: `C_Theta >= -1` is equivalent to
   `A >= (1/6)(1 - 12/l^2) log(q)` where `A` is the bracket's positive part
   (the `1/6` coefficient is part of the paper's normalization, NOT `1`);
2. `paperAbsLogQ_eq`: `|log q| = log(q)/(2l)`;
3. `naiveThetaCoefficient`: the naive average of the theta values `q^{j^2}` over
   `F_l^⋆` (or over `j = 1..l*`) has coefficient `l(l+1)/12` of `log q`, i.e.
   `sFactor * |log q|`; the comparison `-|log q| <= -|log Θ|` is then equivalent to
   `l(l+1) <= 12`, which FAILS for the paper's `l >= 5` (`l13_fails`).  Therefore the
   naive average / hull-model coefficient `processionAverage` is NOT the paper's `|log Θ|`
   normalization.
4. `hullArithmetic_trivially_true`: in the hull model the q arithmetic volume is
   negative and the procession average positive, so their comparison is automatic —
   i.e. that reduction does not test the paper inequality (sign mismatch).

The hull model's error: it sets `thetaPilotHullLogVolumeReal = processionAverage` where
`processionAverage` is a POSITIVE multiple of `log q`, but the actual Haar hull
log-volume is NEGATIVE; and its coefficient `(l*+1)/12 = (l+1)/24` of `log q` corresponds
to the naive `j^2` average, which cannot satisfy Cor 3.12 for `l >= 5`.  The paper
coefficient enters through the `(l+1)/4` factor and the `1/6(1-12/l^2)` term of Theorem
1.10, not through `(l+1)/24`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperConstantCheckActual

/-! ## 1. Paper normalizations -/

/-- IUT IV lines 1358-1360: `|log(q)| = log(q)/(2l)`. -/
def paperAbsLogQ (l : ℕ) (logq : ℝ) : ℝ :=
  logq / (2 * (l : ℝ))

/-- The paper's `C_Theta` (IUT IV lines 1363-1375) for the positive bracket part `A`. -/
def paperCTheta (l : ℕ) (A logq : ℝ) : ℝ :=
  ((l : ℝ) + 1) / (4 * paperAbsLogQ l logq) *
      (A - (1 / 6) * (1 - 12 / ((l : ℝ) ^ 2)) * logq) - 1

theorem paperAbsLogQ_eq (l : ℕ) (logq : ℝ) :
    paperAbsLogQ l logq = logq / (2 * (l : ℝ)) :=
  rfl

/-- **`C_Theta >= -1` iff `A >= (1/6)(1 - 12/l^2) log q`** (for positive `log q`, `l`). -/
theorem paperCTheta_ge_neg_one_iff {l : ℕ} (hl : 0 < l) {logq A : ℝ}
    (hlogq : 0 < logq) :
    paperCTheta l A logq ≥ -1 ↔
      A ≥ (1 / 6) * (1 - 12 / ((l : ℝ) ^ 2)) * logq := by
  have hlR : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl
  have hpos : 0 < 4 * paperAbsLogQ l logq := by
    unfold paperAbsLogQ
    positivity
  unfold paperCTheta
  rw [show ((l : ℝ) + 1) / (4 * paperAbsLogQ l logq) *
        (A - (1 / 6) * (1 - 12 / ((l : ℝ) ^ 2)) * logq) - 1 ≥ -1 ↔
      A - (1 / 6) * (1 - 12 / ((l : ℝ) ^ 2)) * logq ≥ 0 by
    constructor <;> intro h
    · have := mul_nonneg (le_of_lt (div_pos (by positivity) hpos)) ?_
      · nlinarith
      · nlinarith
    · have hfac : 0 < ((l : ℝ) + 1) / (4 * paperAbsLogQ l logq) := div_pos (by positivity) hpos
      nlinarith [mul_pos hfac (by linarith : (0:ℝ) < A - (1/6)*(1-12/((l:ℝ)^2))*logq)]]
  constructor <;> intro h <;> linarith

/-! ## 2. The naive theta-value average coefficient -/

/-- The naive procession average of the theta values `q^{j^2}` over `F_l^⋆` has
  coefficient `l(l+1)/12` of `log q` (equivalently `sFactor * |log q|`). -/
def naiveThetaCoefficient (l : ℕ) : ℝ :=
  (l : ℝ) * ((l : ℝ) + 1) / 12

/-- With `l = 2*l* + 1` the naive coefficient equals `(l*+1)(2l*+1)/6 = sFactor`. -/
theorem naiveThetaCoefficient_eq_sFactor (n : ℕ) :
    naiveThetaCoefficient (2 * n + 1) =
      ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) / 6 := by
  unfold naiveThetaCoefficient
  push_cast
  ring

/-- The naive `|log Θ| = sFactor * |log q|` comparison with `-|log q|` is equivalent to
  `sFactor <= 1`, i.e. `l(l+1) <= 12`. -/
theorem naiveComparison_iff (l : ℕ) (hl : 0 < l) {logq : ℝ} (hlogq : 0 < logq) :
    -(paperAbsLogQ l logq) ≤ -(naiveThetaCoefficient l * paperAbsLogQ l logq) ↔
      naiveThetaCoefficient l ≤ 1 := by
  have hA : 0 < paperAbsLogQ l logq := by
    unfold paperAbsLogQ
    positivity
  constructor <;> intro h
  · nlinarith
  · nlinarith

/-- **Failure at `l = 13`** (`l* = 6`): `sFactor = 35/6 > 1`, so the naive coefficient
  cannot satisfy Cor 3.12 for paper-legal `l >= 5`. -/
theorem l13_naive_fails : ¬ (naiveThetaCoefficient 13 ≤ 1) := by
  unfold naiveThetaCoefficient
  norm_num

/-! ## 3. The hull-model arithmetic comparison is vacuous -/

open LeanFormal.IUT.XiFPaper.Mzk1S3137ComparisonArithmeticActual

/-- In the hull model the q arithmetic volume is `-m log p/(2(2l*+1))` (negative) and
  the procession average is `(l*+1)/12 * m log p` (positive for `m, log p > 0`), hence
  their comparison is automatic and does not test the paper inequality. -/
theorem hullArithmetic_trivially_true {m n : ℕ} {p : ℝ} (hm : 0 < m)
    (hp : 1 ≤ p) :
    qPilotArithmeticVolume m n p ≤ processionAverage m n p := by
  have hlog : 0 ≤ Real.log p := Real.log_nonneg hp
  unfold qPilotArithmeticVolume processionAverage
  have hposden : 0 < 2 * ((2 * n + 1 : ℕ) : ℝ) := by positivity
  have hqneg : -((m : ℝ) * Real.log p / (2 * ((2 * n + 1 : ℕ) : ℝ))) ≤ 0 := by
    apply neg_nonpos.mpr
    exact div_nonneg (mul_nonneg (by positivity) hlog) (by positivity)
  have havg_nonneg : 0 ≤ ((n : ℝ) + 1) / 12 * ((m : ℝ) * Real.log p) := by
    positivity
  linarith

end

end LeanFormal.IUT.XiFPaper.Mzk1PaperConstantCheckActual