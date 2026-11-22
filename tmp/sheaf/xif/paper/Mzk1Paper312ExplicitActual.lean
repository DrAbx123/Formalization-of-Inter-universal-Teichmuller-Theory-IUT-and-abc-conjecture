/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A779: paper 3.12 as an explicit arithmetic inequality (direct attack) -/

/- Explicit form of the scaled-theta side (hull/shehdd scaled region + green
IntegralLogShellHaarIndex/IndexArithmetic):
* per bad place v and label j = i+1: local term = log index_v - (j^2/(2l))*qlog_v + diff_v
  where qlog_v = |log q_v| (magnitudes) and diff_v collects the different/unit correction;
* capsule average over i: (1/nC) * sum_{j<nC}; using the PROVED capsule_average_coeff
  ((1/n)*sum (j+1)^2/(2l) = sFactor(n)/(2l)) and clana_coeff, the theta side becomes
  thetaSide = Lbar + Dbar - sFactor(nC) * A,
  where Lbar = sum_v log index_v, Dbar = sum_v diff_v, A = (1/(2l)) * sum_v qlog_v;
* q side: qReading = -A (green S3137 qPilotLogVolumeReading_nonpos).

Then qReading <= thetaSide is EXACTLY (sFactor(nC) - 1) * A <= Lbar + Dbar.
The genuine local content is A <= Lbar + Dbar (each qlog_v dominated by
log index_v + diff_v); log index_v >= 0 is GREEN (logShellIntegerIndex >= 1).
The different/unit correction diff_v >= 0 is NOT yet proved; its bounds are the content of
IntegralLogShellSharpBounds A/B exponents. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Paper312ExplicitActual

def ExplicitPaper312Inequality (sFactor A Lbar Dbar : ℝ) : Prop :=
  (sFactor - 1) * A ≤ Lbar + Dbar

theorem paper312_iff_explicit {sFactor A Lbar Dbar qReading thetaSide : ℝ}
    (hq : qReading = -A) (hθ : thetaSide = Lbar + Dbar - sFactor * A) :
    qReading ≤ thetaSide ↔ ExplicitPaper312Inequality sFactor A Lbar Dbar := by
  unfold ExplicitPaper312Inequality
  rw [hq, hθ]
  constructor <;> intro h <;> nlinarith

/-- Conditional closure: if 0 <= sFactor-1 <= 1, 0 <= A and A <= Lbar + Dbar, then the
explicit inequality holds (and hence the paper comparison).  The hypothesis
A <= Lbar + Dbar is the genuine local content; it is NOT automatic from nonnegativity. -/
theorem explicitInequality_of_bounds {sFactor A Lbar Dbar : ℝ}
    (hs0 : 0 ≤ sFactor - 1) (hs1 : sFactor - 1 ≤ 1)
    (hA0 : 0 ≤ A) (hA : A ≤ Lbar + Dbar) :
    ExplicitPaper312Inequality sFactor A Lbar Dbar := by
  unfold ExplicitPaper312Inequality
  nlinarith

/-- Green component: log index >= 0 (index >= 1). -/
theorem log_index_nonneg (index : ℕ) (h : 1 ≤ index) :
    0 ≤ Real.log (index : ℝ) := by
  apply Real.log_nonneg
  exact_mod_cast h

end LeanFormal.IUT.XiFPaper.Mzk1Paper312ExplicitActual
