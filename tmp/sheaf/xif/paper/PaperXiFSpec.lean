import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # Paper xi-f statement layer

This file fixes the actual scalar form of IUT III Corollary 3.12 Step (xi-f):

  -|log q| in R_{<= -|log Theta|}

and proves the real-arithmetic lemmas that the source construction must feed.
No q-pilot object, hull, or source theorem is asserted here; those are
constructed in the paper-level modules. This is the statement/arithmetic
kernel, not a substitute for the source objects.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper

/-- The signed q-pilot log-volume `-|log q|` of Step (xi-f). -/
def paperSignedLog (q : Real) : Real := -|Real.log q|

/-- The paper ray `R_{<= -|log Theta|}`. -/
def paperHullRay (thetaLog : Real) : Set Real := Set.Iic thetaLog

/-- Paper xi-f: the signed q-pilot log lies in the Theta-hull ray. -/
def paperXiF (q thetaLog : Real) : Prop :=
  paperSignedLog q ∈ paperHullRay thetaLog

theorem paperXiF_iff (q thetaLog : Real) :
    paperXiF q thetaLog ↔ paperSignedLog q ≤ thetaLog :=
  Iff.rfl

theorem paperSignedLog_eq_neg_abs_log (q : Real) :
    paperSignedLog q = -|Real.log q| := rfl

theorem paperSignedLog_neg_iff (q : Real) :
    paperSignedLog q < 0 ↔ |Real.log q| ≠ 0 := by
  unfold paperSignedLog
  constructor
  · intro h hzero
    rw [hzero] at h
    rw [neg_zero] at h
    exact lt_irrefl 0 h
  · intro h
    exact neg_neg_of_pos (lt_of_le_of_ne (abs_nonneg _) (Ne.symm h))

/-- If `0 < q < 1`, the signed q-pilot log is negative. -/
theorem paperSignedLog_neg_of_pos_lt_one {q : Real} (hq0 : 0 < q) (hq1 : q < 1) :
    paperSignedLog q < 0 := by
  rw [paperSignedLog_eq_neg_abs_log]
  exact neg_neg_of_pos (abs_pos.mpr (ne_of_lt (Real.log_neg hq0 hq1)))

/-- If `0 < q < 1` and `0 < theta < 1`, xi-f is equivalent to
`|log theta| <= |log q|` (`q` at least as contracted as `theta`). -/
theorem paperXiF_iff_abs_log_ge_of_pos_lt_one {q theta : Real}
    (hq0 : 0 < q) (hq1 : q < 1) (ht0 : 0 < theta) (ht1 : theta < 1) :
    paperXiF q (-|Real.log theta|) ↔ |Real.log theta| ≤ |Real.log q| := by
  unfold paperXiF paperHullRay paperSignedLog
  rw [Set.mem_Iic]
  have hqlog : Real.log q < 0 := Real.log_neg hq0 hq1
  have htlog : Real.log theta < 0 := Real.log_neg ht0 ht1
  rw [abs_of_neg hqlog, abs_of_neg htlog]
  constructor <;> intro h <;> linarith

/-- Sufficient source-level comparison: if `q <= theta` and both lie in `(0,1)`,
then the signed q-pilot log lies in the Theta-hull ray. This is the exact
direction needed when the q-pilot value is the contracted base unit of the
theta packet. -/
theorem paperXiF_of_q_le_theta {q theta : Real}
    (hq0 : 0 < q) (hq1 : q < 1) (ht0 : 0 < theta) (ht1 : theta < 1)
    (h : q ≤ theta) :
    paperXiF q (-|Real.log theta|) := by
  rw [paperXiF_iff_abs_log_ge_of_pos_lt_one hq0 hq1 ht0 ht1]
  rw [abs_of_neg (Real.log_neg hq0 hq1), abs_of_neg (Real.log_neg ht0 ht1)]
  linarith [Real.log_le_log hq0 h]

/-- If the q-pilot value equals the theta value, xi-f holds with equality. -/
theorem paperXiF_refl (q : Real) :
    paperXiF q (-|Real.log q|) := by
  unfold paperXiF paperHullRay paperSignedLog
  rw [Set.mem_Iic]

/-- The final real-arithmetic step of Corollary 3.12: from xi-f
`-|log q| <= thetaLog` and `thetaLog <= cTheta * |log q|` with
`|log q| > 0`, conclude `-1 <= cTheta`. -/
theorem paperXiF_final_bound {q thetaLog cTheta : Real}
    (hq : Real.log q ≠ 0)
    (hxi : paperSignedLog q ≤ thetaLog)
    (hc : thetaLog ≤ cTheta * |Real.log q|) :
    -1 ≤ cTheta := by
  have hqpos : 0 < |Real.log q| := abs_pos.mpr hq
  have hdiv : thetaLog / |Real.log q| ≤ cTheta :=
    (div_le_iff₀ hqpos).mpr hc
  have hlower : (-1 : Real) ≤ thetaLog / |Real.log q| := by
    rw [le_div_iff₀ hqpos, neg_one_mul]
    simpa [paperSignedLog] using hxi
  linarith

/-- Packaged paper xi-f scalar data. The source construction must provide
the q parameter, the signed theta-hull log, and the xi-f inclusion. -/
structure PaperXiFScalarData where
  q : Real
  q_pos : 0 < q
  q_log_ne_zero : Real.log q ≠ 0
  thetaHullLog : Real
  xi_f : paperXiF q thetaHullLog

namespace PaperXiFScalarData

theorem signedLog_ne_zero (D : PaperXiFScalarData) : paperSignedLog D.q ≠ 0 := by
  unfold paperSignedLog
  rw [neg_ne_zero, abs_ne_zero]
  exact D.q_log_ne_zero

theorem signedLog_nonpos (D : PaperXiFScalarData) : paperSignedLog D.q ≤ 0 := by
  unfold paperSignedLog
  exact neg_nonpos.mpr (abs_nonneg _)

theorem cTheta_lowerBound (D : PaperXiFScalarData) {cTheta : Real}
    (hc : D.thetaHullLog ≤ cTheta * |Real.log D.q|) :
    -1 ≤ cTheta :=
  paperXiF_final_bound D.q_log_ne_zero D.xi_f hc

end PaperXiFScalarData

end XiFPaper
end LeanFormal.IUT

end