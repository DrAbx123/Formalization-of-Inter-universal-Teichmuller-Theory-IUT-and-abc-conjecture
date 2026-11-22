/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Mzk1SSIneqNonemptyActual — R3 nonemptiness: a class of D satisfying SSIneq (A764)

ROUTE R3 (`coord/ROUTES-FINAL-GAP.md` §3).  Abstract arithmetic form of
`Wall.SSIneq` (lana `Iut/Wall/MultiContainer.lean`): with
`s(l) = l(l+1)/12`, `A = log q/(2l)` and `V = logVol(hull(vcI D))`,

  `SSIneq D  ⟺  (s(l) − 1)·A ≤ V`,

which equals `((l+1)/24 − 1/(2l))·log q ≤ V`.  This file proves:

* **conditional nonemptiness**: if `σ(D) = log q/(log d + log f) ≤ 5` (i.e. `≤ 6 − δ`
  with `δ ≥ 1`) and the hull lower bound `V ≥ (1/4)·l·(log d + log f)` holds, then
  `SSIneq D` (abstract form), for every `l ≥ 5`;
* **small-`l` sharpening at σ = 6**: for `5 ≤ l ≤ 12`, `σ ≤ 6` already suffices;
* **exact gap**: for `l > 12`, at `σ = 6` the inequality needs the extra
  `(1/4 − 3/l)·(log d + log f)`, i.e. `V ≥ (l/4 + (1/4 − 3/l))·(log d + log f)`;
* numeric witnesses for `l = 5, 7, 11` (σ = 6) and `l = 13` (σ = 4).

Everything here is pure real arithmetic; no lana modules are imported and no
structural input is assumed as an axiom. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1SSIneqNonemptyActual

/-- `sFactor l = l(l+1)/12` (lana `sFactor` at `n = (l−1)/2`). -/
def sFactor (l : ℝ) : ℝ := l * (l + 1) / 12

/-- `absLogQ = log q /(2l)` (lana `absLogQ`). -/
def absLogQ (qlog l : ℝ) : ℝ := qlog / (2 * l)

/-- Abstract `SSIneq` left-hand side `(s − 1)·A`. -/
def ssIneqLHS (qlog l : ℝ) : ℝ := (sFactor l - 1) * absLogQ qlog l

/-- The left-hand side in the log-q coefficient form. -/
theorem ssIneqLHS_eq {qlog l : ℝ} (hl : l ≠ 0) :
    ssIneqLHS qlog l = ((l + 1) / 24 - 1 / (2 * l)) * qlog := by
  unfold ssIneqLHS sFactor absLogQ
  field_simp
  ring

/-- **Coefficient bound** (δ ≥ 1): `(l+1)/24 − 1/(2l) ≤ l/(4(6−δ))` for `l ≥ 5`. -/
theorem coeff_le_quarter_div {l δ : ℝ} (hl : 5 ≤ l) (hδ : 1 ≤ δ) (hδ6 : δ < 6) :
    (l + 1) / 24 - 1 / (2 * l) ≤ l / (4 * (6 - δ)) := by
  have hl0 : (0 : ℝ) < l := by linarith
  have h6 : (0 : ℝ) < 6 - δ := by linarith
  -- density: (l+1)/24 − 1/(2l) ≤ l/20, and l/20 ≤ l/(4(6−δ)) for δ ≥ 1
  have hbase : (l + 1) / 24 - 1 / (2 * l) ≤ l / 20 := by
    have hform : (l + 1) / 24 - 1 / (2 * l) = (5 * l ^ 2 + 5 * l - 60) / (120 * l) := by
      field_simp
      ring
    rw [hform]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 120 * l)]
    have hr : l / 20 * (120 * l) = 6 * l ^ 2 := by ring
    rw [hr]
    nlinarith [sq_nonneg (l - 1)]
  have hmono : l / 20 ≤ l / (4 * (6 - δ)) := by
    have hbpos : (0 : ℝ) < 4 * (6 - δ) := by positivity
    have hbc : 4 * (6 - δ) ≤ 20 := by linarith
    have := div_le_div_of_nonneg_left (le_of_lt hl0) hbpos hbc
    -- this : l / 20 ≤ l / (4 * (6 - δ))
    exact this
  linarith

/-- **Conditional nonemptiness** (δ ≥ 1 branch): if the hull lower bound
`V ≥ (1/4)·l·(log d + log f)` holds and `log q ≤ (6 − δ)(log d + log f)` with
`δ ≥ 1`, then `SSIneq` (abstract form) holds for `l ≥ 5`. -/
theorem ssIneq_of_sigma_bound {qlog dlog flog V l δ : ℝ} (hl : 5 ≤ l) (hδ : 1 ≤ δ)
    (hδ6 : δ < 6)
    (hdf : 0 ≤ dlog + flog) (hq : 0 ≤ qlog)
    (hσ : qlog ≤ (6 - δ) * (dlog + flog))
    (hV : (1 / 4) * l * (dlog + flog) ≤ V) :
    ssIneqLHS qlog l ≤ V := by
  have hl0 : l ≠ 0 := by linarith
  have h6 : (0 : ℝ) < 6 - δ := by linarith
  have hlpos : (0 : ℝ) < l := by linarith
  rw [ssIneqLHS_eq hl0]
  -- coefficient × qlog ≤ coefficient × (6−δ)(d+f) ≤ (l/4)(d+f) ≤ V
  have hcq : ((l + 1) / 24 - 1 / (2 * l)) * qlog ≤
      l / (4 * (6 - δ)) * qlog := by
    apply mul_le_mul_of_nonneg_right (coeff_le_quarter_div hl hδ hδ6) hq
  have hdiv : qlog / (6 - δ) ≤ dlog + flog := by
    rw [div_le_iff₀ h6]
    nlinarith [hσ]
  have hmid : l / (4 * (6 - δ)) * qlog = (l / 4) * (qlog / (6 - δ)) := by
    field_simp
  have h1 : l / (4 * (6 - δ)) * qlog ≤ (l / 4) * (dlog + flog) := by
    rw [hmid]
    exact mul_le_mul_of_nonneg_left hdiv (by linarith)
  linarith

/-- **Small-`l` sharpening at σ = 6**: for `5 ≤ l ≤ 12` and `log q ≤ 6(log d + log f)`,
the hull lower bound `V ≥ (l/4)(log d + log f)` already gives `SSIneq`. -/
theorem ssIneq_of_sigma_six_small {qlog dlog flog V l : ℝ} (hl5 : 5 ≤ l) (hl12 : l ≤ 12)
    (hdf : 0 ≤ dlog + flog) (hq : 0 ≤ qlog)
    (hσ : qlog ≤ 6 * (dlog + flog))
    (hV : (1 / 4) * l * (dlog + flog) ≤ V) :
    ssIneqLHS qlog l ≤ V := by
  have hl0 : l ≠ 0 := by linarith
  have hlpos : (0 : ℝ) < l := by linarith
  rw [ssIneqLHS_eq hl0]
  have hcoef : (l + 1) / 24 - 1 / (2 * l) ≤ l / 24 := by
    have h1 : (l + 1) / 24 - 1 / (2 * l) = l / 24 + (1 / 24 - 1 / (2 * l)) := by ring
    rw [h1]
    have h2 : (1 / 24 : ℝ) - 1 / (2 * l) ≤ 0 := by
      rw [sub_nonpos]
      have h24 : (1 : ℝ) / 24 ≤ 1 / (2 * l) := by
        have h2l : (0 : ℝ) < 2 * l := by linarith
        have hle : 2 * l ≤ 24 := by linarith
        exact one_div_le_one_div_of_le h2l hle
      exact h24
    linarith
  have hcq : ((l + 1) / 24 - 1 / (2 * l)) * qlog ≤ (l / 24) * qlog := by
    apply mul_le_mul_of_nonneg_right hcoef hq
  have hqdiv : qlog / 6 ≤ dlog + flog := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 6)]
    nlinarith [hσ]
  have hmid : (l / 24) * qlog = (l / 4) * (qlog / 6) := by
    field_simp
    ring
  have h1 : (l / 24) * qlog ≤ (l / 4) * (dlog + flog) := by
    rw [hmid]
    exact mul_le_mul_of_nonneg_left hqdiv (by linarith)
  linarith

/-- **Exact gap at σ = 6 for `l > 12`**: the `σ = 6` LHS exceeds `(l/4)(log d + log f)`
by exactly `(1/4 − 3/l)·(log d + log f)`. -/
theorem gap_sigma_six {qlog dlog flog l : ℝ} (hl : 12 < l)
    (hq : qlog = 6 * (dlog + flog)) (hdf : 0 ≤ dlog + flog) :
    ssIneqLHS qlog l - (1 / 4) * l * (dlog + flog) =
      (1 / 4 - 3 / l) * (dlog + flog) := by
  have hl0 : l ≠ 0 := by linarith
  rw [ssIneqLHS_eq hl0, hq]
  field_simp
  ring

/-- The gap `1/4 − 3/l` is positive for `l > 12`. -/
theorem gap_pos {l : ℝ} (hl : 12 < l) : (0 : ℝ) < 1 / 4 - 3 / l := by
  rw [sub_pos]
  rw [div_lt_iff₀ (by linarith : (0 : ℝ) < l)]
  linarith

/-! ### Numeric witnesses -/

/-- Witness `l = 5`, `σ = 6`: `SSIneq` holds with `V = (5/4)(log d + log f)`. -/
theorem witness_l5 : ssIneqLHS 6 5 ≤ 2 := by
  rw [ssIneqLHS_eq (by norm_num : (5 : ℝ) ≠ 0)]
  norm_num

/-- Witness `l = 7`, `σ = 6`. -/
theorem witness_l7 : ssIneqLHS 6 7 ≤ (7 / 4 : ℝ) := by
  rw [ssIneqLHS_eq (by norm_num : (7 : ℝ) ≠ 0)]
  norm_num

/-- Witness `l = 11`, `σ = 6`. -/
theorem witness_l11 : ssIneqLHS 6 11 ≤ (11 / 4 : ℝ) := by
  rw [ssIneqLHS_eq (by norm_num : (11 : ℝ) ≠ 0)]
  norm_num

/-- Witness `l = 13`, `σ = 4`: the δ = 2 branch (σ ≤ 5) with margin. -/
theorem witness_l13 : ssIneqLHS 4 13 ≤ (13 / 4 : ℝ) := by
  rw [ssIneqLHS_eq (by norm_num : (13 : ℝ) ≠ 0)]
  norm_num

/-! ### Rows -/

def r3NonemptyRows : List (String × String) :=
  [ ("sFactor/absLogQ/ssIneqLHS definitions", "DEFINED (abstract form)"),
    ("ssIneqLHS = ((l+1)/24 − 1/(2l))·log q", "PROVED"),
    ("σ ≤ 6−δ, δ≥1 ⇒ SSIneq (l≥5)", "PROVED (conditional)"),
    ("σ ≤ 6, 5≤l≤12 ⇒ SSIneq", "PROVED (conditional)"),
    ("σ = 6, l>12: exact gap (1/4−3/l)(log d+log f)", "PROVED"),
    ("numeric witnesses l=5,7,11,13", "PROVED") ]

theorem r3NonemptyRows_length : r3NonemptyRows.length = 6 := rfl

#check ssIneq_of_sigma_bound
#check ssIneq_of_sigma_six_small
#check gap_sigma_six
#check r3NonemptyRows_length

end LeanFormal.IUT.XiFPaper.Mzk1SSIneqNonemptyActual
end
