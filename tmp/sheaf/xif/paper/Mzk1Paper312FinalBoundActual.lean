/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Paper312ExplicitActual
import Mathlib.Tactic

/-! # A783: the final bound `A <= Lbar + Dbar` — reduction to per-place local bounds -/

/- From A779: paper 3.12 <=> (sFactor-1)*A <= Lbar + Dbar, with the sufficient condition
`A <= Lbar + Dbar` (since `0 <= sFactor-1 <= 1`).  Here
  A = (1/(2l)) * sum_v qlog_v,  Lbar = sum_v log index_v,  Dbar = sum_v diff_v.

GREEN inputs for the per-place comparison:
* `logShellIntegerIndex_eq_residueCard_pow_of_powerCardHypothesis` (IndexResidueFormula:118):
  under the named residue-power hypothesis, `index_v = residueCard_v ^ a_v`;
* `logShellResidueCard` is the actual residue cardinal `p ^ f_v` (ResidueFormula:55);
* hence `log index_v = a_v * f_v * log p` (Real.log_pow below);
* `qlog_v = (f_v/[F:Q]) * ord_v(q_v) * log p` (normalized degree weights); at a bad
  multiplicative place `ord_v(q_v) = 1` (Tate parameter uniformizer), giving
  `qlog_v = (f_v/[F:Q]) * log p`.

Then the per-place bound `qlog_v/(2l) <= log index_v + diff_v` reduces to
`1/([F:Q]*2l) <= a_v` (with `diff_v = 0`), which holds whenever `a_v >= 1`.  The sum
version below is exact real arithmetic; the residue/ord inputs are the named green/paper
conditions.  If every place satisfies the per-place bound, paper 3.12 follows. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Paper312FinalBoundActual

/-- Sum of the per-place bounds gives `A <= Lbar + Dbar`. -/
theorem A_le_sum_of_local {ι : Type*} [Fintype ι] {l : ℝ} {qlog logIdx diff : ι → ℝ}
    (h : ∀ i, qlog i / (2 * l) ≤ logIdx i + diff i) :
    (1 / (2 * l)) * (∑ i, qlog i) ≤ ∑ i, (logIdx i + diff i) := by
  have h1 : (1 / (2 * l)) * (∑ i, qlog i) = ∑ i, qlog i / (2 * l) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h1]
  exact Finset.sum_le_sum (fun i _ => h i)

/-- `log (q^a) = a * log q` for positive `q` (green Real.log_pow). -/
theorem log_pow_eq_mul_log {q : ℝ} (hq : 0 < q) (a : ℕ) :
    Real.log (q ^ a) = (a : ℝ) * Real.log q := by
  rw [Real.log_pow]

/-- **Per-place bound at a bad multiplicative place with `diff = 0`**:
if `ord(q_v) = 1` and the residue-power exponent satisfies `1/([F:Q]*2l) <= a_v`, then
`qlog_v/(2l) <= log index_v`. -/
theorem local_bound_ord_one {p f Fdeg l a : ℝ}
    (hp : 0 < p) (hp1 : 1 < p) (hf : 0 < f) (hl : 0 < l) (hF : 0 < Fdeg)
    (ha : 1 ≤ a * (Fdeg * (2 * l))) :
    (f / Fdeg) * Real.log p / (2 * l) ≤ a * f * Real.log p := by
  have hlog : 0 < Real.log p := Real.log_pos hp1
  have hcoef : (f / Fdeg) / (2 * l) ≤ a * f := by
    rw [div_div]
    rw [div_le_iff₀ (by positivity : 0 < Fdeg * (2 * l))]
    nlinarith
  have h1 : (f / Fdeg) * Real.log p / (2 * l) = ((f / Fdeg) / (2 * l)) * Real.log p := by
    field_simp
  rw [h1]
  have h2 : a * f * Real.log p = (a * f) * Real.log p := by ring
  rw [h2]
  exact mul_le_mul_of_nonneg_right hcoef hlog.le

/-- Combined: if all per-place bounds hold, then the A779 explicit inequality's sufficient
condition `A <= Lbar + Dbar` holds. -/
theorem A_le_Lbar_add_Dbar {ι : Type*} [Fintype ι] {l : ℝ} {qlog logIdx diff : ι → ℝ}
    (h : ∀ i, qlog i / (2 * l) ≤ logIdx i + diff i) :
    (1 / (2 * l)) * (∑ i, qlog i) ≤ ∑ i, (logIdx i + diff i) :=
  A_le_sum_of_local h

/-- Paper 3.12 from the per-place bounds (via A779's `explicitInequality_of_bounds`). -/
theorem paper312_of_local_bounds {ι : Type*} [Fintype ι] {l sFactor : ℝ}
    {qlog logIdx diff : ι → ℝ}
    (hs0 : 0 ≤ sFactor - 1) (hs1 : sFactor - 1 ≤ 1)
    (hA0 : 0 ≤ (1 / (2 * l)) * (∑ i, qlog i))
    (h : ∀ i, qlog i / (2 * l) ≤ logIdx i + diff i) :
    LeanFormal.IUT.XiFPaper.Mzk1Paper312ExplicitActual.ExplicitPaper312Inequality
      sFactor ((1 / (2 * l)) * (∑ i, qlog i)) (∑ i, logIdx i) (∑ i, diff i) := by
  have hsum := A_le_sum_of_local h
  have hsum' : (∑ i, (logIdx i + diff i)) = (∑ i, logIdx i) + ∑ i, diff i := by
    rw [Finset.sum_add_distrib]
  rw [hsum'] at hsum
  exact LeanFormal.IUT.XiFPaper.Mzk1Paper312ExplicitActual.explicitInequality_of_bounds
    hs0 hs1 hA0 hsum

/-- Numeric sanity check: for `p = 2`, `f = 1`, `Fdeg = 1`, `l = 13`, `a = 1` the
per-place bound holds: `log 2 / 26 <= log 2`. -/
theorem numeric_check_p2 : Real.log 2 / 26 ≤ (1 : ℝ) * 1 * Real.log 2 := by
  have h : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

end LeanFormal.IUT.XiFPaper.Mzk1Paper312FinalBoundActual
