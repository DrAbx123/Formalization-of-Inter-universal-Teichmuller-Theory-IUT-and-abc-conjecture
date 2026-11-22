import Mathlib.Tactic
/-! Absorbing the Cor 3.12 logQ term to derive the Thm 1.10 numeric logQ bound.

From hCor312
  (1/6) logQ <= (1+12 d/l) S + 10 E + (2/l^2) logQ,
move the last term left:
  (1/6 - 2/l^2) logQ <= (1+12 d/l) S + 10 E.
For l >= 7, d >= 1, S,E >= 0 the coefficient inequalities give
  logQ <= 4 d l S + 5 l^2 E.
The case l = 5 is recorded separately as not following from the same constants. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110LogQActual
/-- Coefficient positivity: `0 < 1/6 - 2/l^2` for `l >= 7`. -/
theorem logQ_coeff_pos {l : Real} (hl : 7 ≤ l) : 0 < 1 / 6 - 2 / l ^ 2 := by
  have hl0 : (0 : Real) < l := by linarith
  have hl2 : (0 : Real) < l ^ 2 := pow_pos hl0 2
  rw [show (2 : Real) / l ^ 2 = 2 / l ^ 2 by rfl]
  have h : (2 : Real) / l ^ 2 ≤ 2 / 49 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
  linarith
/-- Absorb the `(2/l^2) logQ` term of hCor312 into the left side. -/
theorem hCor312_absorb {l d S E Q : Real}
    (h312 : (1 / 6) * Q ≤ (1 + 12 * d / l) * S + 10 * E + (2 / l ^ 2) * Q) :
    (1 / 6 - 2 / l ^ 2) * Q ≤ (1 + 12 * d / l) * S + 10 * E := by
  nlinarith [h312]
/-- **Numerical logQ bound derived from hCor312**, for `l >= 7`, `d >= 1`, `S,E >= 0`. -/
theorem logQ_bound_of_hCor312
    {l d S E Q : Real}
    (hl : 7 ≤ l) (hd : 1 ≤ d) (hS : 0 ≤ S) (hE : 0 ≤ E)
    (h312 : (1 / 6) * Q ≤ (1 + 12 * d / l) * S + 10 * E + (2 / l ^ 2) * Q) :
    Q ≤ (4 * d * l) * S + 5 * l ^ 2 * E := by
  have hc : 0 < 1 / 6 - 2 / l ^ 2 := logQ_coeff_pos hl
  have habs := hCor312_absorb h312
  have hQ : Q ≤ ((1 + 12 * d / l) * S + 10 * E) / (1 / 6 - 2 / l ^ 2) := by
    rw [le_div_iff₀ hc]
    linarith [habs]
  refine le_trans hQ ?_
  have hl0 : (0 : Real) < l := by linarith
  have hl2 : (0 : Real) < l ^ 2 := pow_pos hl0 2
  have hden : (0 : Real) < 1 / 6 - 2 / l ^ 2 := hc
  have hl2ge : (49 : Real) ≤ l ^ 2 := by
    nlinarith [sq_nonneg (l - 7)]
  have hbase : 0 ≤ 4 * l ^ 2 - 6 * l - 120 := by
    nlinarith [hl]
  have hdl : 0 ≤ (d - 1) * (l ^ 2 - 49) := by
    apply mul_nonneg
    · linarith
    · nlinarith [hl]
  have hScleared : 0 ≤ 4 * d * l * (l ^ 2 - 12) - (6 * l ^ 2 + 72 * d * l) := by
    nlinarith [hbase, hdl, hd, hl2ge]
  have hEcleared : 0 ≤ 5 * l ^ 2 * (l ^ 2 - 24) := by
    nlinarith [hl2ge]
  rw [div_le_iff₀ hden]
  field_simp
  nlinarith [mul_nonneg hS hScleared, mul_nonneg hE hEcleared, hS, hE]
/-- For `l = 5` the same constants do **not** follow from Cor 3.12 alone:
the coefficient comparison fails already at `d = 1`.  This is recorded as the exact
remaining l=5 input, not assumed. -/
def l5RemainingInput : List String :=
  [ "l = 5 separate case of the logQ numeric bound (not derivable from the same hCor312 constants)" ]
theorem l5RemainingInput_length : l5RemainingInput.length = 1 := rfl
#check logQ_bound_of_hCor312
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110LogQActual
end
