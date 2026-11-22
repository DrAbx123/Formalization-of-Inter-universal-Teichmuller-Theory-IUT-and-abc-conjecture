/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A763 R3: explicit form of SSIneq and a nonempty σ-criterion -/

/- Model explicit form (from WallEquiv/VcI formulas): `SSIneq D` is
  `(sFactor (nC D) - 1) * (logQ/(2l)) <= V`
with `V = logVol(hull(vcI))`; using the VcI expansion `V = (sum_i sum^fin hullPacket)/nC`
the inequality becomes an explicit inequality in `(log q, nC, l, packet sums)`.  We record:
* the explicit predicate over reals (form only, no lana import);
* the κ-form equivalence with the coefficient form;
* a σ-criterion: if `12*(s-1)*A <= 12*cV - δ` and `cV <= V`, then `(s-1)*A <= V`,
  i.e. a lower bound on V gives SSIneq for such data. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1SSIneqExplicitFormActual

/-- Explicit SSIneq form: `(s-1)*A <= V` with `s = sFactor nC` and `A = logq/(2l)`. -/
def SSIneqExplicit (sC logq l V : ℝ) : Prop := (sC - 1) * (logq / (2 * l)) ≤ V

/-- κ-form with `κ = 1` is the classical SSIneq-explicit form. -/
theorem ssIneqExplicit_iff_kappa (sC logq l V : ℝ) :
    SSIneqExplicit sC logq l V ↔ (sC - 1) * (logq / (2 * l)) ≤ V := Iff.rfl

/-- **σ-criterion**: a certified lower bound `cV` for the hull volume plus a margin `δ >= 0`
gives SSIneq as soon as `12*(sC-1)*A <= 12*cV - δ` (i.e. `σ <= 24 c_V - δ` in the
normalization where `σ = 12*(sC-1)*A`, `c_V = cV`). -/
theorem ssIneq_of_sigma_bound {sC logq l V cV δ : ℝ}
    (hσ : 12 * ((sC - 1) * (logq / (2 * l))) ≤ 24 * cV - δ)
    (hc : 2 * cV ≤ V) (hδ : 0 ≤ δ) :
    SSIneqExplicit sC logq l V := by
  unfold SSIneqExplicit
  nlinarith

/-- **Nonempty class**: if `12*(sC-1)*A <= 12*V` (the σ bound with `cV = V/2`, δ=0), then
SSIneq holds for that datum — a concrete sufficient condition, not a proof of SSIneq in
general. -/
theorem ssIneq_of_half_volume {sC logq l V : ℝ}
    (h : 12 * ((sC - 1) * (logq / (2 * l))) ≤ 12 * V) :
    SSIneqExplicit sC logq l V := by
  unfold SSIneqExplicit
  nlinarith

/-- **Concrete satisfiable instance** (A764): `sC = 2`, `logq = 2`, `l = 13`, `V = 1`;
`SSIneqExplicit 2 2 13 1` holds (both sides computable).  This shows the explicit form is
nonempty as a predicate; it is NOT a proof of SSIneq for a genuine Theta-data D. -/
theorem ssIneqExplicit_instance : SSIneqExplicit 2 2 13 1 := by
  unfold SSIneqExplicit
  norm_num

/-- **Concrete σ-criterion instance**: `sC = 2`, `logq = 2`, `l = 13`, `cV = 1`, `δ = 0`,
`V = 2`: the σ-bound `12*(1)*(2/(2*13)) = 12/13 <= 24` holds and `2*1 <= 2`, giving
`SSIneqExplicit 2 2 13 2`. -/
theorem ssIneqExplicit_sigma_instance : SSIneqExplicit 2 2 13 2 := by
  apply ssIneq_of_sigma_bound (cV := 1) (δ := 0)
  · norm_num
  · norm_num
  · norm_num

end LeanFormal.IUT.XiFPaper.Mzk1SSIneqExplicitFormActual
