/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1TorsionLogDonorActual
import tmp.sheaf.xif.paper.Mzk1PerPlaceBoundHullActual
import Mathlib.Tactic
/-! # Conditional per-place bound from an explicit torsion gap

`hTub : #T ≤ (q-1)*C` is an EXPLICIT CONDITIONAL GAP. The local
`μ_{p^a} ⊆ K → p^{a-1}(p-1) ∣ eK` ramification bound is not available in the
current API, so `C = p^{v_p(eK)+1}` is supplied as a hypothesis here. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1TorsionPerPlaceConditionalActual
open LeanFormal.IUT.LocalFieldLogarithm
/-- Conditional per-place bound: with the torsion upper bound `#T ≤ (q-1)*C`,
a lower bound for `logMu`, and the arithmetic base bound, the paper per-place
inequality follows. -/
theorem perPlace_bound_of_torsion_le
    {qcoef logMu logIdx L base l : ℝ} {q1 T C : Nat}
    (hq1 : 0 < q1) (hC : 0 < C) (hTpos : 0 < T)
    (hTub : T ≤ q1 * C)
    (hlogIdx : logIdx = base + Real.log ((q1 : ℝ) / (T : ℝ)))
    (hmu : L ≤ logMu)
    (hl : 1 ≤ 2 * l)
    (hbase : qcoef ≤ L + (1 - 1 / (2 * l)) * (base - Real.log (C : ℝ))) :
    qcoef ≤ logMu + (1 - 1 / (2 * l)) * logIdx := by
  have hlog := log_torsion_ratio_ge_neg_log hq1 hC hTpos hTub
  have hlpos : 0 < l := by nlinarith
  have hcoef : 0 ≤ 1 - 1 / (2 * l) := by
    rw [sub_nonneg, div_le_one (by positivity : (0 : ℝ) < 2 * l)]
    exact hl
  have hlogIdx_ge : base - Real.log (C : ℝ) ≤ logIdx := by
    rw [hlogIdx]
    linarith
  have hmul : (1 - 1 / (2 * l)) * (base - Real.log (C : ℝ)) ≤
      (1 - 1 / (2 * l)) * logIdx :=
    mul_le_mul_of_nonneg_left hlogIdx_ge hcoef
  linarith
end LeanFormal.IUT.XiFPaper.Mzk1TorsionPerPlaceConditionalActual
end