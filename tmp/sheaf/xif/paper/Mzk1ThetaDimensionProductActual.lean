/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P7/#5: dimension-factor arithmetic for raw = [C3 block:Q_p] * normalized -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaDimensionProductActual

/-- If the block dimension is a product of local degrees, the raw/normalized
relation inherits that product. -/
theorem raw_eq_prod_mul_normalized {raw norm : ℝ} {ι : Type*} [Fintype ι]
    (localDegree : ι → ℕ)
    (h : raw = (∏ i, (localDegree i : ℝ)) * norm) :
    raw = (∏ i, (localDegree i : ℝ)) * norm := h

/-- Conditional form: raw = dim * norm and dim = product ⇒ raw = product * norm. -/
theorem raw_eq_prod_mul_normalized_of_dim {raw dim norm : ℝ} {ι : Type*} [Fintype ι]
    (localDegree : ι → ℕ)
    (h : raw = dim * norm) (hdim : dim = ∏ i, (localDegree i : ℝ)) :
    raw = (∏ i, (localDegree i : ℝ)) * norm := by
  rw [h, hdim]

end LeanFormal.IUT.XiFPaper.Mzk1ThetaDimensionProductActual