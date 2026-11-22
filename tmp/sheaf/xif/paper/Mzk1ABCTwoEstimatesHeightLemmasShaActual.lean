import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesShaActual

/-!
# A594 height-estimate intermediate lemmas (shehdd)

Numerical reductions for the first IUT IV Thm 1.10 estimate (the height bound).
Objects (`ABCTwoEstimates`) are NOT changed; these are pure real-arithmetic
lemmas plus the standard implication from a weight bound to the height estimate.

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesHeightLemmasShaActual

/-- Monotonicity in `δ` for the height estimate when the log-volume reading is
nonnegative: a bound at `δ0 > 0` implies the bound at every `δ >= δ0`. -/
theorem height_estimate_mono_delta {h L δ0 δ : Real}
    (hL : 0 ≤ L) (hδ0 : 0 < δ0) (hδ : δ0 ≤ δ)
    (hbound : h ≤ (1 + δ0) * L) : h ≤ (1 + δ) * L := by
  have hle : (1 + δ0) * L ≤ (1 + δ) * L :=
    mul_le_mul_of_nonneg_right (by linarith) hL
  linarith [hbound]

/-- From a pointwise weight bound `h <= w` (`w >= 0`, `δ > 0`) one gets the
height-estimate shape `h <= (1+δ)*w`.  This is the standard route
`height <= arithmeticWeight` ⇒ `height_estimate` with `logVolume = weight`. -/
theorem height_estimate_of_weight_bound {h w δ : Real}
    (hw : 0 ≤ w) (hδ : 0 < δ) (hbound : h ≤ w) :
    h ≤ (1 + δ) * w := by
  have hwδ : 0 ≤ δ * w := mul_nonneg (le_of_lt hδ) hw
  nlinarith [hbound]

/-- Ratio form: for `L > 0`, the height estimate is equivalent to
`h / L <= 1 + δ`. -/
theorem height_estimate_iff_ratio {h L δ : Real} (hL : 0 < L) :
    h ≤ (1 + δ) * L ↔ h / L ≤ 1 + δ := by
  rw [div_le_iff₀ hL]
  rfl

end LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesHeightLemmasShaActual
