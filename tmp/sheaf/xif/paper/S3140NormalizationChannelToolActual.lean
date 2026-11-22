import Mathlib

/-!
# S3140 generic normalization-channel tool (mathematical tool manufacture)

**Generic reusable TOOL, fully proved.**  It separates a readout's *normalization
convention* from its *value* in the form actually used by the IUT normalization
identifications: a per-place raw reading equals the degree-normalized V-form plus
an exact normalization factor, and the weighted regional reading inherits the
same decomposition.  This is the generic shape behind hull's
`thetaNormalizationFactor` / `c3NormalizedLogVolume` channel, mainline's
weighted regional readouts, and any future LGP/hull normalization consumer.

Nothing here is an instantiation: the instantiation data (identifying the V-form
of the actual paper hull with the canonical rooted readout, and vanishing/exact
value of the normalization factor) remains a named exact missing at the consumer
site.  This tool file only proves the generic algebra that transports a
per-place normalization decomposition through a finite weighted sum.

No sorry/axiom/arbitrary carrier.  WRITE-ONLY.
-/

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.S3140NormalizationChannelToolActual

universe u

/-- The exact normalization factor of a raw reading relative to a normalized
(V-form) reading. -/
def normalizationFactor (raw normalized : ℝ) : ℝ :=
  raw - normalized

/-- **Generic tool (pointwise channel).**  A raw reading is its normalized
V-form plus the exact normalization factor. -/
theorem raw_eq_normalized_add_factor (raw normalized : ℝ) :
    raw = normalized + normalizationFactor raw normalized := by
  unfold normalizationFactor
  ring

/-- **Generic tool (pointwise vanishing criterion).**  The raw reading equals
the normalized one iff the exact normalization factor vanishes. -/
theorem raw_eq_normalized_iff_factor_zero (raw normalized : ℝ) :
    raw = normalized ↔ normalizationFactor raw normalized = 0 := by
  unfold normalizationFactor
  constructor <;> intro h <;> linarith

/-- **Generic tool (weighted regional channel).**  If every place satisfies the
pointwise normalization decomposition, then any finite weighted regional reading
satisfies the same decomposition with the weighted normalization factor. -/
theorem weighted_raw_eq_weighted_normalized_add_factor
    {ι : Type u} [Fintype ι] (w raw normalized factor : ι → ℝ)
    (h : ∀ b, raw b = normalized b + factor b) :
    (∑ b : ι, w b * raw b) =
      (∑ b : ι, w b * normalized b) + ∑ b : ι, w b * factor b := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun b _ => by rw [h b]; ring)

/-- **Generic tool (weighted vanishing criterion).**  If the weighted
normalization factor vanishes (e.g. every per-place factor is zero), the weighted
raw reading equals the weighted normalized reading. -/
theorem weighted_raw_eq_weighted_normalized_of_factor_zero
    {ι : Type u} [Fintype ι] (w raw normalized factor : ι → ℝ)
    (h : ∀ b, raw b = normalized b + factor b)
    (hzero : (∑ b : ι, w b * factor b) = 0) :
    (∑ b : ι, w b * raw b) = ∑ b : ι, w b * normalized b := by
  rw [weighted_raw_eq_weighted_normalized_add_factor w raw normalized factor h, hzero,
    add_zero]

/-- Pointwise corollary: if every place has zero exact normalization factor, the
weighted raw reading equals the weighted normalized reading. -/
theorem weighted_raw_eq_weighted_normalized_of_pointwise_zero
    {ι : Type u} [Fintype ι] (w raw normalized : ι → ℝ)
    (h : ∀ b, raw b = normalized b + normalizationFactor (raw b) (normalized b))
    (hzero : ∀ b, normalizationFactor (raw b) (normalized b) = 0) :
    (∑ b : ι, w b * raw b) = ∑ b : ι, w b * normalized b := by
  refine weighted_raw_eq_weighted_normalized_of_factor_zero w raw normalized
    (fun b => normalizationFactor (raw b) (normalized b)) h ?_
  exact Finset.sum_eq_zero (fun b _ => by rw [hzero b, mul_zero])

#check normalizationFactor
#check raw_eq_normalized_add_factor
#check raw_eq_normalized_iff_factor_zero
#check weighted_raw_eq_weighted_normalized_add_factor
#check weighted_raw_eq_weighted_normalized_of_factor_zero
#check weighted_raw_eq_weighted_normalized_of_pointwise_zero

end LeanFormal.IUT.XiFPaper.S3140NormalizationChannelToolActual
