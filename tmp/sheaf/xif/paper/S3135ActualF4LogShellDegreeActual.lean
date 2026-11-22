import tmp.sheaf.xif.paper.S3135F4ActualHullResidualActual

/-!
# Actual source-side log-shell / log-degree computation for the F4 residual

**task-10 deliverable.**  Reduces the F4 residual of
`S3135F4ActualHullResidualActual.S3135ActualF4DegreeResidual` to two concrete source
cards, on the actual value-realized carrier
`W = I.sourceUnitRegionHaarInterface v R n D`:

1. **`S3135ValueGroupDegreeFaithfulness`** — the actual source realization of positive
   reals in the value monoid is degree-faithful:
   `logDegreeAt (posRealAction (ofAdd x)) = x`.  This is the value-group half of the
   log-shell construction of IUT II, Example 1.8, (ix) (iut2.txt:2402-2409:
   `I(G) ⊆ O^×μ(G)` is `p^{-1}` times the image of the `G`-invariants of `O^×(G)`;
   cf. [AbsTopIII], Proposition 5.8, (ii)), and the `q`-normalization of Remark 3.9.4.
   The existing source realization only records faithfulness at the actual
   `q`-parameter (`SourceImageRealization.degree_of_q`); the general value-group
   faithfulness at the point's log-shell exponent is the named card here.
2. **`S3135ScalingNormalization`** — the `(1+eps)`-normalized comparison of the
   scaling log-degree against the height:
   `0 <= (1+eps) * logDegree(scaling) + eps * ht(x)`, equivalently
   `(1+eps) * (-logDegree(scaling)) <= eps * ht(x)`.
   This is the concrete log-shell/volume normalization inequality: the log-volume of
   the `lambda·O` region is normalized against `O` (IUT III Remark 3.9.5, (i); the
   carrier field `scaleShift_unitRegion_logVolume_le`), and its log-degree shadow is
   exactly this inequality.  In paper terms: the scaling contributes at most an
   `eps`-fraction of the height, which is the point of the `(1 + eps)` normalization
   of IUT IV section 1 (Proposition 1.4, Normalized Log-volume Estimates,
   iut4.txt:671-760) and IUT IV:2367-2375.

## Proved here

* the actual point construction `abcSourcePoint a b c` (the constant value-monoid
  point whose log-shell exponent is `ht(x)/card(SourceVolumeIndex l)`), with the
  **actual log-degree computation**
  `sourceLocalLogDegree v (abcSourcePoint a b c) = ht(x) = log c`, i.e. the value
  realization of the normalized height (the log-volume of the arithmetic line bundle
  of the point, [GenEll] Definition 1.5, (iii));
* the exact equivalence
  `S3135ActualF4DegreeResidual eps (abcSourcePoint) <-> S3135ScalingNormalization eps`;
* F4 at the actual carrier (`FrontierHeightComparisonClause`) for the constructed
  point from the two named cards (via `s3135_actualF4_of_degreeResidual`).

The H_C (θ-pilot hull) side is orthogonal to this file: it is the F5/Cor 3.12 side
(hull stream files `S3132HullReadoutForBatchAActual`, `S3129IQHullLogVolumeSourceActual`),
whereas F4 only concerns the arithmetic-line-bundle point and its log-shell degree.
-/

noncomputable section

open scoped BigOperators NNReal ENNReal
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3135F4ActualHullResidualActual

namespace LeanFormal.IUT.XiFPaper.S3135ActualF4LogShellDegreeActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
variable (D : I.SourceUnitRegionHaarData v R n)

/-- The number of source volume indices, as a real. -/
noncomputable def sourceVolumeIndexCard : ℝ :=
  (Fintype.card (SourceVolumeIndex l) : ℝ)

theorem sourceVolumeIndexCard_pos : (0 : ℝ) < sourceVolumeIndexCard (l := l) := by
  unfold sourceVolumeIndexCard
  exact_mod_cast sourceVolumeIndex_card_pos l

theorem sourceVolumeIndexCard_ne_zero : sourceVolumeIndexCard (l := l) ≠ 0 :=
  ne_of_gt (sourceVolumeIndexCard_pos (l := l))

/-- **Named card 1: value-group degree faithfulness.**  The actual realization of the
positive reals in the source value monoid is degree-faithful (IUT II, Example 1.8,
(ix); [AbsTopIII], Proposition 5.8, (ii); Remark 3.9.4).  This is the value-group half
of the log-shell construction; the existing source realization supplies it only at the
actual `q`-parameter (`SourceImageRealization.degree_of_q`). -/
def S3135ValueGroupDegreeFaithfulness : Prop :=
  ∀ x : ℝ, I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd x)) = x

/-- The actual source point of the ABC triple: the constant value-monoid point whose
log-shell exponent is `ht(x) / card(SourceVolumeIndex l)`, so that its total
log-degree over the volume index is the normalized height of `x = a/c`. -/
noncomputable def abcSourcePoint (a b c : ℕ) : I.ThetaPilotPoint v :=
  I.constantThetaPilotPoint v R
    (Multiplicative.ofAdd
      (Height.logHeight₁ (abcRationalPoint a c) / sourceVolumeIndexCard (l := l)))

/-- **The actual source-side log-degree computation** (task-10 item 2): the total
log-degree of the constructed point is the height `ht_{omega(D)}(x)`
([GenEll] Definition 1.5, (iii); IUT IV:2367-2375), given the value-group
degree-faithfulness card. -/
theorem sourceLocalLogDegree_abcSourcePoint (hdeg : S3135ValueGroupDegreeFaithfulness I v R)
    (a b c : ℕ) :
    I.sourceLocalLogDegree v (abcSourcePoint I v R a b c) =
      Height.logHeight₁ (abcRationalPoint a c) := by
  unfold abcSourcePoint
  rw [I.sourceLocalLogDegree_constant v R _ hdeg]
  unfold sourceVolumeIndexCard
  have hcN : (Fintype.card (SourceVolumeIndex l) : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (sourceVolumeIndex_card_pos l)
  field_simp

/-- On an ABC triple the computed log-degree is `Real.log c` (the canonical height via
`RationalPointDictionary.abcRationalPoint_logHeight₁`). -/
theorem sourceLocalLogDegree_abcSourcePoint_eq_log (hdeg : S3135ValueGroupDegreeFaithfulness I v R)
    {a b c : ℕ} (habc : IsABCTriple a b c) :
    I.sourceLocalLogDegree v (abcSourcePoint I v R a b c) = Real.log (c : ℝ) := by
  rw [sourceLocalLogDegree_abcSourcePoint I v R hdeg]
  exact abcRationalPoint_logHeight₁ habc

/-- The log-degree of the scaled source point: the scaling contributes additively. -/
theorem sourceLocalLogDegree_scaled_abcSourcePoint
    (hdeg : S3135ValueGroupDegreeFaithfulness I v R) (a b c : ℕ) :
    I.sourceLocalLogDegree v (D.scaling * abcSourcePoint I v R a b c) =
      I.sourceLocalLogDegree v D.scaling +
        Height.logHeight₁ (abcRationalPoint a c) := by
  rw [I.sourceLocalLogDegree_mul, sourceLocalLogDegree_abcSourcePoint I v R hdeg]

/-- **Named card 2: the concrete normalized log-shell/scaling inequality.**  The
scaling's log-degree contraction is bounded by an `eps`-fraction of the height:
`0 <= (1+eps) * logDegree(scaling) + eps * ht(x)`.  This is the log-degree shadow of
the log-volume normalization of the `lambda·O` region (IUT III Remark 3.9.5, (i);
carrier field `scaleShift_unitRegion_logVolume_le`) against the normalized log-volume
estimate (IUT IV section 1, Proposition 1.4, iut4.txt:671-760). -/
def S3135ScalingNormalization (eps : ℝ) : Prop :=
  ∀ a b c : ℕ, IsABCTriple a b c →
    0 ≤ (1 + eps) * I.sourceLocalLogDegree v D.scaling +
      eps * Height.logHeight₁ (abcRationalPoint a c)

/-- The same card in purely multiplicative form, the concrete inequality reported as
the reduced residual: `(1+eps) * (-logDegree(scaling)) <= eps * ht(x)`. -/
theorem s3135_scalingNormalization_iff_mul_form (eps : ℝ) :
    S3135ScalingNormalization I v R n D eps ↔
      ∀ a b c : ℕ, IsABCTriple a b c →
        (1 + eps) * (-I.sourceLocalLogDegree v D.scaling) ≤
          eps * Height.logHeight₁ (abcRationalPoint a c) := by
  constructor
  · intro h a b c habc
    have h' := h a b c habc
    linarith
  · intro h a b c habc
    have h' := h a b c habc
    linarith

/-- **The residual reduces exactly to the normalized scaling inequality.**  For the
constructed source point, the F4 degree/height residual is equivalent to the concrete
log-shell normalization inequality (given value-group degree faithfulness).  No
content is hidden: the equivalence is proved in both directions. -/
theorem s3135_degreeResidual_abcSourcePoint_iff (hdeg : S3135ValueGroupDegreeFaithfulness I v R)
    (eps : ℝ) :
    S3135ActualF4DegreeResidual I v R n D (abcSourcePoint I v R) eps ↔
      S3135ScalingNormalization I v R n D eps := by
  constructor
  · intro h a b c habc
    have h' := h a b c habc
    rw [sourceLocalLogDegree_scaled_abcSourcePoint I v R n D hdeg] at h'
    linarith
  · intro h a b c habc
    have h' := h a b c habc
    rw [sourceLocalLogDegree_scaled_abcSourcePoint I v R n D hdeg]
    linarith

/-- **F4 at the actual carrier with the constructed source point.**  From the two named
cards (value-group degree faithfulness + the normalized scaling inequality for every
`eps > 0`), the height comparison clause holds at the actual value-realized carrier
for the constructed arithmetic-line-bundle point. -/
theorem s3135_actualF4_withSourcePoint
    (hdeg : S3135ValueGroupDegreeFaithfulness I v R)
    (hnorm : ∀ eps : ℝ, 0 < eps → S3135ScalingNormalization I v R n D eps) :
    FrontierHeightComparisonClause (sourceActualCarrier I v R n D)
      (fun _ _ a b c => abcSourcePoint I v R a b c) :=
  s3135_actualF4_of_degreeResidual I v R n D (abcSourcePoint I v R)
    (fun eps heps =>
      (s3135_degreeResidual_abcSourcePoint_iff I v R n D hdeg eps).mpr (hnorm eps heps))

#check S3135ValueGroupDegreeFaithfulness
#check S3135ScalingNormalization
#check sourceLocalLogDegree_abcSourcePoint
#check s3135_degreeResidual_abcSourcePoint_iff
#check s3135_actualF4_withSourcePoint

end LeanFormal.IUT.XiFPaper.S3135ActualF4LogShellDegreeActual
end
