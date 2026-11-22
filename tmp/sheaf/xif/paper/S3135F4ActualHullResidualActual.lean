import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontier
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapSupplyLayer

/-!
# F4 at the actual value-realized carrier: exact residual

**This file attacks the real F4 target** (Lead review 2026-11-10): the
`IQHullLogVolumeInterface` carrier realized from the actual source value-monoid data
(`IQCarrierHaarData.lean:159-203`,
`W = I.sourceUnitRegionHaarInterface v R n D`), whose log-volume is the actual
supremum of value-monoid log-degrees (`SourceImageHullVolume.lean:103-195`:
`sourcePointVolume = ofReal (sourceLocalLogDegree)`, `sourceSetVolume = sup`), not a
diagonal definition.  The point datum `p a b c` is the (named) image point of
`x = a/c`; the comparison region is
`scaleShift '' (unitRegion ∪ {p a b c})` (Remark 3.9.5, (i)).

## The exact residual

F4 (IUT IV:2367-2375 and section 2 Theorem A, IUT IV:93-112) asks
`ht_{omega(D)}(x) <= (1 + eps) * (actual region log-volume)`.
The region log-volume is the sup of point volumes, so it is at least the singleton
point volume of the scaled point `lambda * p a b c`; hence F4 follows from the
**positive degree/height dictionary**

`Height.logHeight₁ (abcRationalPoint a c) <=
   (1 + eps) * I.sourceLocalLogDegree v (D.scaling * p a b c)`

(`S3135ActualF4DegreeResidual`).  This is the *lower-bound* direction of the point
dictionary, the opposite of the point-height dictionary `degree <= logHeight₁`
that is consumed as `(d)` in `Cor312CarrierRealizationSpec.lean:58-85`; that upper
direction is refuted at `(1, 2, 3)` there (`log 6 > log 3`), so F4 cannot be routed
through it.  The positive direction is exactly the paper's arithmetic-line-bundle
log-volume computation: the log-volume of the (line bundle of the) point is the
normalized height plus `O(log ht)`, absorbed by `(1 + eps)` for every `eps > 0`
([GenEll] Definition 1.5(iii), (iv); IUT IV:2367-2375).

## What is proved here

* `s3135_actualF4_of_degreeResidual`: F4 at the actual carrier from the named
  positive degree/height residual (with region finiteness, which is proved from the
  `SourceUnitRegionHaarData` fields, not assumed);
* `s3135_actualF4_iff_singletonPoint`: the residual is exactly the singleton
  point-volume against height card (its `toReal` form), so no content is hidden;
* `s3135_actualF4_not_by_hullContainment`: the hull-containment route to F4 is
  impossible (heights are unbounded, the hull log-volume is finite), so F4 must use
  the point/scale-shift part of the region — this rules out the vacuous route;
* the region-volume finiteness bound `sourceActual_regionVolume_lt_top` and the
  singleton-volume computation `sourceActual_singletonVolume_eq`.

The residual `S3135ActualF4DegreeResidual` is **not proved**: it is the exact
source-side input (normalized log-shell/degree lower bound for the point of
`x = a/c`) and is reported as the remaining F4 math with the page/line references
above.
-/

noncomputable section

open scoped BigOperators NNReal ENNReal
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

namespace LeanFormal.IUT.XiFPaper.S3135F4ActualHullResidualActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
variable (D : I.SourceUnitRegionHaarData v R n)
variable (p : ℕ → ℕ → ℕ → I.ThetaPilotPoint v)

/-- The actual carrier of the comparison: the value-realized
`IQHullLogVolumeInterface` from the source unit-region/Haar data. -/
abbrev sourceActualCarrier : IQHullLogVolumeInterface (I.ThetaPilotPoint v) :=
  I.sourceUnitRegionHaarInterface v R n D

/-- **The exact residual of F4 at the actual carrier (positive degree/height
dictionary).**  The normalized log-degree of the scaled point datum is at least
`(1 + eps)^{-1}` times the height of `x = a/c`.  This is the positive direction of
the point log-volume/height dictionary ([GenEll] Definition 1.5, (iii), (iv); IUT
IV:2367-2375); it is *not* proved here and is the exact remaining F4 input. -/
def S3135ActualF4DegreeResidual (eps : ℝ) : Prop :=
  ∀ a b c : ℕ, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤
      (1 + eps) * I.sourceLocalLogDegree v (D.scaling * p a b c)

/-- The actual region log-volume dominates the singleton point volume of the scaled
point: the region contains the image of `p a b c`. -/
theorem sourceActual_pointVolume_le_regionVolume (a b c : ℕ) :
    I.sourcePointVolume v (D.scaling * p a b c) ≤
      (sourceActualCarrier I v R n D).logVolume
        (normalizedComparisonRegion (sourceActualCarrier I v R n D) p a b c) := by
  change I.sourcePointVolume v (D.scaling * p a b c) ≤
    I.sourceSetVolume v ((fun x => D.scaling * x) '' (D.unitRegion ∪ {p a b c}))
  unfold sourceSetVolume
  exact le_iSup_of_le (D.scaling * p a b c)
    (le_iSup_of_le ⟨p a b c, Set.mem_union_right _ (Set.mem_singleton _), rfl⟩ le_rfl)

/-- The singleton point volume is the `ofReal` of the actual log-degree
(definitional unfolding of `sourcePointVolume`). -/
theorem sourceActual_pointVolume_eq (a b c : ℕ) :
    I.sourcePointVolume v (D.scaling * p a b c) =
      ENNReal.ofReal (I.sourceLocalLogDegree v (D.scaling * p a b c)) := rfl

/-- The region log-volume is finite: every point of the region is either the scaling
of a unit-region point (log-degree at most `D.degreeBound`) or the scaling of the
named point; the scaling has nonpositive log-degree. -/
theorem sourceActual_regionVolume_lt_top (a b c : ℕ) :
    (sourceActualCarrier I v R n D).logVolume
      (normalizedComparisonRegion (sourceActualCarrier I v R n D) p a b c) < ⊤ := by
  change I.sourceSetVolume v
    ((fun x => D.scaling * x) '' (D.unitRegion ∪ {p a b c})) < ⊤
  have hbound : I.sourceSetVolume v
      ((fun x => D.scaling * x) '' (D.unitRegion ∪ {p a b c})) ≤
      ENNReal.ofReal D.degreeBound + I.sourcePointVolume v (D.scaling * p a b c) := by
    unfold sourceSetVolume
    refine iSup_le fun y => iSup_le fun hy => ?_
    rcases hy with ⟨z, hz, rfl⟩
    rcases hz with hz | hz
    · have hdeg : I.sourceLocalLogDegree v (D.scaling * z) ≤ D.degreeBound := by
        rw [I.sourceLocalLogDegree_mul]
        have h1 : I.sourceLocalLogDegree v D.scaling ≤ 0 := D.scaling_logDegree_nonpos
        have h2 : I.sourceLocalLogDegree v z ≤ D.degreeBound := D.unitRegion_logDegree_le z hz
        linarith
      have hle : I.sourcePointVolume v (D.scaling * z) ≤ ENNReal.ofReal D.degreeBound :=
        ENNReal.ofReal_le_ofReal hdeg
      refine le_trans hle ?_
      have h := add_le_add (le_refl (ENNReal.ofReal D.degreeBound))
        (bot_le : (0 : ENNReal) ≤ I.sourcePointVolume v (D.scaling * p a b c))
      simpa only [bot_eq_zero, add_zero] using h
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      refine le_trans (le_refl (I.sourcePointVolume v (D.scaling * p a b c))) ?_
      have h := add_le_add
        (bot_le : (0 : ENNReal) ≤ ENNReal.ofReal D.degreeBound)
        (le_refl (I.sourcePointVolume v (D.scaling * p a b c)))
      simpa only [bot_eq_zero, zero_add] using h
  exact lt_of_le_of_lt hbound
    (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩)

/-- **F4 at the actual carrier from the exact residual.**  The (1+eps)-normalized
height comparison `FrontierHeightComparisonClause` holds at the actual value-realized
carrier, provided the positive degree/height residual.  Region finiteness is proved,
not assumed: the `(1+eps)` factor is absorbed through the actual log-volume lower
bound. -/
theorem s3135_actualF4_of_degreeResidual
    (hres : ∀ eps : ℝ, 0 < eps → S3135ActualF4DegreeResidual I v R n D p eps) :
    FrontierHeightComparisonClause (sourceActualCarrier I v R n D)
      (fun _ _ a b c => p a b c) := by
  intro eps heps a b c habc
  change Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + eps) *
    ((sourceActualCarrier I v R n D).logVolume
      (normalizedComparisonRegion (sourceActualCarrier I v R n D) p a b c)).toReal
  have hres' := hres eps heps a b c habc
  have hvol := sourceActual_pointVolume_le_regionVolume I v R n D p a b c
  have hfin := sourceActual_regionVolume_lt_top I v R n D p a b c
  have htoReal := ENNReal.toReal_mono (ne_of_lt hfin) hvol
  have hdeg_nonneg : 0 ≤ I.sourceLocalLogDegree v (D.scaling * p a b c) := by
    have hnn : 0 ≤ Height.logHeight₁ (abcRationalPoint a c) := Height.zero_le_logHeight₁ _
    by_contra hneg
    push_neg at hneg
    have hcoef_pos : (0 : ℝ) < 1 + eps := by linarith
    have hlt := mul_neg_of_pos_of_neg hcoef_pos hneg
    linarith
  have hsrc := sourceActual_pointVolume_eq I v R n D p a b c
  rw [hsrc, ENNReal.toReal_ofReal hdeg_nonneg] at htoReal
  have hcoef : 0 ≤ 1 + eps := by linarith
  have hmul := mul_le_mul_of_nonneg_left htoReal hcoef
  linarith

/-- The singleton log-volume of the scaled point is the `ofReal` of its actual
log-degree. -/
theorem sourceActual_singletonVolume_eq (a b c : ℕ) :
    (sourceActualCarrier I v R n D).logVolume
        {(sourceActualCarrier I v R n D).scaleShift (p a b c)} =
      ENNReal.ofReal (I.sourceLocalLogDegree v (D.scaling * p a b c)) := by
  change I.sourceSetVolume v {(fun x => D.scaling * x) (p a b c)} = _
  rw [I.cor312GapSupply_sourceSetVolume_singleton v]
  rfl

/-- **The residual is exactly the singleton point-volume/height card.**  Under the
nonnegative degree regime forced by the residual, the residual is equivalent to the
`toReal` form `ht(x) <= (1 + eps) * (volume {scaleShift point}).toReal`; nothing is
hidden in the region decomposition. -/
theorem s3135_actualF4_iff_singletonPoint (eps : ℝ) (heps : 0 < eps)
    (hheight_pos : ∀ a b c : ℕ, IsABCTriple a b c →
      0 < Height.logHeight₁ (abcRationalPoint a c)) :
    S3135ActualF4DegreeResidual I v R n D p eps ↔
      ∀ a b c : ℕ, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + eps) * ((sourceActualCarrier I v R n D).logVolume
            {(sourceActualCarrier I v R n D).scaleShift (p a b c)}).toReal := by
  constructor
  · intro h a b c habc
    have h' := h a b c habc
    have hdeg_nonneg : 0 ≤ I.sourceLocalLogDegree v (D.scaling * p a b c) := by
      have hnn : 0 ≤ Height.logHeight₁ (abcRationalPoint a c) := Height.zero_le_logHeight₁ _
      by_contra hneg
      push_neg at hneg
      have hcoef_pos : (0 : ℝ) < 1 + eps := by linarith
      have hlt := mul_neg_of_pos_of_neg hcoef_pos hneg
      linarith
    rw [sourceActual_singletonVolume_eq I v R n D p a b c,
      ENNReal.toReal_ofReal hdeg_nonneg]
    exact h'
  · intro h a b c habc
    have h' := h a b c habc
    rcases le_total 0 (I.sourceLocalLogDegree v (D.scaling * p a b c)) with hd | hd
    · rw [sourceActual_singletonVolume_eq I v R n D p a b c,
        ENNReal.toReal_ofReal hd] at h'
      exact h'
    · rw [sourceActual_singletonVolume_eq I v R n D p a b c,
        ENNReal.ofReal_of_nonpos hd, ENNReal.toReal_zero,
        mul_zero] at h'
      exact absurd h' (not_le.mpr (hheight_pos a b c habc))

/-- **The hull-containment route to F4 is impossible.**  At the actual carrier, the
hull log-volume is finite (`hull_logVolume_lt_top`) and the heights of ABC rational
points are unbounded; hence no comparison region contained in the hull can dominate
the height.  F4 must use the point/scale-shift part of the region (the arithmetic
line bundle), not the finite θ-pilot hull. -/
theorem s3135_actualF4_not_by_hullContainment
    (hsub : ∀ a b c : ℕ, IsABCTriple a b c →
      normalizedComparisonRegion (sourceActualCarrier I v R n D) p a b c ⊆
        (sourceActualCarrier I v R n D).hull) :
    ¬ (∀ a b c : ℕ, IsABCTriple a b c →
        ENNReal.ofReal (Height.logHeight₁ (abcRationalPoint a c)) ≤
          (sourceActualCarrier I v R n D).logVolume
            (normalizedComparisonRegion (sourceActualCarrier I v R n D) p a b c)) :=
  no_heightDictionary_into_finiteHull (sourceActualCarrier I v R n D)
    (sourceActualCarrier I v R n D).hull_logVolume_lt_top
    (normalizedComparisonRegion (sourceActualCarrier I v R n D) p) hsub

#check S3135ActualF4DegreeResidual
#check s3135_actualF4_of_degreeResidual
#check s3135_actualF4_iff_singletonPoint
#check s3135_actualF4_not_by_hullContainment

end LeanFormal.IUT.XiFPaper.S3135F4ActualHullResidualActual
end
