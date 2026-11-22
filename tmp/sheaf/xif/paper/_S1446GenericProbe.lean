import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport
import LeanFormal.IUT.Foundations.LocalFields.NormalizedHaarTransport
import Mathlib.MeasureTheory.Measure.Map

noncomputable section
open scoped BigOperators TensorProduct Topology Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1446ReportCReadoutActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.NormalizedHaarTransport
open MeasureTheory Topology

/-! ## 1. The normalized readout and the explicit isomorphism branch -/

/-- The normalized readout of a region `S` relative to a reference region `C`:
the log of the `S`-mass minus the log of the `C`-mass.  The common Haar
normalization cancels in the difference; this is the unit-relative log-volume
that the source comparison uses. -/
def s1446RelativeReadout {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (S C : Set X) : ℝ :=
  Real.log (μ S).toReal - Real.log (μ C).toReal

/-- Route C, first admissible branch: an actual topological additive group
isomorphism `e`, with the source region and the reference region transported by
the *same* `e`.  The reference image in the target is `e '' C`; the readout is
invariant.  This is exactly the hypothesis under which
`NormalizedHaarTransport` applies. -/
theorem s1446RelativeReadout_image_eq
    {G H : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [AddGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    [MeasurableSpace H] [BorelSpace H] [LocallyCompactSpace H]
    (e : G ≃ₜ+ H) (μ : Measure G) (ν : Measure H)
    [Measure.IsAddHaarMeasure μ] [Measure.IsAddHaarMeasure ν]
    {S C : Set G} (hS : IsCompact (closure S)) (hC : IsCompact (closure C))
    (hSpos : 0 < μ S) (hCpos : 0 < μ C) :
    s1446RelativeReadout ν (e '' S) (e '' C) =
      s1446RelativeReadout μ S C := by
  simpa only [s1446RelativeReadout] using
    NormalizedHaarTransport.relative_log_mass_image_eq e μ ν hS hC hSpos hCpos

/-- The explicit datum of route C's isomorphism branch.  Both the source region
and the reference region live in the source group and are transported together;
the target reference region is not an independently chosen ambient set. -/
structure S1446ReferenceIsomorphism
    (G H : Type*) [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [AddGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    [MeasurableSpace H] [BorelSpace H] [LocallyCompactSpace H]
    (μ : Measure G) (ν : Measure H)
    [Measure.IsAddHaarMeasure μ] [Measure.IsAddHaarMeasure ν] where
  /-- The actual topological additive group isomorphism. -/
  e : G ≃ₜ+ H
  /-- The source region, in the source group. -/
  sourceRegion : Set G
  /-- The reference region, in the same source group. -/
  referenceRegion : Set G
  source_compact : IsCompact (closure sourceRegion)
  reference_compact : IsCompact (closure referenceRegion)
  source_pos : 0 < μ sourceRegion
  reference_pos : 0 < μ referenceRegion

/-- The readout identity supplied by an explicit `S1446ReferenceIsomorphism`.
The target reference region is `e '' referenceRegion` by construction. -/
theorem s1446ReferenceIsomorphism_readout
    {G H : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [AddGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    [MeasurableSpace H] [BorelSpace H] [LocallyCompactSpace H]
    {μ : Measure G} {ν : Measure H}
    [Measure.IsAddHaarMeasure μ] [Measure.IsAddHaarMeasure ν]
    (D : S1446ReferenceIsomorphism G H μ ν) :
    s1446RelativeReadout ν (D.e '' D.sourceRegion) (D.e '' D.referenceRegion) =
      s1446RelativeReadout μ D.sourceRegion D.referenceRegion :=
  s1446RelativeReadout_image_eq D.e μ ν D.source_compact D.reference_compact
    D.source_pos D.reference_pos

/-! ## 2. The intrinsic-image-measure branch -/

/-- The measure intrinsic to the image of `e`: the pushforward of the source
Haar.  This is the target measure in route C's second branch.  It is a
definition, not an assertion of equality with any ambient Haar. -/
def s1446IntrinsicImageMeasure {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (e : α → β) : Measure β :=
  Measure.map e μ

/-- On the image of a measurable set, the intrinsic image measure returns the
source mass.  This is the exact content of the S1085/S1086 pushforward step. -/
theorem s1446IntrinsicImageMeasure_image
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {e : α → β}
    (hmeas : Measurable e) (hinj : Function.Injective e)
    {S : Set α} (hS : MeasurableSet (e '' S)) :
    s1446IntrinsicImageMeasure μ e (e '' S) = μ S := by
  unfold s1446IntrinsicImageMeasure
  rw [Measure.map_apply hmeas hS, Set.preimage_image_eq _ hinj]

/-- If the target measure is the intrinsic image measure, the relative readout
of the transported source and reference regions is exactly the source readout.
No compactness, positivity or ambient equality is needed: the pushforward is a
definitional transport of the source mass. -/
theorem s1446RelativeReadout_intrinsicImage_eq
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {e : α → β}
    (hmeas : Measurable e) (hinj : Function.Injective e)
    {S C : Set α} (hS : MeasurableSet (e '' S)) (hC : MeasurableSet (e '' C)) :
    s1446RelativeReadout (s1446IntrinsicImageMeasure μ e) (e '' S) (e '' C) =
      s1446RelativeReadout μ S C := by
  unfold s1446RelativeReadout
  rw [s1446IntrinsicImageMeasure_image μ hmeas hinj hS,
    s1446IntrinsicImageMeasure_image μ hmeas hinj hC]

/-! ## 3. Completion degree transport of the local point readout -/

section CompletionDegree

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
variable (place : NumberField.FinitePlace K)

/-- The signed degree-normalized log norm of a lower completion element. -/
def s1446LowerDegreeNormalizedSignedLog
    (x : (comap (k := k) place).maximalIdeal.adicCompletion k) : ℝ :=
  -(Real.log ‖x‖ / (Module.finrank ℚ k : ℝ))

/-- The signed degree-normalized log norm of an upper completion element. -/
def s1446UpperDegreeNormalizedSignedLog
    (x : place.maximalIdeal.adicCompletion K) : ℝ :=
  -(Real.log ‖x‖ / (Module.finrank ℚ K : ℝ))

/-- Completion degree transport: the absolute-degree-normalized signed log of
the completion image is `e * f / [K : k]` times the lower readout.  This is the
local normalization used when the source q parameter is moved to the upper
completion; the element itself is transported by `completionMap`, not raised to
a power. -/
theorem s1446CompletionDegreeReadoutTransport
    (x : (comap (k := k) place).maximalIdeal.adicCompletion k) (hx : x ≠ 0) :
    s1446UpperDegreeNormalizedSignedLog (K := K) place
        (completionMap (k := k) place x) =
      ((relativeCompletionDegree (k := k) place : ℝ) /
        (Module.finrank k K : ℝ)) *
        s1446LowerDegreeNormalizedSignedLog (k := k) place x := by
  unfold s1446UpperDegreeNormalizedSignedLog s1446LowerDegreeNormalizedSignedLog
  rw [absoluteDegreeNormalizedLogNorm_completionMap (k := k) place x hx]
  ring

/-- The invariant form: after dividing by the relative degree factor, the
degree-normalized signed log readout is exactly the source readout. -/
theorem s1446CompletionDegreeReadoutInvariant
    (x : (comap (k := k) place).maximalIdeal.adicCompletion k) (hx : x ≠ 0) :
    s1446UpperDegreeNormalizedSignedLog (K := K) place
        (completionMap (k := k) place x) /
      ((relativeCompletionDegree (k := k) place : ℝ) /
        (Module.finrank k K : ℝ)) =
      s1446LowerDegreeNormalizedSignedLog (k := k) place x := by
  rw [s1446CompletionDegreeReadoutTransport (k := k) (K := K) place x hx]
  have hdeg : (relativeCompletionDegree (k := k) place : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (relativeCompletionDegree_pos (k := k) place).ne'
  have hfin : (Module.finrank k K : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Module.finrank_pos (R := k) (M := K)).ne'
  have hratio : ((relativeCompletionDegree (k := k) place : ℝ) /
      (Module.finrank k K : ℝ)) ≠ 0 := div_ne_zero hdeg hfin
  exact mul_div_cancel_left₀ _ hratio

end CompletionDegree

end LeanFormal.IUT.XiFPaper.S1446ReportCReadoutActual
