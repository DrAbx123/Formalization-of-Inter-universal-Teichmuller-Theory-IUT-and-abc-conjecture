/-
# S1446: route C normalized readout for the xi-f comparison

This file implements route C of the 2026-10-30 gap report
(`coord/reports/gap-exploration-20261030.md`): transport the normalized readout
prescribed by the source, using the three actual donors named there.

* `NormalizedHaarTransport`: if an actual topological additive group
  isomorphism `e : G ≃ₜ+ H` transports the source region `S` *and* the
  reference region `C` together, then the relative log-mass readout is
  invariant.  This is the first admissible branch.  The reference image is
  explicitly `e '' C`; no ambient Haar equality is involved.
* completion degree transport (`FinitePlaceCompletionNormTransport`): the
  absolute-degree-normalized signed log norm of a completion image is
  `e * f / [K : k]` times the lower readout; after dividing by that degree
  factor the point readout is invariant.  This is the local q-readout
  normalization used when a source parameter is moved to an upper completion.
* S1086 pushforward: if the source uses the measure intrinsic to the image,
  the target measure is the pushforward `Measure.map e mu`; on images of
  measurable sets it returns the source mass.  This is the second admissible
  branch, and it is the branch that applies to the actual root-stack
  embedding, whose range is a proper L-stalk inside the ambient extension.

The file deliberately does **not** prove `ambient Haar = pushforward`.  The
proposition `S1446AmbientHaarEq` is recorded only as an independent statement;
it is not a hypothesis of any readout theorem.  If the ambient Haar of the
embedding range vanishes while the intrinsic hull readout is positive, the two
measures are provably different; `s1446Ambient_ne_pushforward_of_zero_range`
records exactly that conditional obstruction.

The xi-f application specializes the intrinsic branch to
`rootStackEmbedding : qVFamTensorBlock T b -> rootStackExtension T b` and to
the actual regions `qPilotQ1URegion ⊆ paperLambdaORegion`.  The reference
region in the root-stack extension is *definitionally* the image of the
lambda-O region; the relative readout on the image equals the source readout in
the qVFam block, and S1086's pushforward inequality gives the per-b readout
comparison.  The ambient root-stack Haar is not used.

-/

import tmp.sheaf.xif.paper.S1086PerBQ1URootHullActual
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
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.QVFamPureFractionalScalingDataGapActual
open LeanFormal.IUT.XiFPaper.S1072CanonicalQ1URegionActual
open LeanFormal.IUT.XiFPaper.S1073RootStackPaperThetaHullActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S1085PushforwardHullEqActual
open LeanFormal.IUT.XiFPaper.S1080PushforwardConstructionActual
open LeanFormal.IUT.XiFPaper.S1079RootStackMeasureAuditActual
open LeanFormal.IUT.XiFPaper.S1095PushforwardHullEqActual
open LeanFormal.IUT.XiFPaper.S1102PushforwardHullPositivityActual
open LeanFormal.IUT.XiFPaper.S1086PerBQ1URootHullActual
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
  exact s1085Map_image_of_injective μ hmeas hinj hS

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

/-! ## 4. The actual xi-f readout pair -/

section XiF

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- The source-side reference readout: the log mass of the lambda-O region in
the qVFam block, computed with the block Haar.  This is the domain shadow of the
root-stack hull. -/
noncomputable def s1446XiFReferenceLog : Real :=
  Real.log ((Measure.addHaar : Measure (qVFamTensorBlock T b))
    (paperLambdaORegion (l := l) T b
      (paperRootCoefficientFamily (l := l) T b))).toReal

/-- Explicit identification of the reference region in the root-stack
extension: the hull is, by definition, the image of the lambda-O region under
the actual embedding. -/
theorem s1446XiFReferenceRegion_eq_image :
    rootStackPaperThetaHull (l := l) T b =
      rootStackEmbedding (l := l) T b ''
        paperLambdaORegion (l := l) T b
          (paperRootCoefficientFamily (l := l) T b) := by
  unfold rootStackPaperThetaHull
  rfl

/-- The source branch declaration for the actual root-stack comparison: the
measure on the image is the intrinsic image measure of the qVFam block Haar,
i.e. the S1080/S1086 pushforward.  This is a definitional identity, not an
ambient Haar equality. -/
theorem s1446XiFSourceUsesIntrinsicImageMeasure :
    rootStackPaperThetaHullLogPushforward (l := l) T b =
      Real.log ((s1446IntrinsicImageMeasure
        (Measure.addHaar : Measure (qVFamTensorBlock T b))
        (rootStackEmbedding (l := l) T b))
          (rootStackPaperThetaHull (l := l) T b)).toReal := by
  unfold rootStackPaperThetaHullLogPushforward s1446IntrinsicImageMeasure
    s1080PushforwardHaar s1079HaarOnRange
  rfl

/-- The intrinsic hull readout equals the source-side reference readout, from
the S1086/S1095 pushforward identity.  This is the step that proves that the
source-faithful reading on the image is exactly the reading of the reference
region in the qVFam block. -/
theorem s1446XiFHullIntrinsicLog_eq_referenceLog
    (h : S1095ExactMinimum (l := l) T b) :
    rootStackPaperThetaHullLogPushforward (l := l) T b =
      s1446XiFReferenceLog (l := l) T b := by
  unfold rootStackPaperThetaHullLogPushforward s1446XiFReferenceLog
  rw [s1095HullMeasure_eq_domainHaar (l := l) T b h]

/-- The relative readout is transported from the qVFam source block to the
root-stack image together with *both* regions: the q[1u] source region and the
lambda-O reference region.  The first set is the image of `qPilotQ1URegion`; the
second is the hull, definitionally the image of the reference region. -/
theorem s1446XiFRelativeReadout_image
    (hinj : S1085EmbeddingInjective (l := l) T b)
    (h : S1095ExactMinimum (l := l) T b)
    (hS : S1086Q1URegionMeasurable (l := l) T b) :
    s1446RelativeReadout (s1080PushforwardHaar (l := l) T b)
        (rootStackEmbedding (l := l) T b '' qPilotQ1URegion (l := l) T b)
        (rootStackPaperThetaHull (l := l) T b) =
      s1446RelativeReadout (Measure.addHaar : Measure (qVFamTensorBlock T b))
        (qPilotQ1URegion (l := l) T b)
        (paperLambdaORegion (l := l) T b
          (paperRootCoefficientFamily (l := l) T b)) := by
  unfold s1446RelativeReadout
  have hq := s1086Q1UPushforward (l := l) T b hinj h.1 hS
  have hc := s1095HullMeasure_eq_domainHaar (l := l) T b h
  rw [hq, hc]

/-- The actual per-b readout pair: the S1086 pushforward inequality together
with the identification of its right-hand readout with the source-side
reference readout.  No ambient Haar equality is used. -/
theorem s1446XiFReadout_pair
    (hcont : S1086Q1UImageContainment (l := l) T b)
    (h : S1095ExactMinimum (l := l) T b)
    (hS : S1086Q1URegionMeasurable (l := l) T b)
    (hQ1UPos : 0 < (Measure.addHaar : Measure (qVFamTensorBlock T b))
      (qPilotQ1URegion (l := l) T b))
    (hQ1UFin : (Measure.addHaar : Measure (qVFamTensorBlock T b))
      (qPilotQ1URegion (l := l) T b) < ⊤) :
    qPilotQ1ULogHaar (l := l) T b ≤
        rootStackPaperThetaHullLogPushforward (l := l) T b ∧
      rootStackPaperThetaHullLogPushforward (l := l) T b =
        s1446XiFReferenceLog (l := l) T b := by
  refine ⟨?_, s1446XiFHullIntrinsicLog_eq_referenceLog (l := l) T b h⟩
  exact s1086PerB_pushforward_of_measurable (l := l) T b hcont
    (show S1102MeasurabilityInput (l := l) T b from h) hS hQ1UPos hQ1UFin

/-- Relative form of the readout comparison: the normalized q[1u] readout
against the lambda-O reference region is nonpositive.  This is the same
inequality written in the normalized-readout language of route C. -/
theorem s1446XiFRelativeReadout_nonpos
    (hcont : S1086Q1UImageContainment (l := l) T b)
    (h : S1095ExactMinimum (l := l) T b)
    (hS : S1086Q1URegionMeasurable (l := l) T b)
    (hQ1UPos : 0 < (Measure.addHaar : Measure (qVFamTensorBlock T b))
      (qPilotQ1URegion (l := l) T b))
    (hQ1UFin : (Measure.addHaar : Measure (qVFamTensorBlock T b))
      (qPilotQ1URegion (l := l) T b) < ⊤) :
    s1446RelativeReadout (Measure.addHaar : Measure (qVFamTensorBlock T b))
      (qPilotQ1URegion (l := l) T b)
      (paperLambdaORegion (l := l) T b
        (paperRootCoefficientFamily (l := l) T b)) ≤ 0 := by
  have hpair := s1446XiFReadout_pair (l := l) T b hcont h hS hQ1UPos hQ1UFin
  have hle : qPilotQ1ULogHaar (l := l) T b ≤ s1446XiFReferenceLog (l := l) T b := by
    rw [← hpair.2]
    exact hpair.1
  unfold qPilotQ1ULogHaar s1446XiFReferenceLog at hle
  exact sub_nonpos.mpr hle

/-! ## 5. The ambient-Haar alternative is not used -/

/-- The ambient-Haar = pushforward equality.  It is recorded as a proposition
only: no route-C theorem above takes it as a hypothesis, and it is not proved
here.  In the actual root-stack situation the embedding range is a proper
L-stalk, so the ambient Haar is generally the wrong measure. -/
def S1446AmbientHaarEq : Prop :=
  s1080PushforwardHaar (l := l) T b = rootStackPaperThetaHaar (l := l) T b

/-- Exact obstruction, conditional form: if the ambient Haar of the embedding
range is zero while the intrinsic hull readout is positive, then the ambient
Haar and the pushforward are different measures.  This is why route C stops
instead of attempting `ambient Haar = pushforward`. -/
theorem s1446Ambient_ne_pushforward_of_zero_range
    (hzero : rootStackPaperThetaHaar (l := l) T b
      (Set.range (rootStackEmbedding (l := l) T b)) = 0)
    (hpos : 0 < s1080PushforwardHaar (l := l) T b
      (rootStackPaperThetaHull (l := l) T b)) :
    rootStackPaperThetaHaar (l := l) T b ≠
      s1080PushforwardHaar (l := l) T b := by
  intro heq
  have hzeroHull : rootStackPaperThetaHaar (l := l) T b
      (rootStackPaperThetaHull (l := l) T b) = 0 :=
    measure_mono_null (s1079Hull_subset_range (l := l) T b) hzero
  rw [heq] at hzeroHull
  exact hpos.ne' hzeroHull

end XiF

end LeanFormal.IUT.XiFPaper.S1446ReportCReadoutActual
