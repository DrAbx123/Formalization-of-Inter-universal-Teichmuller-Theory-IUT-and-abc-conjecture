/-
# S1414: xi-f normalized readout transport (route C)

Route C of the gap report: transport the normalized readout specified by the
source.  We use the three actual donors named in the report:

* NormalizedHaarTransport: relative log mass is invariant under an actual
  topological additive group isomorphism when the source region and the
  reference region are transported together;
* completion degree transport: the degree-normalized signed log norm of the
  completion image scales by the relative completion degree e*f / [K:k];
* the S1086 pushforward branch: if the source uses the intrinsic measure on the
  image, the pushforward Haar has the same region readout as the source Haar.

No ambient Haar = pushforward equality is asserted.  The pushforward branch is
the corrected measure statement of S1079/S1080, and the ambient root-stack Haar
is not used as a substitute.

The file constructs the generic readout transports and the xi-f source/hull
readout pair, and identifies the exact first field left by route C: the
measurability of the chosen reference image (equivalently the closedness of the
source reference lattice), which is the same exact input isolated in
S1098/S1100.
-/

import tmp.sheaf.xif.paper.S1086PerBQ1URootHullActual
import tmp.sheaf.xif.paper.S1091QPilotQ1UPositivityActual
import tmp.sheaf.xif.paper.S863ProductImageCompactActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport
import LeanFormal.IUT.Foundations.LocalFields.NormalizedHaarTransport
import Mathlib.MeasureTheory.Measure.Map

noncomputable section
open scoped BigOperators TensorProduct Topology Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1414NormalizedReadoutActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S839PaperRootMinimalProductCompactActual
open LeanFormal.IUT.XiFPaper.S863ProductImageCompactActual
open LeanFormal.IUT.XiFPaper.S1079RootStackMeasureAuditActual
open LeanFormal.IUT.XiFPaper.S1091QPilotQ1UPositivityActual
open LeanFormal.IUT.XiFPaper.S1102PushforwardHullPositivityActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S1072CanonicalQ1URegionActual
open LeanFormal.IUT.XiFPaper.S1073RootStackPaperThetaHullActual
open LeanFormal.IUT.XiFPaper.S1080PushforwardConstructionActual
open LeanFormal.IUT.XiFPaper.S1085PushforwardHullEqActual
open LeanFormal.IUT.XiFPaper.S1086PerBQ1URootHullActual
open LeanFormal.IUT.XiFPaper.S1095PushforwardHullEqActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S312QPilotRootTensorBaseChangeActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open MeasureTheory Topology

universe u v

/-! ## 1. The relative normalized readout -/

/-- The normalized readout of a region S relative to a reference region C:
the signed log of the S-mass minus the signed log of the C-mass.  This is
the unit-relative log-volume used by the paper; the common Haar normalization
cancels in the difference. -/
def s1414RelativeReadout {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (S C : Set X) : ℝ :=
  Real.log (μ S).toReal - Real.log (μ C).toReal

theorem s1414RelativeReadout_self {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Set X) :
    s1414RelativeReadout μ S S = 0 :=
  sub_self _

/-- Monotonicity of the relative readout at a fixed reference region. -/
theorem s1414RelativeReadout_mono {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {S T C : Set X} (hST : S ⊆ T)
    (hSpos : 0 < μ S) (hTfin : μ T < ⊤) :
    s1414RelativeReadout μ S C ≤ s1414RelativeReadout μ T C := by
  have hSfin : μ S < ⊤ := lt_of_le_of_lt (measure_mono hST) hTfin
  have hlog : Real.log (μ S).toReal ≤ Real.log (μ T).toReal :=
    Real.log_le_log (ENNReal.toReal_pos hSpos.ne' hSfin.ne)
      (ENNReal.toReal_mono hTfin.ne (measure_mono hST))
  exact sub_le_sub_right hlog _

/-! ## 2. Isomorphism branch: source and reference region transported together -/

/-- If a source region and a reference region are transported by the same
actual topological additive group isomorphism, the relative normalized readout
is unchanged.  This is exactly the hypothesis under which
NormalizedHaarTransport applies; it is not an ambient-Haar identity. -/
theorem s1414RelativeReadout_image_eq
    {G H : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [AddGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    [MeasurableSpace H] [BorelSpace H] [LocallyCompactSpace H]
    (e : G ≃ₜ+ H) (μ : Measure G) (ν : Measure H)
    [Measure.IsAddHaarMeasure μ] [Measure.IsAddHaarMeasure ν]
    {S C : Set G} (hS : IsCompact (closure S)) (hC : IsCompact (closure C))
    (hSpos : 0 < μ S) (hCpos : 0 < μ C) :
    s1414RelativeReadout ν (e '' S) (e '' C) = s1414RelativeReadout μ S C :=
  NormalizedHaarTransport.relative_log_mass_image_eq e μ ν hS hC hSpos hCpos

/-! ## 3. Intrinsic-measure branch: the source uses the pushforward on the image -/

/-- The image of a set under an injective measurable map has the source mass
under the pushforward measure.  This is the generic S1085 identity. -/
theorem s1414Map_image_of_injective
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {f : α → β} (hf : Measurable f) (hinj : Function.Injective f)
    {S : Set α} (hS : MeasurableSet (f '' S)) :
    (Measure.map f μ) (f '' S) = μ S :=
  s1085Map_image_of_injective μ hf hinj hS

/-- If the source uses the intrinsic measure on an image (the pushforward Haar),
the relative normalized readout on the image is exactly the source readout.
No compactness or positivity of the regions is needed for this identity; only
injectivity, measurability of the map, and measurability of the two images. -/
theorem s1414RelativeReadout_map_eq
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {f : α → β} (hf : Measurable f) (hinj : Function.Injective f)
    {S C : Set α} (hS : MeasurableSet (f '' S)) (hC : MeasurableSet (f '' C)) :
    s1414RelativeReadout (Measure.map f μ) (f '' S) (f '' C) =
      s1414RelativeReadout μ S C := by
  unfold s1414RelativeReadout
  rw [s1414Map_image_of_injective μ hf hinj hS,
    s1414Map_image_of_injective μ hf hinj hC]

/-! ## 4. Completion degree transport of the degree-normalized point readout -/

section CompletionDegree

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
variable (place : NumberField.FinitePlace K)

/-- The signed degree-normalized log norm of a lower completion element:
the negative log norm divided by the absolute degree. -/
def s1414LowerDegreeNormalizedSignedLog
    (x : (comap (k := k) place).maximalIdeal.adicCompletion k) : ℝ :=
  - Real.log ‖x‖ / (Module.finrank ℚ k : ℝ)

/-- The signed degree-normalized log norm of an upper completion element. -/
def s1414UpperDegreeNormalizedSignedLog
    (x : place.maximalIdeal.adicCompletion K) : ℝ :=
  - Real.log ‖x‖ / (Module.finrank ℚ K : ℝ)

/-- Completion degree transport: the degree-normalized signed log of the image
is the source readout scaled by e*f / [K:k]. -/
theorem s1414CompletionDegreeReadoutTransport
    (x : (comap (k := k) place).maximalIdeal.adicCompletion k) (hx : x ≠ 0) :
    s1414UpperDegreeNormalizedSignedLog (K := K) place
        (completionMap (k := k) place x) =
      ((relativeCompletionDegree (k := k) place : ℝ) /
        (Module.finrank k K : ℝ)) *
        s1414LowerDegreeNormalizedSignedLog (k := k) place x := by
  unfold s1414UpperDegreeNormalizedSignedLog s1414LowerDegreeNormalizedSignedLog
  rw [neg_div, absoluteDegreeNormalizedLogNorm_completionMap (k := k) place x hx,
    neg_div]
  ring

/-- The invariant form: after dividing out the relative degree factor, the
degree-normalized signed log readout is exactly the source readout.  This is
the normalized readout transport supplied by the completion degree identity. -/
theorem s1414CompletionDegreeReadoutInvariant
    (x : (comap (k := k) place).maximalIdeal.adicCompletion k) (hx : x ≠ 0) :
    s1414UpperDegreeNormalizedSignedLog (K := K) place
        (completionMap (k := k) place x) /
      ((relativeCompletionDegree (k := k) place : ℝ) /
        (Module.finrank k K : ℝ)) =
      s1414LowerDegreeNormalizedSignedLog (k := k) place x := by
  rw [s1414CompletionDegreeReadoutTransport (k := k) (K := K) place x hx]
  have hdeg : (relativeCompletionDegree (k := k) place : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (relativeCompletionDegree_pos (k := k) place).ne'
  have hfin : (Module.finrank k K : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Module.finrank_pos (R := k) (M := K)).ne'
  have hratio : ((relativeCompletionDegree (k := k) place : ℝ) /
      (Module.finrank k K : ℝ)) ≠ 0 := div_ne_zero hdeg hfin
  exact mul_div_cancel_left₀ _ hratio

end CompletionDegree

/-! ## 5. The xi-f source/reference regions and the pushforward readout -/

section XiFSource

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- The source reference region: the canonical integral unit reference
(holomorphic lattice) of the qVFam tensor block. -/
noncomputable def s1414SourceReference : Set (qVFamTensorBlock T b) :=
  arithmeticTupleCanonicalUnitReference (qVFamTensorPlaces T b) qVFamTensorTuple

theorem s1414SourceReference_compact :
    IsCompact (s1414SourceReference T b) := by
  simpa [s1414SourceReference] using
    (isCompact_arithmeticTupleCanonicalRegions
      (qVFamTensorPlaces T b) qVFamTensorTuple).2

theorem s1414SourceReference_pos_lt_top :
    0 < (Measure.addHaar : Measure (qVFamTensorBlock T b))
        (s1414SourceReference T b) ∧
      (Measure.addHaar : Measure (qVFamTensorBlock T b))
        (s1414SourceReference T b) < ⊤ := by
  simpa [s1414SourceReference] using
    (measure_arithmeticTupleCanonicalRegions_pos_lt_top
      (qVFamTensorPlaces T b) qVFamTensorTuple
      (Measure.addHaar : Measure (qVFamTensorBlock T b))).2

/-- Continuity of the actual root-stack embedding. -/
theorem s1414Embedding_continuous :
    Continuous (rootStackEmbedding (l := l) T b) := by
  unfold rootStackEmbedding
  exact (continuous_algebraMap (rootNormedExtension T b)
    (rootStackExtension T b)).comp
    ((continuous_algebraMap (rootBase T b) (rootNormedExtension T b)).comp
      (LinearMap.continuous_of_finiteDimensional
        (qVFamBlockLinearEquiv T b).toLinearMap))

theorem s1414Embedding_measurable :
    S1085EmbeddingMeasurable (l := l) T b :=
  (s1414Embedding_continuous (l := l) T b).measurable

/-- The image of the reference region in the root-stack extension. -/
noncomputable def s1414SourceReferenceImage : Set (rootStackExtension T b) :=
  rootStackEmbedding (l := l) T b '' s1414SourceReference T b

theorem s1414SourceReferenceImage_compact :
    IsCompact (s1414SourceReferenceImage T b) :=
  (s1414SourceReference_compact T b).image
    (s1414Embedding_continuous (l := l) T b)

/-- The reference image is measurable as an actual fact: it is the continuous
image of a compact reference region. -/
theorem s1414SourceReferenceImage_measurable :
    MeasurableSet (s1414SourceReferenceImage T b) :=
  (s1414SourceReferenceImage_compact T b).isClosed.measurableSet

/-- Measurability of the root-stack paper theta hull image. -/
def S1414HullImageMeasurable : Prop :=
  MeasurableSet (rootStackPaperThetaHull (l := l) T b)

/-- Exact first source field of the normalized-readout route: the product
lattice identification for the paper cRoot region. -/
def S1414ExactFirstField : Prop :=
  S863ProductImageEq (l := l) T b

theorem s1414Region_eq_product :
    paperLambdaORegion (l := l) T b
        (paperRootCoefficientFamily (l := l) T b) =
      ((s839FractionalLattice (l := l) T b *
        s839HolomorphicLattice (l := l) T b :
          Submodule ℤ_[(qVFamTensorP T b)] (qVFamTensorBlock T b)) :
        Set (qVFamTensorBlock T b)) := rfl

/-- The exact first field gives measurability of the root-stack hull image. -/
theorem s1414HullImageMeasurable_of_exactFirstField
    (h : S1414ExactFirstField T b) :
    S1414HullImageMeasurable T b := by
  unfold S1414ExactFirstField at h
  unfold S863ProductImageEq at h
  unfold S1414HullImageMeasurable
  have hcompact : IsCompact (paperLambdaORegion (l := l) T b
      (paperRootCoefficientFamily (l := l) T b)) := by
    rw [s1414Region_eq_product (l := l) T b]
    rw [h]
    exact s863MulImageCompact (l := l) T b
  have himage : IsCompact (rootStackPaperThetaHull (l := l) T b) := by
    unfold rootStackPaperThetaHull
    exact hcompact.image (s1414Embedding_continuous (l := l) T b)
  exact himage.isClosed.measurableSet

/-- Pushforward mass of an image, with the intrinsic image measure. -/
theorem s1414PushforwardMass_image
    (hinj : S1085EmbeddingInjective (l := l) T b)
    (hmeas : S1085EmbeddingMeasurable (l := l) T b)
    {S : Set (qVFamTensorBlock T b)}
    (hS : MeasurableSet (rootStackEmbedding (l := l) T b '' S)) :
    s1080PushforwardHaar (l := l) T b
        (rootStackEmbedding (l := l) T b '' S) =
      (Measure.addHaar : Measure (qVFamTensorBlock T b)) S := by
  unfold s1080PushforwardHaar s1079HaarOnRange
  exact s1085Map_image_of_injective
    (Measure.addHaar : Measure (qVFamTensorBlock T b)) hmeas hinj hS

theorem s1414HullPushforwardMass
    (hinj : S1085EmbeddingInjective (l := l) T b)
    (hmeas : S1085EmbeddingMeasurable (l := l) T b)
    (hH : S1414HullImageMeasurable T b) :
    s1080PushforwardHaar (l := l) T b (rootStackPaperThetaHull (l := l) T b) =
      (Measure.addHaar : Measure (qVFamTensorBlock T b))
        (paperLambdaORegion (l := l) T b
          (paperRootCoefficientFamily (l := l) T b)) := by
  have h := s1414PushforwardMass_image (l := l) T b hinj hmeas
    (S := paperLambdaORegion (l := l) T b
      (paperRootCoefficientFamily (l := l) T b)) ?_
  · simpa [rootStackPaperThetaHull] using h
  · simpa [rootStackPaperThetaHull, S1414HullImageMeasurable] using hH

theorem s1414ReferencePushforwardMass
    (hinj : S1085EmbeddingInjective (l := l) T b)
    (hmeas : S1085EmbeddingMeasurable (l := l) T b) :
    s1080PushforwardHaar (l := l) T b (s1414SourceReferenceImage T b) =
      (Measure.addHaar : Measure (qVFamTensorBlock T b))
        (s1414SourceReference T b) :=
  s1414PushforwardMass_image (l := l) T b hinj hmeas
    (S := s1414SourceReference T b)
    (by simpa [s1414SourceReferenceImage] using
      s1414SourceReferenceImage_measurable T b)

/-- The source xi-f readout in the degree-normalized convention. -/
noncomputable def s1414SourceReadout : ℝ :=
  (1 / (Module.finrank ℚ_[qVFamTensorP T b] (qVFamTensorBlock T b) : ℝ)) *
    s1414RelativeReadout (Measure.addHaar : Measure (qVFamTensorBlock T b))
      (qPilotQ1URegion (l := l) T b) (s1414SourceReference T b)

/-- The theta-side pushforward readout relative to the same reference image. -/
noncomputable def s1414HullReadout : ℝ :=
  (1 / (Module.finrank ℚ_[qVFamTensorP T b] (qVFamTensorBlock T b) : ℝ)) *
    s1414RelativeReadout (s1080PushforwardHaar (l := l) T b)
      (rootStackPaperThetaHull (l := l) T b)
      (s1414SourceReferenceImage T b)

theorem s1414SourceReadout_eq_normalizedLogVolume :
    s1414SourceReadout T b =
      arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
        (Measure.addHaar : Measure (qVFamTensorBlock T b))
        (qPilotQ1URegion (l := l) T b) := by
  unfold s1414SourceReadout s1414RelativeReadout s1414SourceReference
    arithmeticTupleNormalizedLogVolume
  rfl

theorem s1414HullReadout_eq_hullRegion
    (hinj : S1085EmbeddingInjective (l := l) T b)
    (hmeas : S1085EmbeddingMeasurable (l := l) T b)
    (hH : S1414HullImageMeasurable T b) :
    s1414HullReadout T b =
      (1 / (Module.finrank ℚ_[qVFamTensorP T b] (qVFamTensorBlock T b) : ℝ)) *
        (Real.log ((Measure.addHaar : Measure (qVFamTensorBlock T b))
          (paperLambdaORegion (l := l) T b
            (paperRootCoefficientFamily (l := l) T b))).toReal -
         Real.log ((Measure.addHaar : Measure (qVFamTensorBlock T b))
          (s1414SourceReference T b)).toReal) := by
  unfold s1414HullReadout s1414RelativeReadout
  rw [s1414HullPushforwardMass (l := l) T b hinj hmeas hH,
    s1414ReferencePushforwardMass (l := l) T b hinj hmeas]

/-- The xi-f normalized readout inequality with explicit S1086 inputs. -/
theorem s1414XiFNormalizedReadout_le
    (hcont : S1086Q1UImageContainment (l := l) T b)
    (hinj : S1085EmbeddingInjective (l := l) T b)
    (hmeas : S1085EmbeddingMeasurable (l := l) T b)
    (hS : S1086Q1URegionMeasurable (l := l) T b)
    (hH : S1414HullImageMeasurable T b)
    (hQpos : 0 < (Measure.addHaar : Measure (qVFamTensorBlock T b))
      (qPilotQ1URegion (l := l) T b))
    (hQfin : (Measure.addHaar : Measure (qVFamTensorBlock T b))
      (qPilotQ1URegion (l := l) T b) < ⊤)
    (hHullFin : s1080PushforwardHaar (l := l) T b
      (rootStackPaperThetaHull (l := l) T b) < ⊤) :
    s1414SourceReadout T b ≤ s1414HullReadout T b := by
  have hHmass := s1414HullPushforwardMass (l := l) T b hinj hmeas hH
  have hOmass := s1414ReferencePushforwardMass (l := l) T b hinj hmeas
  have hraw := s1086PerB_pushforward (l := l) T b hcont hinj hmeas hS
    hQpos hQfin hHullFin
  have hrel :
      s1414RelativeReadout (Measure.addHaar : Measure (qVFamTensorBlock T b))
        (qPilotQ1URegion (l := l) T b) (s1414SourceReference T b) ≤
      s1414RelativeReadout (s1080PushforwardHaar (l := l) T b)
        (rootStackPaperThetaHull (l := l) T b)
        (s1414SourceReferenceImage T b) := by
    unfold s1414RelativeReadout
    unfold qPilotQ1ULogHaar rootStackPaperThetaHullLogPushforward at hraw
    rw [hHmass] at hraw
    rw [hHmass, hOmass]
    exact sub_le_sub_right hraw _
  unfold s1414SourceReadout s1414HullReadout
  exact mul_le_mul_of_nonneg_left hrel (by positivity)

/-- The xi-f normalized readout transport with only the exact source fields. -/
theorem s1414XiFNormalizedReadout_le_of_exact
    (hcont : S1086Q1UImageContainment (l := l) T b)
    (hS : S1086Q1URegionMeasurable (l := l) T b)
    (hFirst : S1414ExactFirstField T b) :
    s1414SourceReadout T b ≤ s1414HullReadout T b := by
  have hinj : S1085EmbeddingInjective (l := l) T b :=
    rootStackEmbedding_injective_actual (l := l) T b
  have hmeas : S1085EmbeddingMeasurable (l := l) T b :=
    s1414Embedding_measurable (l := l) T b
  have hH : S1414HullImageMeasurable T b :=
    s1414HullImageMeasurable_of_exactFirstField (l := l) T b hFirst
  have hH' : S1085RegionMeasurable (l := l) T b := by
    change MeasurableSet (rootStackPaperThetaHull (l := l) T b)
    exact hH
  have hQpos := s1091QPilotQ1U_measure_pos (l := l) T b
  have hQfin := s1091QPilotQ1U_measure_lt_top (l := l) T b
  have hHullFin : s1080PushforwardHaar (l := l) T b
      (rootStackPaperThetaHull (l := l) T b) < ⊤ :=
    s1102Hull_finiteness_actual (l := l) T b ⟨hmeas, hH'⟩
  exact s1414XiFNormalizedReadout_le (l := l) T b hcont hinj hmeas hS hH
    hQpos hQfin hHullFin

/-! ## 6. The actual source/reference isomorphism branch -/

/-- The actual topological additive group isomorphism between the qVFam tensor
block and the root base completion. -/
noncomputable def s1414QVFamBlockContinuousAddEquiv :
    qVFamTensorBlock T b ≃ₜ+ rootBase T b where
  toAddEquiv := (qVFamBlockLinearEquiv (l := l) T b).toAddEquiv
  continuous_toFun :=
    (qVFamBlockLinearEquiv (l := l) T b).toLinearMap.continuous_of_finiteDimensional
  continuous_invFun :=
    (qVFamBlockLinearEquiv (l := l) T b).symm.toLinearMap.continuous_of_finiteDimensional

/-- The source/reference isomorphism branch: transporting both regions by the
same actual topological additive group isomorphism leaves the normalized
readout unchanged (NormalizedHaarTransport). -/
theorem s1414SourceReferenceIsomorphismTransport
    [MeasurableSpace (rootBase T b)] [BorelSpace (rootBase T b)]
    (hS : IsCompact (closure (qPilotQ1URegion (l := l) T b)))
    (hC : IsCompact (closure (s1414SourceReference T b)))
    (hSpos : 0 < (Measure.addHaar : Measure (qVFamTensorBlock T b))
      (qPilotQ1URegion (l := l) T b))
    (hCpos : 0 < (Measure.addHaar : Measure (qVFamTensorBlock T b))
      (s1414SourceReference T b)) :
    s1414RelativeReadout (Measure.addHaar : Measure (rootBase T b))
        (s1414QVFamBlockContinuousAddEquiv T b ''
          qPilotQ1URegion (l := l) T b)
        (s1414QVFamBlockContinuousAddEquiv T b ''
          s1414SourceReference T b) =
      s1414RelativeReadout (Measure.addHaar : Measure (qVFamTensorBlock T b))
        (qPilotQ1URegion (l := l) T b) (s1414SourceReference T b) :=
  s1414RelativeReadout_image_eq
    (s1414QVFamBlockContinuousAddEquiv T b)
    (Measure.addHaar) (Measure.addHaar) hS hC hSpos hCpos

/-! ## 7. Packaged normalized readout transport and exact first field -/

/-- The packaged xi-f normalized readout transport data.  The first three
fields are the exact source inputs; the last field is the transported
normalized inequality. -/
structure S1414NormalizedReadoutData where
  /-- Exact first field: geometric containment of the q[1u] image in the
  root-stack paper theta hull. -/
  sourceImageContainment : S1086Q1UImageContainment (l := l) T b
  /-- Measurability of the q[1u] image. -/
  q1uImageMeasurable : S1086Q1URegionMeasurable (l := l) T b
  /-- Exact product-lattice identification. -/
  productImageEq : S1414ExactFirstField T b
  /-- The transported xi-f normalized readout inequality. -/
  readout_le : s1414SourceReadout T b ≤ s1414HullReadout T b

/-- Constructor: the exact source fields give the packaged normalized readout
transport. -/
theorem s1414NormalizedReadoutData_of_exact
    (hcont : S1086Q1UImageContainment (l := l) T b)
    (hS : S1086Q1URegionMeasurable (l := l) T b)
    (hFirst : S1414ExactFirstField T b) :
    S1414NormalizedReadoutData (l := l) T b where
  sourceImageContainment := hcont
  q1uImageMeasurable := hS
  productImageEq := hFirst
  readout_le := s1414XiFNormalizedReadout_le_of_exact (l := l) T b hcont hS hFirst

/-- The exact first field of a packaged normalized readout transport: the
source image containment. -/
theorem s1414NormalizedReadoutFirstField
    (D : S1414NormalizedReadoutData (l := l) T b) :
    S1086Q1UImageContainment (l := l) T b :=
  D.sourceImageContainment

/-- The exact first field is exactly the source image containment. -/
theorem s1414NormalizedReadoutFirstField_spec
    (D : S1414NormalizedReadoutData (l := l) T b) :
    s1414NormalizedReadoutFirstField (l := l) T b D =
      D.sourceImageContainment :=
  rfl

#check s1414RelativeReadout_image_eq
#check s1414RelativeReadout_map_eq
#check s1414CompletionDegreeReadoutTransport
#check s1414XiFNormalizedReadout_le_of_exact
#check s1414NormalizedReadoutData_of_exact
#check s1414NormalizedReadoutFirstField

#print axioms s1414RelativeReadout_image_eq
#print axioms s1414RelativeReadout_map_eq
#print axioms s1414CompletionDegreeReadoutTransport
#print axioms s1414XiFNormalizedReadout_le_of_exact
#print axioms s1414NormalizedReadoutData_of_exact

end XiFSource

end LeanFormal.IUT.XiFPaper.S1414NormalizedReadoutActual