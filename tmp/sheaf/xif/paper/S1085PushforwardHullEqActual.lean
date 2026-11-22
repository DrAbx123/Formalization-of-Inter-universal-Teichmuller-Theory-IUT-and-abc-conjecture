import tmp.sheaf.xif.paper.S1084IntegerWitnessActual
import tmp.sheaf.xif.paper.S1073RootStackPaperThetaHullActual
import tmp.sheaf.xif.paper.S1080PushforwardConstructionActual
import Mathlib.MeasureTheory.Measure.Map

/-! # S1085: pushforward hull identity

For an injective measurable map f and a measurable set S,
  (Measure.map f mu) (f '' S) = mu S,
because the preimage of f '' S is S.  Apply this to
f = rootStackEmbedding and S = paperLambdaORegion(cRoot); the hull is
definitionally f '' S.  The injectivity/measurability/measurable-set facts are
kept as explicit exact inputs (the tree has no actual continuity theorem for
rootStackEmbedding here).  No fake identity. -/

noncomputable section
open scoped BigOperators TensorProduct Topology Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1085PushforwardHullEqActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S1080PushforwardConstructionActual
open LeanFormal.IUT.XiFPaper.S1084IntegerWitnessActual
open LeanFormal.IUT.XiFPaper.S1079RootStackMeasureAuditActual
open LeanFormal.IUT.XiFPaper.S1073RootStackPaperThetaHullActual
open MeasureTheory Topology

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Generic pushforward-image identity. -/
theorem s1085Map_image_of_injective
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (mu : Measure α) {f : α → β} (hf : Measurable f)
    (hinj : Function.Injective f) {S : Set α} (hImage : MeasurableSet (f '' S)) :
    (Measure.map f mu) (f '' S) = mu S := by
  rw [Measure.map_apply hf hImage]
  rw [Set.preimage_image_eq S hinj]

/-- Exact injectivity input. -/
def S1085EmbeddingInjective : Prop :=
  Function.Injective (rootStackEmbedding (l := l) T b)

/-- Exact measurability input. -/
def S1085EmbeddingMeasurable : Prop :=
  Measurable (rootStackEmbedding (l := l) T b)

/-- Exact measurability of the lambda-O region. -/
def S1085RegionMeasurable : Prop :=
  MeasurableSet (rootStackPaperThetaHull (l := l) T b)

/-- The pushforward hull identity from the exact injectivity/measurability
data. -/
theorem s1085PushforwardHullEq_of_data
    (hinj : S1085EmbeddingInjective (l := l) T b)
    (hmeas : S1085EmbeddingMeasurable (l := l) T b)
    (hS : S1085RegionMeasurable (l := l) T b) :
    S1080PushforwardHullEq (l := l) T b := by
  unfold S1080PushforwardHullEq s1080PushforwardHaar s1079HaarOnRange
    rootStackPaperThetaHull
  exact s1085Map_image_of_injective
    (Measure.addHaar : Measure (qVFamTensorBlock T b)) hmeas hinj hS

/-- Exact minimum for the pushforward identity. -/
def S1085ExactMinimum : Prop :=
  S1085EmbeddingInjective (l := l) T b ∧
    S1085EmbeddingMeasurable (l := l) T b ∧
      S1085RegionMeasurable (l := l) T b

end LeanFormal.IUT.XiFPaper.S1085PushforwardHullEqActual

end
