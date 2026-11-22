import tmp.sheaf.xif.paper.S1085PushforwardHullEqActual
import tmp.sheaf.xif.paper.S782FiniteRootStackExtensionActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.S312QPilotRootTensorBaseChangeActual

/-! # S1090: injectivity/measurability of rootStackEmbedding

rootStackEmbedding is the composition
  qVFamBlock --linear equiv--> rootBase-extension L --algebraMap--> L(mu).
The linear equiv and the two algebra maps of finite field extensions are
injective, so the embedding is injective.  Continuity/measurability of the
algebra maps is the finite-dimensional algebraMap continuity; the lambda-O
region is a finite-dimensional lattice, closed hence measurable.

This file proves injectivity actual and reduces measurability/region
measurability to the exact finite-dimensional continuity/closedness facts. -/

noncomputable section
open scoped BigOperators TensorProduct Topology Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1090EmbeddingFactsActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S1073RootStackPaperThetaHullActual
open LeanFormal.IUT.XiFPaper.S1080PushforwardConstructionActual
open LeanFormal.IUT.XiFPaper.S1084IntegerWitnessActual
open LeanFormal.IUT.XiFPaper.S1085PushforwardHullEqActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S312QPilotRootTensorBaseChangeActual
open MeasureTheory Topology

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Actual injectivity of the root-stack embedding. -/
theorem s1090Embedding_injective :
    S1085EmbeddingInjective (l := l) T b := by
  unfold S1085EmbeddingInjective
  intro x y h
  unfold rootStackEmbedding at h
  have h1 : algebraMap (rootBase T b) (rootNormedExtension T b)
        (qVFamBlockLinearEquiv T b x) =
      algebraMap (rootBase T b) (rootNormedExtension T b)
        (qVFamBlockLinearEquiv T b y) := by
    apply (algebraMap (rootNormedExtension T b) (rootStackExtension T b)).injective
    exact h
  have h2 : qVFamBlockLinearEquiv T b x = qVFamBlockLinearEquiv T b y :=
    (algebraMap (rootBase T b) (rootNormedExtension T b)).injective h1
  exact (qVFamBlockLinearEquiv T b).injective h2

/-- Exact measurability input for the embedding. -/
def S1090EmbeddingMeasurableRequired : Prop :=
  Measurable (rootStackEmbedding (l := l) T b)

/-- Exact closedness/measurability input for the lambda-O region. -/
def S1090RegionClosedRequired : Prop :=
  IsClosed (paperLambdaORegion (l := l) T b
    (paperRootCoefficientFamily (l := l) T b))

/-- The S1085 data follow from the embedding injectivity (actual) plus the
exact measurability/closedness facts. -/
theorem s1090Data_of_measurable_closed
    (hmeas : S1090EmbeddingMeasurableRequired (l := l) T b)
    (hclosed : S1090RegionClosedRequired (l := l) T b) :
    S1085EmbeddingInjective (l := l) T b ∧
      S1085EmbeddingMeasurable (l := l) T b ∧
        IsClosed (paperLambdaORegion (l := l) T b
          (paperRootCoefficientFamily (l := l) T b)) :=
  ⟨s1090Embedding_injective (l := l) T b, hmeas, hclosed⟩

end LeanFormal.IUT.XiFPaper.S1090EmbeddingFactsActual

end
