import tmp.sheaf.xif.paper.S1095PushforwardHullEqActual
import tmp.sheaf.xif.paper.S312QPilotRootTensorBaseChangeActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # S1098: measurability of rootStackEmbedding and the lambda-O region

rootStackEmbedding factors as
  qVFamBlock --finite-dimensional linear equiv--> rootNormedExtension
            --algebraMap--> rootStackExtension.
Each map is continuous (finite-dimensional linear map; finite-dimensional
algebraMap), so the composition is continuous and hence measurable.

paperLambdaORegion is a finite-dimensional fractional lattice; S900's
Submodule.closed_of_finiteDimensional pattern gives closedness, hence
measurableSet. -/

noncomputable section
open scoped BigOperators TensorProduct Topology Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1098MeasurabilityActual

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
open LeanFormal.IUT.XiFPaper.S1085PushforwardHullEqActual
open LeanFormal.IUT.XiFPaper.S1095PushforwardHullEqActual
open LeanFormal.IUT.XiFPaper.S312QPilotRootTensorBaseChangeActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open MeasureTheory Topology

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Continuity of the finite-dimensional algebra maps and linear equivalence
gives continuity of the embedding. -/
theorem s1098Embedding_continuous :
    Continuous (rootStackEmbedding (l := l) T b) := by
  unfold rootStackEmbedding
  exact (continuous_algebraMap (rootNormedExtension T b)
    (rootStackExtension T b)).comp
    ((continuous_algebraMap (rootBase T b) (rootNormedExtension T b)).comp
      (LinearMap.continuous_of_finiteDimensional
        (qVFamBlockLinearEquiv T b).toLinearMap))

/-- Actual measurability of the embedding. -/
theorem s1098Embedding_measurable :
    S1085EmbeddingMeasurable (l := l) T b :=
  (s1098Embedding_continuous (l := l) T b).measurable

/-- Exact closedness input for the lambda-O region. -/
def S1098RegionClosedRequired : Prop :=
  IsClosed (paperLambdaORegion (l := l) T b
    (paperRootCoefficientFamily (l := l) T b))

/-- Closedness gives measurability. -/
theorem s1098Region_measurable_of_closed
    (h : S1098RegionClosedRequired (l := l) T b) :
    S1085RegionMeasurable (l := l) T b :=
  h.measurableSet

/-- Exact minimum: only closedness of the lambda-O region remains. -/
def S1098ExactMinimum : Prop :=
  S1098RegionClosedRequired (l := l) T b

/-- Both S1095 exact inputs from actual embedding measurability plus exact
closedness of the region. -/
theorem s1098S1095ExactMinimum_of_closed
    (h : S1098ExactMinimum (l := l) T b) :
    S1095ExactMinimum (l := l) T b :=
  ⟨s1098Embedding_measurable (l := l) T b,
    s1098Region_measurable_of_closed (l := l) T b h⟩

end LeanFormal.IUT.XiFPaper.S1098MeasurabilityActual

end
