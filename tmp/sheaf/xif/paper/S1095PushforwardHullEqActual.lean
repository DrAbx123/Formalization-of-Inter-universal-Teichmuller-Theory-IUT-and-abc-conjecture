import tmp.sheaf.xif.paper.S1085PushforwardHullEqActual

noncomputable section
open scoped BigOperators TensorProduct Topology
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1095PushforwardHullEqActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S312QPilotRootTensorBaseChangeActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S1073RootStackPaperThetaHullActual
open LeanFormal.IUT.XiFPaper.S1080PushforwardConstructionActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S1085PushforwardHullEqActual
open MeasureTheory Topology

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Actual injectivity of the root-stack embedding. -/
theorem rootStackEmbedding_injective_actual :
    Function.Injective (rootStackEmbedding (l := l) T b) := by
  intro x y h
  unfold rootStackEmbedding at h
  have h1 : algebraMap (rootBase T b) (rootNormedExtension T b)
      (qVFamBlockLinearEquiv T b x) =
      algebraMap (rootBase T b) (rootNormedExtension T b)
        (qVFamBlockLinearEquiv T b y) :=
    (algebraMap (rootNormedExtension T b) (rootStackExtension T b)).injective h
  have h2 : qVFamBlockLinearEquiv T b x = qVFamBlockLinearEquiv T b y :=
    (algebraMap (rootBase T b) (rootNormedExtension T b)).injective h1
  exact (qVFamBlockLinearEquiv T b).injective h2

/-- The pushforward hull identity now needs only measurability of the embedding
and of the hull region. -/
theorem s1095PushforwardHullEq_of_measurable
    (hmeas : S1085EmbeddingMeasurable (l := l) T b)
    (hS : S1085RegionMeasurable (l := l) T b) :
    S1080PushforwardHullEq (l := l) T b :=
  s1085PushforwardHullEq_of_data (l := l) T b
    (rootStackEmbedding_injective_actual T b) hmeas hS

/-- Exact minimum reduced to the two measurability inputs. -/
def S1095ExactMinimum : Prop :=
  S1085EmbeddingMeasurable (l := l) T b ∧
    S1085RegionMeasurable (l := l) T b

theorem s1095PushforwardHullEq_of_exact
    (h : S1095ExactMinimum (l := l) T b) :
    S1080PushforwardHullEq (l := l) T b :=
  s1095PushforwardHullEq_of_measurable (l := l) T b h.1 h.2

/-- Direct hull image measure: the pushforward measure of the hull equals the
domain Haar of the lambda-O region, under the exact two measurability inputs. -/
theorem s1095HullMeasure_eq_domainHaar
    (h : S1095ExactMinimum (l := l) T b) :
    s1080PushforwardHaar (l := l) T b
        (rootStackPaperThetaHull (l := l) T b) =
      (Measure.addHaar : Measure (qVFamTensorBlock T b))
        (paperLambdaORegion T b
          (paperRootCoefficientFamily T b)) :=
  s1095PushforwardHullEq_of_exact (l := l) T b h

end LeanFormal.IUT.XiFPaper.S1095PushforwardHullEqActual

end
