import tmp.sheaf.xif.paper.S909PaperSVsLeastHullActual
import tmp.sheaf.xif.paper.S793PaperLeastLambdaOHullActual
noncomputable section
open scoped BigOperators TensorProduct Topology
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S909PaperSVsLeastHullActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1PaperSVsGapPointConsumerActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

theorem S3128Stage1PaperSVsGap_strict_point
    (G : PaperSVsModelHullGap T b) :
    ∃ x : qVFamTensorBlock T b, x ∈ G.paperS ∧ x ∉ modelHull T b :=
  G.paperS_strict

theorem S3128Stage1PaperSVsGap_modelHull_ssubset
    (G : PaperSVsModelHullGap T b) :
    modelHull T b ⊂ G.paperS :=
  ⟨G.model_subset_paperS, by
    rintro hsub
    rcases G.paperS_strict with ⟨x, hxS, hxnot⟩
    exact hxnot (hsub hxS)⟩

theorem S3128Stage1PaperSVsGap_modelHull_eq_qPilot :
    modelHull T b = qPilotPaperRegion T b :=
  modelHull_eq_qPilotPaperRegion T b

#check S3128Stage1PaperSVsGap_strict_point
#check S3128Stage1PaperSVsGap_modelHull_ssubset
#check S3128Stage1PaperSVsGap_modelHull_eq_qPilot
end LeanFormal.IUT.XiFPaper.S3128Stage1PaperSVsGapPointConsumerActual