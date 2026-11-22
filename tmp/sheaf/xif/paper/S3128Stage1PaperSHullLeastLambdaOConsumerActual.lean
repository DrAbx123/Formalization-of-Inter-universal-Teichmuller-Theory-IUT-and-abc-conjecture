import tmp.sheaf.xif.paper.S3128Stage1PaperSHullConsumerActual
import tmp.sheaf.xif.paper.S909PaperSVsLeastHullActual
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
open LeanFormal.IUT.XiFPaper.S916PaperMultiradialSActual
open LeanFormal.IUT.XiFPaper.S3128Stage1PaperSHullConsumerActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1PaperSHullLeastLambdaOConsumerActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

theorem S3128Stage1PaperSHullLeastLambdaO_subset
    (D : PaperIndImageData T b) :
    paperLeastLambdaOHull T b ⊆ paperSHull T b D := by
  change modelHull T b ⊆ paperSHull T b D
  exact S3128Stage1PaperSHull_modelHull_subset T b D

#check S3128Stage1PaperSHullLeastLambdaO_subset
end LeanFormal.IUT.XiFPaper.S3128Stage1PaperSHullLeastLambdaOConsumerActual