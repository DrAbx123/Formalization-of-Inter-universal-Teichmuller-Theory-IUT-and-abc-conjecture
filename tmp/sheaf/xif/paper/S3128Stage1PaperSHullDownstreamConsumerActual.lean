import tmp.sheaf.xif.paper.S3128Stage1PaperSHullConsumerActual
import tmp.sheaf.xif.paper.S909PaperSVsLeastHullActual
import tmp.sheaf.xif.paper.S793PaperLeastLambdaOHullActual
import tmp.sheaf.xif.paper.S805NonzeroHullReplacementActual
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
open LeanFormal.IUT.XiFPaper.S916PaperMultiradialSActual
open LeanFormal.IUT.XiFPaper.S3128Stage1PaperSHullConsumerActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1PaperSHullDownstreamConsumerActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

theorem S3128Stage1PaperSHullDownstream_modelHull_subset
    (D : PaperIndImageData T b) :
    modelHull T b ⊆ paperSHull T b D :=
  S3128Stage1PaperSHull_modelHull_subset T b D

theorem S3128Stage1PaperSHullDownstream_theta_subset
    (D : PaperIndImageData T b) :
    paperRootThetaImageNZ T b ⊆ paperSHull T b D :=
  S3128Stage1PaperSHull_theta_subset T b D

theorem S3128Stage1PaperSHullDownstream_union_subset
    (D : PaperIndImageData T b) :
    paperSImageUnion T b D ⊆ paperSHull T b D :=
  subset_closure

#check S3128Stage1PaperSHullDownstream_modelHull_subset
#check S3128Stage1PaperSHullDownstream_theta_subset
#check S3128Stage1PaperSHullDownstream_union_subset
end LeanFormal.IUT.XiFPaper.S3128Stage1PaperSHullDownstreamConsumerActual