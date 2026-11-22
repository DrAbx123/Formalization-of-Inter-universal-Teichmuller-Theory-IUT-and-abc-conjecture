import tmp.sheaf.xif.paper.S3128Stage1PaperSHullConsumerActual
import tmp.sheaf.xif.paper.S916PaperMultiradialSActual
import tmp.sheaf.xif.paper.S793PaperLeastLambdaOHullActual
noncomputable section
open scoped BigOperators TensorProduct Topology
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S916PaperMultiradialSActual
open LeanFormal.IUT.XiFPaper.S3128Stage1PaperSHullConsumerActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1PaperSHullEmptyIndConsumerActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

theorem S3128Stage1PaperSHull_empty_ind
    (D : PaperIndImageData T b)
    (h : D.indImage = ∅) :
    paperSHull T b D = closure (paperRootThetaImageNZ T b) := by
  unfold paperSHull paperSImageUnion
  rw [h, Set.union_empty]

theorem S3128Stage1PaperSHull_empty_ind_subset
    (D : PaperIndImageData T b)
    (h : D.indImage = ∅) :
    paperSHull T b D ⊆ closure (paperRootThetaImageNZ T b) := by
  rw [S3128Stage1PaperSHull_empty_ind T b D h]

#check S3128Stage1PaperSHull_empty_ind
#check S3128Stage1PaperSHull_empty_ind_subset
end LeanFormal.IUT.XiFPaper.S3128Stage1PaperSHullEmptyIndConsumerActual