import tmp.sheaf.xif.paper.S3128Stage1PaperSHullConsumerActual
import tmp.sheaf.xif.paper.S916PaperMultiradialSActual
noncomputable section
open scoped BigOperators TensorProduct Topology
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S916PaperMultiradialSActual
open LeanFormal.IUT.XiFPaper.S3128Stage1PaperSHullConsumerActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1PaperSHullClosedConsumerActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

theorem S3128Stage1PaperSHull_isClosed
    (D : PaperIndImageData T b) :
    IsClosed (paperSHull T b D) :=
  isClosed_closure

theorem S3128Stage1PaperSHull_closure_minimal
    (D : PaperIndImageData T b)
    {C : Set (qVFamTensorBlock T b)} (hC : IsClosed C)
    (h : paperSImageUnion T b D ⊆ C) :
    paperSHull T b D ⊆ C :=
  closure_minimal h hC

theorem S3128Stage1PaperSHull_closure_subset
    (D : PaperIndImageData T b) :
    closure (paperSImageUnion T b D) ⊆ paperSHull T b D :=
  subset_rfl

#check S3128Stage1PaperSHull_isClosed
#check S3128Stage1PaperSHull_closure_minimal
#check S3128Stage1PaperSHull_closure_subset
end LeanFormal.IUT.XiFPaper.S3128Stage1PaperSHullClosedConsumerActual