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
namespace LeanFormal.IUT.XiFPaper.S3128Stage1PaperSHullIndImageConsumerActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

theorem S3128Stage1PaperSHullIndImage_indImage_subset
    (D : PaperIndImageData T b) :
    D.indImage ⊆ paperSHull T b D := by
  intro x hx
  exact subset_closure (Or.inr hx)

theorem S3128Stage1PaperSHullIndImage_union_subset
    (D : PaperIndImageData T b) :
    paperSImageUnion T b D ⊆ paperSHull T b D :=
  subset_closure

#check S3128Stage1PaperSHullIndImage_indImage_subset
#check S3128Stage1PaperSHullIndImage_union_subset
end LeanFormal.IUT.XiFPaper.S3128Stage1PaperSHullIndImageConsumerActual