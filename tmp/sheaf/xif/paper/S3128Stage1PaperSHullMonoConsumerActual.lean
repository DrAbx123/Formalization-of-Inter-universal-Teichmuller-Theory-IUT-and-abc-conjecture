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
namespace LeanFormal.IUT.XiFPaper.S3128Stage1PaperSHullMonoConsumerActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

theorem S3128Stage1PaperSHull_eq_closure
    (D : PaperIndImageData T b) :
    paperSHull T b D = closure (paperSImageUnion T b D) := rfl

theorem S3128Stage1PaperSHull_mono
    (D D' : PaperIndImageData T b)
    (h : D.indImage ⊆ D'.indImage) :
    paperSHull T b D ⊆ paperSHull T b D' := by
  apply closure_mono
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl hx
  · exact Or.inr (h hx)

#check S3128Stage1PaperSHull_eq_closure
#check S3128Stage1PaperSHull_mono
end LeanFormal.IUT.XiFPaper.S3128Stage1PaperSHullMonoConsumerActual