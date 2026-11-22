import tmp.sheaf.xif.paper.S909PaperSVsLeastHullActual
import tmp.sheaf.xif.paper.S793PaperLeastLambdaOHullActual
noncomputable section
open scoped BigOperators TensorProduct Topology
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S909PaperSVsLeastHullActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1LeastLambdaOEqQPilotConsumerActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Consumer: least lambda-O hull equals the q-pilot paper region. -/
theorem S3128Stage1LeastLambdaO_eq_qPilot :
    paperLeastLambdaOHull (l := l) T b =
      qPilotPaperRegion (l := l) T b := by
  simpa [modelHull] using
    modelHull_eq_qPilotPaperRegion (l := l) T b

/-- Consumer: least lambda-O hull is contained in the old union hull. -/
theorem S3128Stage1LeastLambdaO_subset_oldUnion :
    paperLeastLambdaOHull (l := l) T b ⊆
      paperRootThetaHull (l := l) T b :=
  paperLeastLambdaOHull_subset_old_unionHull (l := l) T b

#check S3128Stage1LeastLambdaO_eq_qPilot
#check S3128Stage1LeastLambdaO_subset_oldUnion
end LeanFormal.IUT.XiFPaper.S3128Stage1LeastLambdaOEqQPilotConsumerActual