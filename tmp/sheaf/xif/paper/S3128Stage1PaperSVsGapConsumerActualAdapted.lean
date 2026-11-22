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
namespace LeanFormal.IUT.XiFPaper.S3128Stage1PaperSVsGapConsumerActualAdapted
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Consumer: the paper S gap contains the actual theta image. -/
theorem S3128Stage1PaperSVsGap_thetaImage_subset
    (G : PaperSVsModelHullGap (l := l) T b) :
    paperRootThetaImageNZ (l := l) T b ⊆ G.paperS := by
  intro x hx
  apply G.model_subset_paperS
  change x ∈ paperLeastLambdaOHull (l := l) T b
  rw [paperLeastLambdaOHull_eq_minimal (l := l) T b]
  exact paperRootThetaImageNZ_subset_minimal (l := l) T b hx

#check S3128Stage1PaperSVsGap_thetaImage_subset
end LeanFormal.IUT.XiFPaper.S3128Stage1PaperSVsGapConsumerActualAdapted