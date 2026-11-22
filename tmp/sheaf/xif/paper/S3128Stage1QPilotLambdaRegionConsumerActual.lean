import tmp.sheaf.xif.paper.S805NonzeroHullReplacementActual
import tmp.sheaf.xif.paper.S793PaperLeastLambdaOHullActual
noncomputable section
open scoped BigOperators TensorProduct Topology
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1QPilotLambdaRegionConsumerActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Consumer: q-pilot region ⊆ theta image ⊆ paper lambda-O region. -/
theorem S3128Stage1QPilot_subset_lambdaRegion :
    qPilotPaperRegion (l := l) T b ⊆
      paperLambdaORegion (l := l) T b
        (paperRootCoefficientFamily T b) := by
  intro x hx
  exact paperRootThetaImageNZ_subset_minimal (l := l) T b
    (qPilotPaperRegion_subset_thetaImageNZ (l := l) T b hx)

/-- Consumer: q-pilot region ⊆ least lambda-O hull. -/
theorem S3128Stage1QPilot_subset_leastLambdaOHull :
    qPilotPaperRegion (l := l) T b ⊆
      paperLeastLambdaOHull (l := l) T b := by
  intro x hx
  rw [paperLeastLambdaOHull_eq_minimal (l := l) T b]
  exact S3128Stage1QPilot_subset_lambdaRegion (l := l) T b hx

#check S3128Stage1QPilot_subset_lambdaRegion
#check S3128Stage1QPilot_subset_leastLambdaOHull
end LeanFormal.IUT.XiFPaper.S3128Stage1QPilotLambdaRegionConsumerActual