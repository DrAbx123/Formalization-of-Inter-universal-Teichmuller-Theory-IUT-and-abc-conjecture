import tmp.sheaf.xif.paper.S793PaperLeastLambdaOHullActual
noncomputable section
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open scoped BigOperators TensorProduct Topology
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1LeastLambdaOConsumerActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Consumer: the theta image is contained in the least lambda-O hull. -/
theorem S3128Stage1LeastLambdaO_image_subset :
    paperRootThetaImageNZ (l := l) T b ⊆
      paperLeastLambdaOHull (l := l) T b := by
  intro x hx
  exact paperLambdaORegion_cRoot_subset_least (l := l) T b
    (paperRootThetaImageNZ_subset_minimal (l := l) T b hx)

theorem S3128Stage1LeastLambdaO_eq_minimal :
    paperLeastLambdaOHull (l := l) T b =
      paperLambdaORegion (l := l) T b
        (paperRootCoefficientFamily T b) :=
  paperLeastLambdaOHull_eq_minimal (l := l) T b

theorem S3128Stage1LeastLambdaO_subset_oldUnion :
    paperLeastLambdaOHull (l := l) T b ⊆
      paperRootThetaHull (l := l) T b :=
  paperLeastLambdaOHull_subset_old_unionHull (l := l) T b

#check S3128Stage1LeastLambdaO_image_subset
#check S3128Stage1LeastLambdaO_eq_minimal
#check S3128Stage1LeastLambdaO_subset_oldUnion
end LeanFormal.IUT.XiFPaper.S3128Stage1LeastLambdaOConsumerActual