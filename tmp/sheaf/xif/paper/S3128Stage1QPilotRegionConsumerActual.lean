import tmp.sheaf.xif.paper.S805NonzeroHullReplacementActual
noncomputable section
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open scoped BigOperators TensorProduct Topology
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1QPilotRegionConsumerActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Consumer: q-pilot region equals the one-label root theta region. -/
theorem S3128Stage1QPilotRegion_eq_rootThetaRegion_one :
    qPilotPaperRegion (l := l) T b =
      rootThetaRegion (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
        (paperRootCoefficientFamily (l := l) T b) (oneLabel l) :=
  qPilotPaperRegion_eq_rootThetaRegion_one (l := l) T b

/-- Consumer: q-pilot region is contained in the nonzero theta hull. -/
theorem S3128Stage1QPilotRegion_subset_nonzeroHull :
    qPilotPaperRegion (l := l) T b ⊆
      paperRootThetaHullNonzero (l := l) T b :=
  qPilotPaperRegion_subset_nonzeroHull (l := l) T b

#check S3128Stage1QPilotRegion_eq_rootThetaRegion_one
#check S3128Stage1QPilotRegion_subset_nonzeroHull
end LeanFormal.IUT.XiFPaper.S3128Stage1QPilotRegionConsumerActual