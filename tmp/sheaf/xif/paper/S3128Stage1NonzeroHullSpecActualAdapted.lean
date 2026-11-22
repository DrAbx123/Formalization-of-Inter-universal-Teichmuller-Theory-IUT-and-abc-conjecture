import tmp.sheaf.xif.paper.S805NonzeroHullReplacementActual
noncomputable section
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open scoped BigOperators TensorProduct Topology
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1NonzeroHullSpecActualAdapted
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (mu : Measure (qVFamTensorBlock T b))
variable [Measure.IsAddHaarMeasure mu]

structure S3128Stage1NonzeroHullSpec : Prop where
  containment :
    qPilotPaperRegion (l := l) T b ⊆
      paperRootThetaHullNonzero (l := l) T b
  logBridge :
    NonzeroHullLogBridge (l := l) T b mu →
      NonzeroHullLogBridgeRequired (l := l) T b mu

theorem S3128Stage1NonzeroHullSpec_ofSource :
    S3128Stage1NonzeroHullSpec (l := l) T b mu :=
  { containment := qPilotPaperRegion_subset_nonzeroHull (l := l) T b
    logBridge := fun h => h }

#check S3128Stage1NonzeroHullSpec
#check S3128Stage1NonzeroHullSpec_ofSource
end LeanFormal.IUT.XiFPaper.S3128Stage1NonzeroHullSpecActualAdapted