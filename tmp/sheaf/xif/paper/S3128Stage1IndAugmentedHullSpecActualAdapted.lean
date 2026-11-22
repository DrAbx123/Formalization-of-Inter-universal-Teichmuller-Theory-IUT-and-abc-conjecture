import tmp.sheaf.xif.paper.S917IndImageUnionActual
noncomputable section
open scoped BigOperators TensorProduct Topology
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S917IndImageUnionActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1IndAugmentedHullSpecActualAdapted
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

structure S3128Stage1IndAugmentedHullSpec : Prop where
  qPilot_subset_theta :
    qPilotPaperRegion (l := l) T b ⊆
      paperRootThetaImageNZ (l := l) T b
  empty_eq_closure :
    indAugmentedHull (l := l) T b
      (∅ : Set (qVFamTensorBlock T b)) =
        closure (paperRootThetaImageNZ (l := l) T b)

theorem S3128Stage1IndAugmentedHullSpec_ofSource :
    S3128Stage1IndAugmentedHullSpec (l := l) T b :=
  { qPilot_subset_theta :=
      qPilotPaperRegion_subset_thetaImageNZ (l := l) T b
    empty_eq_closure := indAugmentedHull_empty (l := l) T b }

#check S3128Stage1IndAugmentedHullSpec
#check S3128Stage1IndAugmentedHullSpec_ofSource
end LeanFormal.IUT.XiFPaper.S3128Stage1IndAugmentedHullSpecActualAdapted