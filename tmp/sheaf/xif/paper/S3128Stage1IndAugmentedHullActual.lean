import tmp.sheaf.xif.paper.S917IndImageUnionActual
noncomputable section
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open scoped BigOperators TensorProduct Topology
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S917IndImageUnionActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1IndAugmentedHullActual
universe u uX uLabel
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Consumer: exact Ind strict enlargement gives q-pilot proper containment in
the augmented hull. -/
theorem S3128Stage1IndStrictEnlargement_ssubset
    (IndImages : Set (qVFamTensorBlock T b))
    (h : IndStrictEnlargement (l := l) T b IndImages) :
    qPilotPaperRegion (l := l) T b ⊂
      indAugmentedHull (l := l) T b IndImages :=
  qPilot_strict_subset_indAugmentedHull (l := l) T b IndImages h

/-- Consumer: empty Ind image gives the theta closure hull exactly. -/
theorem S3128Stage1IndAugmentedHull_empty :
    indAugmentedHull (l := l) T b (∅ : Set (qVFamTensorBlock T b)) =
      closure (paperRootThetaImageNZ (l := l) T b) :=
  indAugmentedHull_empty

#check S3128Stage1IndStrictEnlargement_ssubset
#check S3128Stage1IndAugmentedHull_empty
end LeanFormal.IUT.XiFPaper.S3128Stage1IndAugmentedHullActual