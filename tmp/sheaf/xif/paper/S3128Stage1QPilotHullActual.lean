import tmp.sheaf.xif.paper.S1126MultiradialAuditActual
noncomputable section
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open scoped BigOperators TensorProduct Topology
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1126MultiradialAuditActual
open LeanFormal.IUT.XiFPaper.S916PaperMultiradialSActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1QPilotHullActual
universe u uX uLabel
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Consumer: the actual q-pilot paper region is contained in the paper
multiradial closure hull S (via the theta possible-image branch). -/
theorem S3128Stage1QPilot_subset_paperSHull
    (D : PaperIndImageData (l := l) T b) :
    qPilotPaperRegion (l := l) T b ⊆ paperSHull (l := l) T b D := by
  intro x hx
  exact subset_closure
    (Or.inl (s1126QPilot_subset_thetaImage (l := l) T b hx))

/-- Consumer: q-pilot region is contained in every augmented hull. -/
theorem S3128Stage1QPilot_subset_augmentedHull
    (IndImages : Set (qVFamTensorBlock T b)) :
    qPilotPaperRegion (l := l) T b ⊆
      indAugmentedHull (l := l) T b IndImages :=
  s1126QPilot_subset_augmentedHull (l := l) T b IndImages

#check S3128Stage1QPilot_subset_paperSHull
#check S3128Stage1QPilot_subset_augmentedHull
end LeanFormal.IUT.XiFPaper.S3128Stage1QPilotHullActual