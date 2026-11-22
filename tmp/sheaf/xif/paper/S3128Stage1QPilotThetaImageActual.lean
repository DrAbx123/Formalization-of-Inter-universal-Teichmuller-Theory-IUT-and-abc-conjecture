import tmp.sheaf.xif.paper.S917IndImageUnionActual
noncomputable section
open scoped BigOperators TensorProduct Topology
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open scoped BigOperators TensorProduct Topology
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S917IndImageUnionActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1QPilotThetaImageActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Consumer: q-pilot region is contained in the theta image. -/
theorem S3128Stage1QPilot_subset_thetaImageNZ :
    qPilotPaperRegion (l := l) T b ⊆
      paperRootThetaImageNZ (l := l) T b :=
  qPilotPaperRegion_subset_thetaImageNZ (l := l) T b

/-- Consumer: q-pilot region is contained in the closure of theta image. -/
theorem S3128Stage1QPilot_subset_closureTheta :
    qPilotPaperRegion (l := l) T b ⊆
      closure (paperRootThetaImageNZ (l := l) T b) := by
  intro x hx
  exact subset_closure (S3128Stage1QPilot_subset_thetaImageNZ (l := l) T b hx)

#check S3128Stage1QPilot_subset_thetaImageNZ
#check S3128Stage1QPilot_subset_closureTheta
end LeanFormal.IUT.XiFPaper.S3128Stage1QPilotThetaImageActual