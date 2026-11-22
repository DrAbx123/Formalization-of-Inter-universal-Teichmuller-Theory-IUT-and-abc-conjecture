import tmp.sheaf.xif.paper.S909PaperSVsLeastHullActual
import tmp.sheaf.xif.paper.S1126MultiradialAuditActual
import tmp.sheaf.xif.paper.S916PaperMultiradialSActual
noncomputable section
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open scoped BigOperators TensorProduct Topology
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S909PaperSVsLeastHullActual
open LeanFormal.IUT.XiFPaper.S1126MultiradialAuditActual
open LeanFormal.IUT.XiFPaper.S916PaperMultiradialSActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1ModelHullConsumerActualAdapted
universe u uX uLabel
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Consumer: the actual model hull equals the q-pilot paper region. -/
theorem S3128Stage1ModelHull_eq_qPilot :
    modelHull T b = qPilotPaperRegion (l := l) T b :=
  modelHull_eq_qPilotPaperRegion (l := l) T b

/-- Consumer: the actual model hull is contained in the paper multiradial
closure hull S. -/
theorem S3128Stage1ModelHull_subset_paperSHull
    (D : PaperIndImageData (l := l) T b) :
    modelHull T b ⊆ paperSHull (l := l) T b D := by
  rw [S3128Stage1ModelHull_eq_qPilot (l := l) T b]
  intro x hx
  exact subset_closure
    (Or.inl (s1126QPilot_subset_thetaImage (l := l) T b hx))

#check S3128Stage1ModelHull_eq_qPilot
#check S3128Stage1ModelHull_subset_paperSHull
end LeanFormal.IUT.XiFPaper.S3128Stage1ModelHullConsumerActualAdapted