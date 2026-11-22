import tmp.sheaf.xif.paper.S909PaperSVsLeastHullActual
import tmp.sheaf.xif.paper.S1126MultiradialAuditActual
import tmp.sheaf.xif.paper.S916PaperMultiradialSActual
noncomputable section
open scoped BigOperators TensorProduct Topology
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S909PaperSVsLeastHullActual
open LeanFormal.IUT.XiFPaper.S1126MultiradialAuditActual
open LeanFormal.IUT.XiFPaper.S916PaperMultiradialSActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1PaperSHullConsumerActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

theorem S3128Stage1PaperSHull_modelHull_subset
    (D : PaperIndImageData T b) :
    modelHull T b ⊆ paperSHull T b D := by
  intro x hx
  rw [modelHull_eq_qPilotPaperRegion T b] at hx
  exact subset_closure (Or.inl (s1126QPilot_subset_thetaImage T b hx))

theorem S3128Stage1PaperSHull_theta_subset
    (D : PaperIndImageData T b) :
    paperRootThetaImageNZ T b ⊆ paperSHull T b D := by
  intro x hx
  exact subset_closure (Or.inl hx)

#check S3128Stage1PaperSHull_modelHull_subset
#check S3128Stage1PaperSHull_theta_subset
end LeanFormal.IUT.XiFPaper.S3128Stage1PaperSHullConsumerActual