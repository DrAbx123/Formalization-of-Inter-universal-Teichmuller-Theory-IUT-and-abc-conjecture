import tmp.sheaf.xif.paper.S3128Stage1PaperSHullConsumerActual
import tmp.sheaf.xif.paper.S1126MultiradialAuditActual
noncomputable section
open scoped BigOperators TensorProduct Topology
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S916PaperMultiradialSActual
open LeanFormal.IUT.XiFPaper.S1126MultiradialAuditActual
open LeanFormal.IUT.XiFPaper.S3128Stage1PaperSHullConsumerActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1PaperSHullQPilotConsumerActualAdapted
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

theorem S3128Stage1PaperSHullQPilot_qPilot_subset
    (D : PaperIndImageData T b) :
    qPilotPaperRegion T b ⊆ paperSHull T b D := by
  intro x hx
  exact subset_closure
    (Or.inl (s1126QPilot_subset_thetaImage T b hx))

theorem S3128Stage1PaperSHullQPilot_qPilot_subset_modelHull
    (D : PaperIndImageData T b) :
    qPilotPaperRegion T b ⊆ paperSHull T b D :=
  S3128Stage1PaperSHullQPilot_qPilot_subset T b D

#check S3128Stage1PaperSHullQPilot_qPilot_subset
end LeanFormal.IUT.XiFPaper.S3128Stage1PaperSHullQPilotConsumerActualAdapted