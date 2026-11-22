import tmp.sheaf.xif.paper.S909PaperSVsLeastHullActual
noncomputable section
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open scoped BigOperators TensorProduct Topology
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S909PaperSVsLeastHullActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1ModelHullGapConsumerActualAdapted
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Consumer: an external paper S gap gives modelHull ⊂ paperS. -/
theorem S3128Stage1ModelHull_ssubset_paperS
    (G : PaperSVsModelHullGap (l := l) T b) :
    modelHull T b ⊂ G.paperS :=
  ⟨G.model_subset_paperS, by
    rintro hsub
    rcases G.paperS_strict with ⟨x, hxS, hxnot⟩
    exact hxnot (hsub hxS)⟩

/-- Consumer: model hull is the q-pilot paper region. -/
theorem S3128Stage1ModelHullIsQPilot :
    ModelHullIsQPilot (l := l) T b :=
  modelHull_eq_qPilotPaperRegion (l := l) T b

#check S3128Stage1ModelHull_ssubset_paperS
#check S3128Stage1ModelHullIsQPilot
end LeanFormal.IUT.XiFPaper.S3128Stage1ModelHullGapConsumerActualAdapted