import tmp.sheaf.xif.paper.S805NonzeroHullReplacementActual
noncomputable section
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1NonzeroHullConsumerActualAdapted
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (mu : Measure (qVFamTensorBlock T b))
variable [Measure.IsAddHaarMeasure mu]

theorem S3128Stage1NonzeroHull_containment :
    qPilotPaperRegion (l := l) T b ⊆
      paperRootThetaHullNonzero (l := l) T b :=
  qPilotPaperRegion_subset_nonzeroHull (l := l) T b

noncomputable def S3128Stage1NonzeroHullData :
    NonzeroHullContainmentData (l := l) T b :=
  nonzeroHullContainmentData (l := l) T b

theorem S3128Stage1NonzeroHullData_containment :
    (S3128Stage1NonzeroHullData (l := l) T b).qPilotImage ⊆
      (S3128Stage1NonzeroHullData (l := l) T b).hull :=
  (S3128Stage1NonzeroHullData (l := l) T b).containment

/-- Consumer: the actual nonzero-hull log bridge implies the required
nonzero hull log condition. -/
theorem S3128Stage1NonzeroHull_logBridge
    (h : NonzeroHullLogBridge (l := l) T b mu) :
    NonzeroHullLogBridgeRequired (l := l) T b mu :=
  h

#check S3128Stage1NonzeroHull_containment
#check S3128Stage1NonzeroHullData_containment
#check S3128Stage1NonzeroHull_logBridge
end LeanFormal.IUT.XiFPaper.S3128Stage1NonzeroHullConsumerActualAdapted