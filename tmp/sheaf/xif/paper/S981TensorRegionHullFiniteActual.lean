import tmp.sheaf.xif.paper.S979TensorRegionHullInequalityActual
import tmp.sheaf.xif.paper.S974TensorHullFiniteActual

-- S981: finiteness of tensorRegionHull under the exact geometric condition
-- hull ⊆ unitRegion.  No compactness/topology is fabricated.

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.S981TensorRegionHullFiniteActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.S945TensorPacketPaperSActual
open LeanFormal.IUT.XiFPaper.S962TensorPacketPaperInequalityActual
open LeanFormal.IUT.XiFPaper.S971TensorRegionImageActual
open LeanFormal.IUT.XiFPaper.S956TensorPacketLogVolumeExactActual
open LeanFormal.IUT.XiFPaper.S979TensorRegionHullInequalityActual
open LeanFormal.IUT.XiFPaper.S974TensorHullFiniteActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (D : FinalLTensorLogVolumeData (l := l) T b)

/-- Exact geometric input: the tensor region hull is inside the
positive-finite unit region. -/
def S981TensorRegionHullSubsetUnitRegion : Prop :=
  tensorRegionHull T b D ⊆ D.unitRegion

theorem tensorRegionHull_measure_lt_top_of_subset
    (h : S981TensorRegionHullSubsetUnitRegion T b D) :
    D.measure (tensorRegionHull T b D) < ⊤ :=
  lt_of_le_of_lt (measure_mono h) D.unit_lt_top

/-- Exact minimal finiteness field. -/
def S981TensorRegionHullFinite : Prop :=
  D.measure (tensorRegionHull T b D) < ⊤

/-- Per-b S979 inequality from positivity and the geometric subset. -/
theorem qPilotTensorLog_le_tensorRegionHullLog_of_subset
    (hpos : 0 < D.measure (qPilotPaperImageInLValued T b))
    (hsub : S981TensorRegionHullSubsetUnitRegion T b D) :
    qPilotTensorLog T b D ≤
      tensorRegionHullLog T b D :=
  qPilotTensorLog_le_tensorRegionHullLog T b D hpos
    (tensorRegionHull_measure_lt_top_of_subset (l := l) T b D hsub)

/-- Per-b S979 inequality from positivity and the exact finite field. -/
theorem qPilotTensorLog_le_tensorRegionHullLog_of_finite
    (hpos : 0 < D.measure (qPilotPaperImageInLValued T b))
    (hfin : S981TensorRegionHullFinite (l := l) T b D) :
    qPilotTensorLog T b D ≤
      tensorRegionHullLog T b D :=
  qPilotTensorLog_le_tensorRegionHullLog T b D hpos hfin

/-- Global weighted inequality under per-b subset + positivity. -/
theorem tensorRegionHullPaperWeightedInequality_of_subset
    (D : ∀ b : Bad (nativePlaceSelection T),
      FinalLTensorLogVolumeData (l := l) T b)
    (hpos : ∀ b : Bad (nativePlaceSelection T),
      0 < (D b).measure (qPilotPaperImageInLValued T b))
    (hsub : ∀ b : Bad (nativePlaceSelection T),
      S981TensorRegionHullSubsetUnitRegion T b (D b)) :
    tensorRegionHullPaperWeightedInequality (l := l) T D := by
  apply tensorRegionHullPaperWeightedInequality_of_perB (l := l) T D
  constructor
  · exact hpos
  · intro b
    exact tensorRegionHull_measure_lt_top_of_subset (l := l) T b (D b) (hsub b)

#check tensorRegionHull_measure_lt_top_of_subset
#check qPilotTensorLog_le_tensorRegionHullLog_of_subset
#check tensorRegionHullPaperWeightedInequality_of_subset

end LeanFormal.IUT.XiFPaper.S981TensorRegionHullFiniteActual

end