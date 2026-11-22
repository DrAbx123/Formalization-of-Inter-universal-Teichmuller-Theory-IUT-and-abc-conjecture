import tmp.sheaf.xif.paper.S962TensorPacketPaperInequalityActual
import tmp.sheaf.xif.paper.S968FinalTensorInequalityCor312Actual
import tmp.sheaf.xif.paper.S956PaperTensorClosureActual

/-! # S974: finiteness of paperTensorHull

paperTensorHull is closure(thetaImageIndUnion).  The S956/S961 data supply a
positive finite unitRegion but no inclusion hull ⊆ unitRegion and no
compactness of the hull.  Hence finiteness is reduced to the exact inclusion
hull ⊆ unitRegion; given it, finiteness is actual by measure monotonicity. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S974TensorHullFiniteActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.S945TensorPacketPaperSActual
open LeanFormal.IUT.XiFPaper.S956TensorPacketLogVolumeExactActual
open LeanFormal.IUT.XiFPaper.S957TensorClosureContainmentActual
open LeanFormal.IUT.XiFPaper.S962TensorPacketPaperInequalityActual
open LeanFormal.IUT.XiFPaper.S968FinalTensorInequalityCor312Actual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
variable (D : FinalLTensorLogVolumeData T b)

/-- Exact missing geometric input: the tensor hull is contained in the
positive-finite unit region. -/
def S974HullSubsetUnitRegion : Prop :=
  paperTensorHull (l := l) T b D ⊆ D.unitRegion

/-- Actual finiteness, conditional on hull ⊆ unitRegion. -/
theorem paperTensorHull_measure_lt_top_of_subset
    (h : S974HullSubsetUnitRegion (l := l) T b D) :
    D.measure (paperTensorHull (l := l) T b D) < ⊤ :=
  lt_of_le_of_lt (measure_mono h) D.unit_lt_top

/-- Exact minimal finiteness input. -/
def S974HullFinitenessRequired : Prop :=
  D.measure (paperTensorHull (l := l) T b D) < ⊤

end LeanFormal.IUT.XiFPaper.S974TensorHullFiniteActual
end
