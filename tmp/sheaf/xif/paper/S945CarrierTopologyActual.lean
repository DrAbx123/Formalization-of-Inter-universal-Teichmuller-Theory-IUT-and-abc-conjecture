import tmp.sheaf.xif.paper.S945TensorPacketPaperSActual
/-! # S945 topology/Haar audit on FinalLValuedCarrier = qVFamBlock ⊗_Qp FinalL
S945 already has the actual theta+Ind1/2/3 image union.  The carrier has no
canonical TopologicalSpace/Haar in the tree: FinalL is an AlgebraicClosure and
Mathlib gives it no topology; Mathlib also has no tensor-product topology
instance.  This file records the exact minimal carrier topology/Haar data and
the conditional log-volume structure.  No fake topology/Haar is asserted. -/
noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S945CarrierTopologyActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedThetaIndHullActual
open LeanFormal.IUT.XiFPaper.S945TensorPacketPaperSActual
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
/-- Exact missing topology/measure on FinalL. -/
structure S945FinalLTopologyGap where
  [topologicalSpace : TopologicalSpace (FinalL T b)]
  [isTopologicalRing : IsTopologicalRing (FinalL T b)]
  [locallyCompactSpace : LocallyCompactSpace (FinalL T b)]
  [measurableSpace : MeasurableSpace (FinalL T b)]
  [borelSpace : BorelSpace (FinalL T b)]
  measure : Measure (FinalL T b)
  [isAddHaar : Measure.IsAddHaarMeasure measure]
def S945FinalLTopologyGapRequired : Prop :=
  Nonempty (S945FinalLTopologyGap (l := l) T b)
/-- Exact minimal topology/Haar data on the tensor carrier. -/
structure S945CarrierTopologyData where
  [topologicalSpace : TopologicalSpace (FinalLValuedCarrier T b)]
  [isTopologicalAddGroup : IsTopologicalAddGroup (FinalLValuedCarrier T b)]
  [locallyCompactSpace : LocallyCompactSpace (FinalLValuedCarrier T b)]
  [measurableSpace : MeasurableSpace (FinalLValuedCarrier T b)]
  [borelSpace : BorelSpace (FinalLValuedCarrier T b)]
  measure : Measure (FinalLValuedCarrier T b)
  [isAddHaar : Measure.IsAddHaarMeasure measure]
  unitRegion : Set (FinalLValuedCarrier T b)
  unit_pos : 0 < measure unitRegion
  unit_lt_top : measure unitRegion < ⊤
def S945CarrierTopologyDataRequired : Prop :=
  Nonempty (S945CarrierTopologyData (l := l) T b)
/-- The carrier topology datum supplies the S945 tensor log-volume datum. -/
noncomputable def s945TensorLogVolumeData_of_carrier
    (D : S945CarrierTopologyData (l := l) T b) :
    S945TensorLogVolumeData where
  carrier := FinalLValuedCarrier T b
  addCommGroup := inferInstance
  topologicalSpace := D.topologicalSpace
  isTopologicalAddGroup := D.isTopologicalAddGroup
  locallyCompactSpace := D.locallyCompactSpace
  measurableSpace := D.measurableSpace
  borelSpace := D.borelSpace
  measure := D.measure
  isAddHaar := D.isAddHaar
  unitRegion := D.unitRegion
  unit_pos := D.unit_pos
  unit_lt_top := D.unit_lt_top
theorem s945TensorLogVolumeRequired_of_carrier
    (D : S945CarrierTopologyData (l := l) T b) :
    S945TensorLogVolumeRequired :=
  ⟨s945TensorLogVolumeData_of_carrier (l := l) T b D⟩
end LeanFormal.IUT.XiFPaper.S945CarrierTopologyActual