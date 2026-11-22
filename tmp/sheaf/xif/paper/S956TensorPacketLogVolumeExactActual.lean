import tmp.sheaf.xif.paper.S945TensorPacketPaperSActual

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S956TensorPacketLogVolumeExactActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.S945TensorPacketPaperSActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- Exact tensor-packet normalized log-volume data on the actual carrier
FinalLValuedCarrier T b.  Unlike S945's arbitrary carrier field, this fixes
the carrier definitionally. -/
structure FinalLTensorLogVolumeData where
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

/-- Exact required datum on the actual carrier. -/
def FinalLTensorLogVolumeRequired : Prop :=
  Nonempty (FinalLTensorLogVolumeData (l := l) T b)

/-- Forgetting the fixed carrier gives the S945 data structure. -/
noncomputable def FinalLTensorLogVolumeData.toS945
    (D : FinalLTensorLogVolumeData (l := l) T b) :
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

/-- Any actual FinalL-carrier datum forgets to the S945 structure. -/
theorem finalLTensorLogVolumeRequired_toS945
    (h : FinalLTensorLogVolumeRequired (l := l) T b) :
    Nonempty (S945TensorLogVolumeData) := by
  rcases h with ⟨D⟩
  exact ⟨D.toS945⟩

end LeanFormal.IUT.XiFPaper.S956TensorPacketLogVolumeExactActual

end