import tmp.sheaf.xif.paper.S956TensorPacketLogVolumeExactActual
import tmp.sheaf.xif.paper.S945CarrierTopologyActual
import tmp.sheaf.xif.paper.S956ClosureContainmentActual

-- S961: FinalLTensorLogVolumeData is exactly the S945/S956 carrier
-- topology+Haar data.  No S959 topology instance exists in the tree and
-- S945 records that no canonical topology/Haar is available, so this is
-- an exact equivalence, not a fabricated topology.

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S961FinalLTensorLogVolumeFromCarrierTopologyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.S956TensorPacketLogVolumeExactActual
open LeanFormal.IUT.XiFPaper.S945CarrierTopologyActual
open LeanFormal.IUT.XiFPaper.S956ClosureContainmentActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Conditional FinalLTensorLogVolumeData from exact S945 carrier topology. -/
noncomputable def finalLTensorLogVolumeDataOfCarrierTopology
    (D : S945CarrierTopologyData (l := l) T b) :
    FinalLTensorLogVolumeData (l := l) T b where
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

/-- Carrier topology data extracted from FinalLTensorLogVolumeData. -/
noncomputable def carrierTopologyDataOfFinalLTensor
    (D : FinalLTensorLogVolumeData (l := l) T b) :
    S945CarrierTopologyData (l := l) T b where
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

theorem finalLTensorLogVolumeRequired_iff_carrierTopologyRequired :
    FinalLTensorLogVolumeRequired (l := l) T b ↔
      S945CarrierTopologyDataRequired (l := l) T b := by
  constructor
  · rintro ⟨D⟩
    exact ⟨carrierTopologyDataOfFinalLTensor (l := l) T b D⟩
  · rintro ⟨D⟩
    exact ⟨finalLTensorLogVolumeDataOfCarrierTopology (l := l) T b D⟩

/-- Exact minimal topology/Haar datum for S961. -/
def S961ExactTopologyGap : Prop :=
  S945CarrierTopologyDataRequired (l := l) T b

theorem S961ExactTopologyGap_iff :
    S961ExactTopologyGap (l := l) T b ↔
      FinalLTensorLogVolumeRequired (l := l) T b :=
  (finalLTensorLogVolumeRequired_iff_carrierTopologyRequired (l := l) T b).symm

#check finalLTensorLogVolumeDataOfCarrierTopology
#check finalLTensorLogVolumeRequired_iff_carrierTopologyRequired
#check S961ExactTopologyGap

end LeanFormal.IUT.XiFPaper.S961FinalLTensorLogVolumeFromCarrierTopologyActual

end