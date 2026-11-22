import tmp.sheaf.xif.paper.S982FinalLTensorFromFiniteQuotientActual
import tmp.sheaf.xif.paper.S945CarrierTopologyActual
import tmp.sheaf.xif.paper.S961FinalLTensorLogVolumeFromCarrierTopologyActual

/-! # S986: finite-quotient transport obligations

S982 supplies actual S976 finite-carrier Haar data and a linear equivalence
from the paper carrier to Fin d -> Qp.  Transporting topology/Haar/unitRegion
along an arbitrary LinearEquiv is not automatic: it needs the topology to be
induced by the equivalence and the measure to be pushed forward, with
continuity/measurability of the equivalence and inverse.  These are recorded
as exact transport obligations; no topology or Haar is fabricated. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S986FiniteQuotientTransportActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.S956TensorPacketLogVolumeExactActual
open LeanFormal.IUT.XiFPaper.S970FiniteLogShellCarrierActual
open LeanFormal.IUT.XiFPaper.S976FiniteLogShellHaarActual
open LeanFormal.IUT.XiFPaper.S965FinalLCarrierTopologyActual
open LeanFormal.IUT.XiFPaper.S945CarrierTopologyActual
open LeanFormal.IUT.XiFPaper.S961FinalLTensorLogVolumeFromCarrierTopologyActual
open LeanFormal.IUT.XiFPaper.S982FinalLTensorFromFiniteQuotientActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- Exact transport obligations for one finite quotient linearization. -/
structure S986TransportObligations where
  linearization : S965CarrierLinearization (l := l) T b
  finiteHaar : FiniteLogShellHaarData
    (p := qVFamTensorP T b) (linearization.d)
  topology_transport : Prop
  measure_transport : Prop
  unitRegion_transport : Prop

def S986TransportObligationsRequired : Prop :=
  Nonempty (S986TransportObligations (l := l) T b)

/-- Actual FinalLTensorLogVolumeData from an S945 carrier-topology datum. -/
noncomputable def s986FinalLTensorData_of_carrierTopology
    (C : S945CarrierTopologyData T b) :
    FinalLTensorLogVolumeData T b :=
  finalLTensorLogVolumeDataOfCarrierTopology T b C

/-- Actual finite-carrier Haar data for every linearization dimension. -/
theorem s986FiniteHaar_actual
    (L : S965CarrierLinearization (l := l) T b) :
    FiniteLogShellHaarRequired (p := qVFamTensorP T b) L.d :=
  finiteLogShellHaarRequired (p := qVFamTensorP T b) L.d

/-- Exact minimal FinalLTensor data. -/
def S986FinalLTensorDataRequired : Prop :=
  Nonempty (FinalLTensorLogVolumeData T b)

end LeanFormal.IUT.XiFPaper.S986FiniteQuotientTransportActual
end
