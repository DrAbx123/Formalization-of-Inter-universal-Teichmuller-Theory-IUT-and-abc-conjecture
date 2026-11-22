import tmp.sheaf.xif.paper.S976FiniteLogShellHaarActual
import tmp.sheaf.xif.paper.S975DensityRegionImageActual
import tmp.sheaf.xif.paper.S965FinalLCarrierTopologyActual
import tmp.sheaf.xif.paper.S945CarrierTopologyActual
import tmp.sheaf.xif.paper.S961FinalLTensorLogVolumeFromCarrierTopologyActual

/-! # S982: FinalLTensorLogVolumeData from the finite log-shell carrier

S976 gives actual topology/Haar/unitRegion on Fin d -> Qp.  To put it on the
fixed paper carrier FinalLValuedCarrier we need an actual finite quotient
linearization plus the three transports.  The latter are recorded as the
exact finite quotient bridge; no topology or Haar is fabricated. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S982FinalLTensorFromFiniteQuotientActual

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
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- Exact finite quotient bridge: linearization, finite Haar data, and the
three transports from the finite carrier to the paper carrier. -/
structure S982FiniteQuotientBridge where
  linearization : S965CarrierLinearization (l := l) T b
  finiteHaar : FiniteLogShellHaarData
    (p := qVFamTensorP T b) (linearization.d)
  topology_transport : Prop
  measure_transport : Prop
  unitRegion_transport : Prop

def S982FiniteQuotientBridgeRequired : Prop :=
  Nonempty (S982FiniteQuotientBridge (l := l) T b)

/-- Actual S976 finite Haar exists for every finite dimension. -/
theorem s982FiniteHaar_actual
    (L : S965CarrierLinearization (l := l) T b) :
    FiniteLogShellHaarRequired (p := qVFamTensorP T b) L.d :=
  finiteLogShellHaarRequired (p := qVFamTensorP T b) L.d

/-- Actual FinalLTensorLogVolumeData from an S945 carrier-topology datum via
S961.  This is the actual construction point once the finite-quotient
transports have been supplied. -/
noncomputable def s982FinalLTensorDataOfCarrierTopology
    (C : S945CarrierTopologyData T b) :
    FinalLTensorLogVolumeData (l := l) T b :=
  finalLTensorLogVolumeDataOfCarrierTopology (l := l) T b C

/-- Exact minimal FinalLTensorLogVolumeData field. -/
def S982FinalLTensorDataRequired : Prop :=
  Nonempty (FinalLTensorLogVolumeData (l := l) T b)

end LeanFormal.IUT.XiFPaper.S982FinalLTensorFromFiniteQuotientActual
end
