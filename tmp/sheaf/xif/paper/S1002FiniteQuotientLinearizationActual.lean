import tmp.sheaf.xif.paper.S970FiniteLogShellCarrierActual
import tmp.sheaf.xif.paper.S976FiniteLogShellHaarActual
import tmp.sheaf.xif.paper.S984FiniteQuotientBridgeActual

noncomputable section
open scoped BigOperators TensorProduct
open MeasureTheory
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1002FiniteQuotientLinearizationActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.S965FinalLCarrierTopologyActual
open LeanFormal.IUT.XiFPaper.S970FiniteLogShellCarrierActual
open LeanFormal.IUT.XiFPaper.S976FiniteLogShellHaarActual
open LeanFormal.IUT.XiFPaper.S984FiniteQuotientBridgeActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Actual finite quotient linearization for any finite-dimensional Qp packet
(no topology/Haar is needed for the linear equivalence itself). -/
theorem finiteQuotientBridge_of_finiteDimensional
    (Packet : Type) [AddCommGroup Packet] [Module ℚ_[qVFamTensorP T b] Packet]
    [FiniteDimensional ℚ_[qVFamTensorP T b] Packet] :
    FiniteQuotientBridge (p := qVFamTensorP T b) Packet :=
  S976FiniteLogShellHaarActual.finiteQuotientBridge_of_finiteDimensional
    (p := qVFamTensorP T b) Packet

/-- Actual self quotient linearization of the finite carrier. -/
theorem finiteCarrier_selfLinearization (d : Nat) :
    FiniteQuotientBridge (p := qVFamTensorP T b)
      (FiniteLogShellCarrier (qVFamTensorP T b) d) :=
  S976FiniteLogShellHaarActual.finiteQuotientBridge_self
    (p := qVFamTensorP T b) d

/-- Exact finite-dimensionality condition on the full FinalL-valued packet. -/
def S1002PaperPacketFiniteDimensional : Prop :=
  FiniteDimensional ℚ_[qVFamTensorP T b] (FinalLValuedCarrier T b)

/-- Exact minimal bridge: the full paper packet is finite-dimensional, or the
paper carrier is replaced by the finite log-shell quotient. -/
def S1002FiniteQuotientBridgeExact : Prop :=
  S1002PaperPacketFiniteDimensional (l := l) T b ∨
    FiniteQuotientBridge (p := qVFamTensorP T b) (FinalLValuedCarrier T b)

/-- Actual finite carrier package: finite dimensional carrier + actual Haar. -/
structure S1002FiniteCarrierActual where
  d : Nat
  haar : FiniteLogShellHaarData (p := qVFamTensorP T b) d

noncomputable def finiteCarrierActual (d : Nat) :
    S1002FiniteCarrierActual (l := l) T b where
  d := d
  haar := S976FiniteLogShellHaarActual.finiteLogShellHaarData
    (p := qVFamTensorP T b) d

end LeanFormal.IUT.XiFPaper.S1002FiniteQuotientLinearizationActual
end