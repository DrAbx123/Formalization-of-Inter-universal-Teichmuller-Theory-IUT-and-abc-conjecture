import tmp.sheaf.xif.paper.S965FinalLCarrierTopologyActual
import tmp.sheaf.xif.paper.S945CarrierTopologyActual

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S984FiniteQuotientBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.S965FinalLCarrierTopologyActual
open LeanFormal.IUT.XiFPaper.S945CarrierTopologyActual
open MeasureTheory
open Module

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- The exact finite-free condition on the full FinalL-valued tensor packet. -/
def S984FiniteFreeCondition : Prop :=
  Module.Finite ℚ_[qVFamTensorP T b] (FinalLValuedCarrier T b) ∧
    Module.Free ℚ_[qVFamTensorP T b] (FinalLValuedCarrier T b)

/-- Exact finite quotient bridge: the packet itself is linearly equivalent to
Qp^d.  This is S965's linearization, restated as the finite quotient bridge. -/
abbrev S984FiniteQuotientBridge : Type :=
  S965CarrierLinearization (l := l) T b

/-- Under finite-free module data, the actual basis/finrank construction gives
the linear equivalence FinalLValuedCarrier ≃ Qp^d. -/
noncomputable def finiteQuotientBridge_of_finiteFree
    [Module.Finite ℚ_[qVFamTensorP T b] (FinalLValuedCarrier T b)]
    [Module.Free ℚ_[qVFamTensorP T b] (FinalLValuedCarrier T b)] :
    S984FiniteQuotientBridge T b :=
  linearizationOfFinite (l := l) T b

/-- Existence form of the conditional bridge. -/
theorem finiteQuotientBridge_required_of_finiteFree
    [Module.Finite ℚ_[qVFamTensorP T b] (FinalLValuedCarrier T b)]
    [Module.Free ℚ_[qVFamTensorP T b] (FinalLValuedCarrier T b)] :
    Nonempty (S984FiniteQuotientBridge T b) :=
  ⟨finiteQuotientBridge_of_finiteFree (l := l) T b⟩

/-- Exact minimal requirement: finite-free on the actual carrier, plus the
carrier topology/Haar data from S965.  No quotient is fabricated. -/
def S984ExactMinimal : Prop :=
  S984FiniteFreeCondition (l := l) T b ∧
    S945CarrierTopologyDataRequired (l := l) T b

end LeanFormal.IUT.XiFPaper.S984FiniteQuotientBridgeActual

end
