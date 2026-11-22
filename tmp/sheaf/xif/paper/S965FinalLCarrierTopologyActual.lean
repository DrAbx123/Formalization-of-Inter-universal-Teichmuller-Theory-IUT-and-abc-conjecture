import tmp.sheaf.xif.paper.S945CarrierTopologyActual
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

-- S965: exact reduction of S945CarrierTopologyData to a finBasis/linear
-- equivalence plus the actual topology/Haar data.  No S959 topology exists;
-- S945 records no canonical topology/Haar on FinalLValuedCarrier.

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S965FinalLCarrierTopologyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.S945CarrierTopologyActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- A finBasis linear equivalence of the FinalL-valued carrier to Qp^d. -/
structure S965CarrierLinearization where
  d : Nat
  e : FinalLValuedCarrier T b ≃ₗ[ℚ_[qVFamTensorP T b]] (Fin d → ℚ_[qVFamTensorP T b])

def S965CarrierLinearizationRequired : Prop :=
  Nonempty (S965CarrierLinearization (l := l) T b)

/-- Actual linearization from finite-free module data (Module.finBasis). -/
noncomputable def linearizationOfFinite
    [Module.Finite ℚ_[qVFamTensorP T b] (FinalLValuedCarrier T b)]
    [Module.Free ℚ_[qVFamTensorP T b] (FinalLValuedCarrier T b)] :
    S965CarrierLinearization (l := l) T b :=
  let basis := Module.finBasis ℚ_[qVFamTensorP T b] (FinalLValuedCarrier T b)
  ⟨Module.finrank ℚ_[qVFamTensorP T b] (FinalLValuedCarrier T b), basis.equivFun⟩

/-- Exact minimum: linearization plus actual carrier topology/Haar. -/
structure S965CarrierTopologyAndLinearization where
  linearization : S965CarrierLinearization (l := l) T b
  carrierTopology : S945CarrierTopologyData (l := l) T b

def S965CarrierTopologyAndLinearizationRequired : Prop :=
  Nonempty (S965CarrierTopologyAndLinearization (l := l) T b)

noncomputable def carrierTopologyData_of_exact
    (D : S965CarrierTopologyAndLinearization (l := l) T b) :
    S945CarrierTopologyData (l := l) T b :=
  D.carrierTopology

theorem exact_iff_linearization_and_carrier :
    S965CarrierTopologyAndLinearizationRequired (l := l) T b ↔
      S965CarrierLinearizationRequired (l := l) T b ∧
      S945CarrierTopologyDataRequired (l := l) T b := by
  constructor
  · rintro ⟨D⟩
    exact ⟨⟨D.linearization⟩, ⟨D.carrierTopology⟩⟩
  · rintro ⟨⟨L⟩, ⟨C⟩⟩
    exact ⟨{ linearization := L, carrierTopology := C }⟩

#check linearizationOfFinite
#check carrierTopologyData_of_exact
#check exact_iff_linearization_and_carrier

end LeanFormal.IUT.XiFPaper.S965FinalLCarrierTopologyActual

end