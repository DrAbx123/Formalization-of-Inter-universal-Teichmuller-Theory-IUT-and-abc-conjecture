import tmp.sheaf.xif.paper.S965FinalLCarrierTopologyActual
import tmp.sheaf.xif.paper.S989FiniteCarrierDirectActual
import tmp.sheaf.xif.paper.S976FiniteLogShellHaarActual

/-! # S996: finite-quotient linearization for S994FiniteInput

The finite log-shell carrier is `Fin d -> Qp`.  On the actual finite paper
tensor packet `qVFamTensorBlock T b` a linearization is available from the
Qp-finite basis.  On the full `FinalLValuedCarrier` a linearization is exactly
the missing finite-module/finite-quotient input; it is recorded as the exact
minimum, not fabricated. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S996FiniteQuotientLinearizationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.S945CarrierTopologyActual
open LeanFormal.IUT.XiFPaper.S965FinalLCarrierTopologyActual
open LeanFormal.IUT.XiFPaper.S970FiniteLogShellCarrierActual
open LeanFormal.IUT.XiFPaper.S976FiniteLogShellHaarActual
open LeanFormal.IUT.XiFPaper.S989FiniteCarrierDirectActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (LeanFormal.IUT.nativePlaceSelection T))]
variable (b : Bad (LeanFormal.IUT.nativePlaceSelection T))

/-- Actual Qp-linearization of the finite paper tensor packet. -/
noncomputable def s996QVFamLinearization :
    qVFamTensorBlock T b ≃ₗ[ℚ_[(qVFamTensorP T b)]]
      (Fin (Module.finrank ℚ_[(qVFamTensorP T b)] (qVFamTensorBlock T b)) → ℚ_[(qVFamTensorP T b)]) :=
  (Module.finBasis ℚ_[(qVFamTensorP T b)] (qVFamTensorBlock T b)).equivFun

/-- Exact minimal finite-module input on the full FinalL-valued carrier. -/
def S996FinalLValuedFiniteModuleRequired : Prop :=
  Module.Finite ℚ_[(qVFamTensorP T b)] (FinalLValuedCarrier T b) ∧
    Module.Free ℚ_[(qVFamTensorP T b)] (FinalLValuedCarrier T b)

/-- Conditional actual linearization from the exact finite-module input. -/
noncomputable def s996LinearizationOfFinite
    (h : S996FinalLValuedFiniteModuleRequired (l := l) T b) :
    S965CarrierLinearization (l := l) T b := by
  letI : Module.Finite ℚ_[(qVFamTensorP T b)] (FinalLValuedCarrier T b) := h.1
  letI : Module.Free ℚ_[(qVFamTensorP T b)] (FinalLValuedCarrier T b) := h.2
  exact linearizationOfFinite (l := l) T b

/-- Exact per-b linearization required by S994FiniteInput. -/
def S996PerBLinearizationRequired : Prop :=
  ∀ b : Bad (LeanFormal.IUT.nativePlaceSelection T), Nonempty (S965CarrierLinearization (l := l) T b)

/-- Exact S994FiniteInput linearization part. -/
def S996FiniteInputLinearizationPart : Prop :=
  ∀ b : Bad (LeanFormal.IUT.nativePlaceSelection T), S996FinalLValuedFiniteModuleRequired (l := l) T b

theorem s996PerB_of_finiteModule
    (h : S996FiniteInputLinearizationPart (l := l) T) :
    S996PerBLinearizationRequired (l := l) T :=
  fun b => ⟨s996LinearizationOfFinite (l := l) T b (h b)⟩

end LeanFormal.IUT.XiFPaper.S996FiniteQuotientLinearizationActual

end
