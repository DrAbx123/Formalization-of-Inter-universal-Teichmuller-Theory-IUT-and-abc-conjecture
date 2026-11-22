import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceLogShell
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorLogShellRealization
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorLogShellTransport

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2718LogShellInterfaceActual

variable {K : Type*} [Field K] [NumberField K]

/-- Bundled actual completion/local-field log-shell interface: compact, open,
contains the completed integers, receives the actual unit logarithm, and is
stable under integral p-adic scalars. -/
theorem S2718_completionLogShell_interface
    (place : NumberField.FinitePlace K) :
    IsCompact (completionLogShell place : Set (Completion place)) ∧
      IsOpen (completionLogShell place : Set (Completion place)) ∧
      (CompletionIntegers place : Set (Completion place)) ⊆ completionLogShell place ∧
      (∀ u : (CompletionIntegers place)ˣ,
        completionUnitLog place u ∈ completionLogShell place) ∧
      (∀ (z : ℤ_[(completionRationalPrime place).val]) {x : Completion place},
        x ∈ completionLogShell place →
          padicCompletionHom place (z : PadicScalarField place) * x ∈
            completionLogShell place) :=
  ⟨isCompact_completionLogShell place,
    isOpen_completionLogShell place,
    completionIntegers_subset_logShell place,
    completionUnitLog_mem_logShell place,
    fun z => completionLogShell_padicInt_mul_mem place z⟩

/-- Actual log-shell is the inverse-scaled range of the actual completion unit
logarithm. -/
theorem S2718_completionLogShell_eq_unitLog_range
    (place : NumberField.FinitePlace K) :
    (completionLogShell place : Set (Completion place)) =
      Set.range (fun u : (CompletionIntegers place)ˣ =>
        (logShellScale (completionRationalPrime place).val : Completion place)⁻¹ *
          completionUnitLog place u) :=
  completionLogShell_eq_unitLog_range place

#print axioms S2718_completionLogShell_interface

end LeanFormal.IUT.XiFPaper.S2718LogShellInterfaceActual
end
