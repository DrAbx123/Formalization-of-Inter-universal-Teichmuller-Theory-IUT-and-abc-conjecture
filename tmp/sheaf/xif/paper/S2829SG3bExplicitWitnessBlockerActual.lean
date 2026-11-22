import tmp.sheaf.xif.paper.S2828SG3bProductNoGoActual
import tmp.sheaf.xif.paper.PrimeStripLogShellActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual
open LeanFormal.IUT.XiFPaper.S349C3TensorLatticeRegionActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2829SG3bExplicitWitnessBlockerActual

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData I)

/-- Exact restriction: the local factor at a tensor index is not a freely
choosable field. It is the completion of I.initial.arithmetic.Fmod at the
actual selected place C3.tensorPlaces i (C3.tensorTuple i). -/
theorem S2829_localFiber_eq_completion (i : C3.tensorIndex) :
    C3LogShellFiber C3 i =
      CommonPrimeCompletion (c3LogShellPlace C3 i) := rfl

/-- The selected local place is determined by the C3 donor fields. -/
theorem S2829_localPlace_eq (i : C3.tensorIndex) :
    c3LogShellPlace C3 i =
      C3.tensorPlaces i (C3.tensorTuple i) := rfl

/-- The local fiber is a finite-dimensional Q_p-space. -/
theorem S2829_localFiber_finiteDimensional (i : C3.tensorIndex) :
    FiniteDimensional ℚ_[C3.p] (C3LogShellFiber C3 i) :=
  inferInstance

/-- The region is by definition the tensor integral image of the local
log-shells. -/
theorem S2829_region_eq_tensorIntegralRegion :
    actualC3LogShellTensorRegion C3 =
      tensorIntegralRegion
        (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i)
        (fun i => actualC3LogShell C3 i) := rfl

/-- Data that would be needed for the proposed explicit two-factor witness:
two distinct tensor indices and two local log-shell elements at each.  This
structure records the exact donor requirements; it does not assert existence. -/
structure S2829TwoFactorWitnessData where
  i : C3.tensorIndex
  j : C3.tensorIndex
  hne : i ≠ j
  a : C3LogShellFiber C3 i
  b : C3LogShellFiber C3 i
  ha : a ∈ actualC3LogShell C3 i
  hb : b ∈ actualC3LogShell C3 i
  c : C3LogShellFiber C3 j
  d : C3LogShellFiber C3 j
  hc : c ∈ actualC3LogShell C3 j
  hd : d ∈ actualC3LogShell C3 j

#check S2829_localFiber_eq_completion
#check S2829_localPlace_eq
#check S2829_localFiber_finiteDimensional
#check S2829_region_eq_tensorIntegralRegion
#check S2829TwoFactorWitnessData
#print axioms S2829_localFiber_eq_completion
#print axioms S2829_region_eq_tensorIntegralRegion

end LeanFormal.IUT.XiFPaper.S2829SG3bExplicitWitnessBlockerActual
end
