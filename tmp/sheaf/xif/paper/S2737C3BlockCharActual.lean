import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual
import tmp.sheaf.xif.paper.S2736jTensorCharActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2737C3BlockCharActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2736jTensorCharActual

variable {l : PrimeGeFive} {V : Type*}
variable {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance c3BlockMeasurableSpace :
    MeasurableSpace (C3LogShellTensorBlock C3) := borel _

local instance c3BlockBorelSpace :
    BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

local instance c3BlockProperSpace :
    ProperSpace (C3LogShellTensorBlock C3) := inferInstance

local instance c3BlockLocallyCompactSpace :
    LocallyCompactSpace (C3LogShellTensorBlock C3) := inferInstance

theorem c3LogShellTensorBlock_char (u : ℚ_[C3.p]ˣ) :
    distribHaarChar (C3LogShellTensorBlock C3) u =
      (‖(u : ℚ_[C3.p])‖₊) ^
        Module.finrank ℚ_[C3.p] (C3LogShellTensorBlock C3) := by
  have h := tensor_char (p := C3.p) (ι := C3.tensorIndex)
    (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i) u
  change distribHaarChar (FinitePadicTensor (p := C3.p)
    (fun i : C3.tensorIndex => C3LogShellFiber C3 i)) u =
    (‖(u : ℚ_[C3.p])‖₊) ^ Module.finrank ℚ_[C3.p]
      (FinitePadicTensor (p := C3.p)
        (fun i : C3.tensorIndex => C3LogShellFiber C3 i))
  exact h

#check c3LogShellTensorBlock_char
end LeanFormal.IUT.XiFPaper.S2737C3BlockCharActual
end
