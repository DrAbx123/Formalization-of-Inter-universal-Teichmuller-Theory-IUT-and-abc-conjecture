import tmp.sheaf.xif.paper.S2737C3BlockCharActual
import tmp.sheaf.xif.paper.S2733ScalingActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2738C3ScalingNormActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2733ScalingActual
open LeanFormal.IUT.XiFPaper.S2737C3BlockCharActual

variable {l : PrimeGeFive} {V : Type*}
variable {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance c3SetSMul :
    SMul ℚ_[C3.p]ˣ (Set (C3LogShellTensorBlock C3)) :=
  ⟨fun u S => (fun x => ((u : ℚ_[C3.p]) • x)) '' S⟩

theorem S2733_scalingHaar_norm
    (u : ℚ_[C3.p]ˣ) (S : Set (C3LogShellTensorBlock C3)) :
    actualC3LogShellTensorHaar C3 (u • S) =
      ((↑((‖(u : ℚ_[C3.p])‖₊) ^
        Module.finrank ℚ_[C3.p] (C3LogShellTensorBlock C3))) : ℝ≥0∞) *
        actualC3LogShellTensorHaar C3 S := by
  calc
    actualC3LogShellTensorHaar C3 (u • S)
        = (distribHaarChar (C3LogShellTensorBlock C3) u : ℝ≥0∞) *
            actualC3LogShellTensorHaar C3 S := S2733_scalingHaar C3 u S
    _ = ((↑((‖(u : ℚ_[C3.p])‖₊) ^
          Module.finrank ℚ_[C3.p] (C3LogShellTensorBlock C3))) : ℝ≥0∞) *
            actualC3LogShellTensorHaar C3 S := by
        rw [c3LogShellTensorBlock_char]

#check S2733_scalingHaar_norm
end LeanFormal.IUT.XiFPaper.S2738C3ScalingNormActual
end
