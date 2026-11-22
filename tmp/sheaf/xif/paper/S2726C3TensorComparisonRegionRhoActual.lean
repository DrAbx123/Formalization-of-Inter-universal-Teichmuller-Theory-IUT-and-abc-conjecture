import tmp.sheaf.xif.paper.S2726TensorComparisonRegionRhoActual
import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual

noncomputable section
open scoped TensorProduct
namespace LeanFormal.IUT.XiFPaper.S2726C3TensorComparisonRegionRhoActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2726TensorComparisonRegionRhoActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

noncomputable def S2726C3TensorComparisonRegionRhoUpper
    (rho : FinitePadicTensorIndex (p := C3.p)
      (fun i => C3LogShellFiber C3 i) → ℝ) :
    Set (C3LogShellTensorBlock C3) :=
  S2726TensorComparisonRegionRhoUpper (p := C3.p)
    (M := fun i => C3LogShellFiber C3 i) rho

noncomputable def S2726C3TensorComparisonRegionRho
    (rho : FinitePadicTensorIndex (p := C3.p)
      (fun i => C3LogShellFiber C3 i) → ℝ) :
    Set (C3LogShellTensorBlock C3) :=
  S2726TensorComparisonRegionRho (p := C3.p)
    (M := fun i => C3LogShellFiber C3 i) rho

#check S2726C3TensorComparisonRegionRho
end LeanFormal.IUT.XiFPaper.S2726C3TensorComparisonRegionRhoActual
end
