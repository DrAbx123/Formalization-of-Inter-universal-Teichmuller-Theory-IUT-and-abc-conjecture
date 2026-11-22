import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
namespace LeanFormal.IUT.XiFPaper.C3LogShellTensorInstancesActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

instance c3LogShellFiberNormed (i : C3.tensorIndex) :
    NormedAddCommGroup (C3LogShellFiber C3 i) := inferInstance

instance c3LogShellFiberNormedSpace (i : C3.tensorIndex) :
    NormedSpace ℚ_[C3.p] (C3LogShellFiber C3 i) := inferInstance

instance c3LogShellFiberFiniteDim (i : C3.tensorIndex) :
    FiniteDimensional ℚ_[C3.p] (C3LogShellFiber C3 i) := inferInstance

instance c3LogShellTensorBlockProperSpace :
    ProperSpace (C3LogShellTensorBlock C3) := inferInstance

instance c3LogShellTensorBlockLocallyCompactSpace :
    LocallyCompactSpace (C3LogShellTensorBlock C3) := inferInstance

#check c3LogShellTensorBlockProperSpace
#check c3LogShellTensorBlockLocallyCompactSpace
end LeanFormal.IUT.XiFPaper.C3LogShellTensorInstancesActual
end
