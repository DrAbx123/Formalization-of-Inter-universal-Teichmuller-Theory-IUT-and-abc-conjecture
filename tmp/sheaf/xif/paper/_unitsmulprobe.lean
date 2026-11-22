import tmp.sheaf.xif.paper.S2733ScalingActual
noncomputable section
namespace ProbeUnits
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open MeasureTheory
variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
example : SMul ℚ_[C3.p]ˣ (C3LogShellTensorBlock C3) := inferInstance
example : DistribMulAction ℚ_[C3.p]ˣ (C3LogShellTensorBlock C3) := inferInstance
end ProbeUnits
end
