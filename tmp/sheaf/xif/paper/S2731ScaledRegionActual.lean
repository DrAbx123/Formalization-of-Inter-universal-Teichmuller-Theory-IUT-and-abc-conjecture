import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.S2731ScaledRegionActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- Paper comparison region: q-pilot scalar image of the actual tensor log-shell region. -/
noncomputable def comparisonRegionScaled (lambda : ℚ_[C3.p]) :
    Set (C3LogShellTensorBlock C3) :=
  (fun x => lambda • x) '' actualC3LogShellTensorRegion C3

#check comparisonRegionScaled
end LeanFormal.IUT.XiFPaper.S2731ScaledRegionActual
end
