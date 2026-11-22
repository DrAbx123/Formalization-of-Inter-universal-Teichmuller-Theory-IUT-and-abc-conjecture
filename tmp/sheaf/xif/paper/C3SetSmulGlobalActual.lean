import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual

noncomputable section
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.C3SetSmulGlobalActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}

/-- Global set-level SMul by p-adic units on the C3 tensor block.
Consumers must share this same instance so that `u • region` elaborates
to the same type across modules. -/
instance c3SetSMul (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    SMul ℚ_[C3.p]ˣ (Set (C3LogShellTensorBlock C3)) :=
  ⟨fun u S => (fun x => ((u : ℚ_[C3.p]) • x)) '' S⟩

end LeanFormal.IUT.XiFPaper.C3SetSmulGlobalActual
end
