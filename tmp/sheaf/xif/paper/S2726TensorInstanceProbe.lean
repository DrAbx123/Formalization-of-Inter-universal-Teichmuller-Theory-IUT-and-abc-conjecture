import tmp.sheaf.xif.paper.S2726C3ComparisonRegionRhoActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2726C3ComparisonRegionRhoActual

namespace LeanFormal.IUT.XiFPaper.S2726TensorInstanceProbe

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (i : C3.tensorIndex)

#check (inferInstance : NormedAddCommGroup (C3LogShellFiber C3 i))
#check (inferInstance : NormedSpace ℚ_[C3.p] (C3LogShellFiber C3 i))
#check (inferInstance : FiniteDimensional ℚ_[C3.p] (C3LogShellFiber C3 i))
#check commonPrimeCompletionNormedField
#check commonPrimeCompletionNormedAlgebra
#check commonPrimeCompletionAlgebra
#check commonPrimeCompletionFinite
#check commonPrimeCompletionProper

example : NormedAddCommGroup (C3LogShellTensorBlock C3) := by
  letI : ∀ i, NormedAddCommGroup (C3LogShellFiber C3 i) := fun i => inferInstance
  letI : ∀ i, NormedSpace ℚ_[C3.p] (C3LogShellFiber C3 i) := fun i => inferInstance
  letI : ∀ i, FiniteDimensional ℚ_[C3.p] (C3LogShellFiber C3 i) := fun i => inferInstance
  infer_instance

example : NormedSpace ℚ_[C3.p] (C3LogShellTensorBlock C3) := by
  letI : ∀ i, NormedAddCommGroup (C3LogShellFiber C3 i) := fun i => inferInstance
  letI : ∀ i, NormedSpace ℚ_[C3.p] (C3LogShellFiber C3 i) := fun i => inferInstance
  letI : ∀ i, FiniteDimensional ℚ_[C3.p] (C3LogShellFiber C3 i) := fun i => inferInstance
  infer_instance

example : FiniteDimensional ℚ_[C3.p] (C3LogShellTensorBlock C3) := by
  letI : ∀ i, NormedAddCommGroup (C3LogShellFiber C3 i) := fun i => inferInstance
  letI : ∀ i, NormedSpace ℚ_[C3.p] (C3LogShellFiber C3 i) := fun i => inferInstance
  letI : ∀ i, FiniteDimensional ℚ_[C3.p] (C3LogShellFiber C3 i) := fun i => inferInstance
  infer_instance

end LeanFormal.IUT.XiFPaper.S2726TensorInstanceProbe
end
