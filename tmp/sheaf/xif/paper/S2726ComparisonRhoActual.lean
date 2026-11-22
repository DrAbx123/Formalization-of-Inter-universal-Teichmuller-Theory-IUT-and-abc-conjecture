import tmp.sheaf.xif.paper.S2726C3TensorComparisonRegionRhoActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.S2726ComparisonRhoActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S2726TensorComparisonRegionRhoActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))

/-- Per-tensor-coordinate comparison radius, summed over local places. -/
noncomputable def comparisonRho
    (j : FinitePadicTensorIndex (p := C3.p)
      (fun i => C3LogShellFiber C3 i)) : ℝ :=
  ∑ i : C3.tensorIndex,
    localLogMagnitude (badPlaceQCandidate (nativePlaceSelection T) (e i))

#check comparisonRho
end LeanFormal.IUT.XiFPaper.S2726ComparisonRhoActual
end
