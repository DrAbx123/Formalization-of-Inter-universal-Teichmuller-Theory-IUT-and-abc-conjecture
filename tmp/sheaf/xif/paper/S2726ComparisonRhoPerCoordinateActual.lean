import tmp.sheaf.xif.paper.S2726C3TensorComparisonRegionRhoActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.S2726ComparisonRhoPerCoordinateActual

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
open LeanFormal.IUT.XiFPaper.S2726C3TensorComparisonRegionRhoActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))

/-- Per-place radius: depends on tensor place i; coordinate j is unused. -/
noncomputable def comparisonRhoAt
    (i : C3.tensorIndex)
    (j : FinitePadicTensorIndex (p := C3.p)
      (fun i => C3LogShellFiber C3 i)) : ℝ :=
  localLogMagnitude (badPlaceQCandidate (nativePlaceSelection T) (e i))

/-- Region at a single C3 tensor place. -/
noncomputable def S2726ComparisonRegionAt
    (i : C3.tensorIndex) : Set (C3LogShellTensorBlock C3) :=
  S2726C3TensorComparisonRegionRho C3 (comparisonRhoAt C3 T e i)

#check S2726ComparisonRegionAt
end LeanFormal.IUT.XiFPaper.S2726ComparisonRhoPerCoordinateActual
end
