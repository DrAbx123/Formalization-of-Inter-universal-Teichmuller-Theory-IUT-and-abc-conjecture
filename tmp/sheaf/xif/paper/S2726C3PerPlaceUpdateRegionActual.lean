import tmp.sheaf.xif.paper.S2726PerPlaceUpdateRegionActual
import tmp.sheaf.xif.paper.S2726C3TensorComparisonRegionRhoActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.S2726C3PerPlaceUpdateRegionActual

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
open LeanFormal.IUT.XiFPaper.S2726PerPlaceUpdateRegionActual
open LeanFormal.IUT.XiFPaper.S2726C3TensorComparisonRegionRhoActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

noncomputable def S2726C3PerPlaceUpdateRho (i : C3.tensorIndex) : ℝ :=
  localLogMagnitude (badPlaceQCandidate (nativePlaceSelection T) (e i))

noncomputable def S2726C3PerPlaceUpdateRegion :
    Set (C3LogShellTensorBlock C3) :=
  S2726PerPlaceUpdateRegion (p := C3.p)
    (M := fun i => C3LogShellFiber C3 i) (S2726C3PerPlaceUpdateRho C3 T e)

#check S2726C3PerPlaceUpdateRegion
end LeanFormal.IUT.XiFPaper.S2726C3PerPlaceUpdateRegionActual
end
