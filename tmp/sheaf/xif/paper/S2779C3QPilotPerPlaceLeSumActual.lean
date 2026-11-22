import tmp.sheaf.xif.paper.S2745C3RegionAllFiniteActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2779C3QPilotPerPlaceLeSumActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]


theorem C3PerPlaceUpdateRho_le_sum (i : C3.tensorIndex) :
    C3PerPlaceUpdateRho (l := l) (V := V) (I := I) C3 T e i ≤
      ∑ j, C3PerPlaceUpdateRho (l := l) (V := V) (I := I) C3 T e j :=
  Finset.single_le_sum (fun j _ =>
    C3PerPlaceUpdateRho_nonneg (l := l) (V := V) (I := I) C3 T e j)
    (Finset.mem_univ i)

#check C3PerPlaceUpdateRho_le_sum

end LeanFormal.IUT.XiFPaper.S2779C3QPilotPerPlaceLeSumActual
end
