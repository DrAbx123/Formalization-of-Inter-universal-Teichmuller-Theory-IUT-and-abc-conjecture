import tmp.sheaf.xif.paper.S2745C3RegionAllFiniteActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2791C3QPilotSumZeroConsumerActual

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

theorem C3QPilotSum_zero_iff :
    (∑ i, C3PerPlaceUpdateRho (l := l) (V := V) (I := I) C3 T e i) = 0 ↔
      ∀ i, C3PerPlaceUpdateRho (l := l) (V := V) (I := I) C3 T e i = 0 :=
  by
    simpa using (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
      (f := fun i => C3PerPlaceUpdateRho (l := l) (V := V) (I := I) C3 T e i)
      (fun i _ => C3PerPlaceUpdateRho_nonneg (l := l) (V := V) (I := I) C3 T e i))

theorem C3QPilotSum_eq_zero_of_forall_zero
    (h : ∀ i, C3PerPlaceUpdateRho (l := l) (V := V) (I := I) C3 T e i = 0) :
    (∑ i, C3PerPlaceUpdateRho (l := l) (V := V) (I := I) C3 T e i) = 0 :=
  Finset.sum_eq_zero (fun i _ => h i)

#check C3QPilotSum_zero_iff
end LeanFormal.IUT.XiFPaper.S2791C3QPilotSumZeroConsumerActual
end
