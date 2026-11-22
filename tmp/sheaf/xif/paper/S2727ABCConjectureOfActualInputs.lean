import tmp.sheaf.xif.paper.S2727AdditiveBridgeActual
noncomputable section
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 8000000
namespace LeanFormal.IUT.XiFPaper.S2727ABCConjectureOfActualInputs
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2726C3PerPlaceUpdateRegionActual
open LeanFormal.IUT.XiFPaper.S2727V2RegionTarget
open LeanFormal.IUT.XiFPaper.S2727V2AssemblyActual
open LeanFormal.IUT.XiFPaper.S2727AdditiveBridgeActual

/-- Conditional ABCConjecture from the five actual-input groups
C3/T/e/A/logShellPoint plus the two arithmetic gap families hheight/hvol. -/
theorem ABCConjecture_of_actual_inputs
    {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (T : SourceNativeInitialThetaData.{0} fiveLabel)
    [Fintype (Bad (nativePlaceSelection T))]
    (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
    [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
    [DecidableEq C3.tensorIndex]
    (A : Real → Real)
    (logShellPoint : Nat → Nat → Nat → C3LogShellTensorBlock C3)
    (logShellPoint_mem :
      ∀ a b c : Nat,
        logShellPoint a b c ∈ comparisonRegion C3 T e)
    (hheight : ∀ (eps : Real), 0 < eps →
      ∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + eps) * comparisonRegionVolume C3 T e + A eps)
    (hvol : ∀ (eps : Real), 0 < eps →
      ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
        comparisonRegionVolume C3 T e ≤
          (1 + eps) * arithmeticWeight (abcRationalPoint a c) +
            ((S2727C3HullData C3).logVolume (S2727C3HullData C3).hull).toReal + D) :
    ABCConjecture :=
  S2727_abcConjecture C3 T e A logShellPoint logShellPoint_mem hheight hvol

#check ABCConjecture_of_actual_inputs
#print axioms ABCConjecture_of_actual_inputs

end LeanFormal.IUT.XiFPaper.S2727ABCConjectureOfActualInputs