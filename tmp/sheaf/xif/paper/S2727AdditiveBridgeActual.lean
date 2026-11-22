import tmp.sheaf.xif.paper.S2727V2AssemblyActual
import tmp.sheaf.xif.paper.Cor312ComparisonRegionV2AdditiveActual
noncomputable section
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 8000000
namespace LeanFormal.IUT.XiFPaper.S2727AdditiveBridgeActual
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
open LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2AdditiveActual
variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]
local instance s2727bMeas : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance s2727bBorel : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

noncomputable def S2727AdditiveBridge
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
    Cor312ToABCBridgeInterfaceV2Additive where
  carrier := C3LogShellTensorBlock C3
  hullData := S2727C3HullData C3
  Aeps := A
  epsilonComparison := fun eps heps =>
    { comparisonRegion := fun _ _ _ => comparisonRegion C3 T e
      logShellPoint := logShellPoint
      logShellPoint_mem := logShellPoint_mem
      height_le_comparisonRegionVolume_add := by
        intro a b c habc
        rw [S2727C3HullData_logVolume]
        simpa [comparisonRegionVolume] using hheight eps heps a b c habc
      regionVolume_le_normalizedWeight := by
        obtain ⟨D, hD⟩ := hvol eps heps
        refine ⟨D, ?_⟩
        intro a b c habc
        rw [S2727C3HullData_logVolume]
        simpa [comparisonRegionVolume, S2727C3HullData_logVolume] using hD a b c habc }

theorem S2727_abcConjecture
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
  abcConjecture_of_additiveV2
    (S2727AdditiveBridge C3 T e A logShellPoint logShellPoint_mem hheight hvol)

#check S2727AdditiveBridge
#check S2727_abcConjecture
#print axioms S2727_abcConjecture

end LeanFormal.IUT.XiFPaper.S2727AdditiveBridgeActual