import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.S2736dTLCompactActual
import tmp.sheaf.xif.paper.S2736cTensorLatticeActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2810C3NormalizedHaarLatticeFiniteActual

open MeasureTheory
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
open LeanFormal.IUT.XiFPaper.S2736cTensorLatticeActual
open LeanFormal.IUT.XiFPaper.S2736dTLCompactActual
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measQ2 : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelQ2 : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩


theorem C3NormalizedHaar_tensorLattice_lt_top :
    c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      (tensorLattice (p := C3.p)
        (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i)) < ⊤ := by
  rw [c3TensorLattice_self_measure (l := l) (V := V) (I := I) C3]
  exact ENNReal.one_lt_top

#check C3NormalizedHaar_tensorLattice_lt_top

end LeanFormal.IUT.XiFPaper.S2810C3NormalizedHaarLatticeFiniteActual
end
