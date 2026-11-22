import tmp.sheaf.xif.paper.S2794C3NormalizedUnitLatticeInvarianceActual
import tmp.sheaf.xif.paper.S2921C3TensorBlockScalingGenericActual
import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 800000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2924C3LatticeUnitImageLogVolumeConsumerActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2734LatticeActual
open LeanFormal.IUT.XiFPaper.S2736cTensorLatticeActual
open LeanFormal.IUT.XiFPaper.S2736dTLCompactActual
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual
open LeanFormal.IUT.XiFPaper.S2794C3NormalizedUnitLatticeInvarianceActual
open LeanFormal.IUT.XiFPaper.S2921C3TensorBlockScalingGenericActual
open LeanFormal.IUT.XiFPaper.C3NormalizedHaarInstancesActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorInstancesActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measCP : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelCP : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩


theorem C3Lattice_unit_image_measure_one
    (T : SourceNativeInitialThetaData.{0} fiveLabel)
    [Fintype (Bad (nativePlaceSelection T))]
    (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
    (w : (PadicInt C3.p)ˣ) :
    c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      ((fun x : C3LogShellTensorBlock C3 =>
        ((unitQHom (p := C3.p) w : ℚ_[C3.p]) • x)) ''
        (tensorLattice (p := C3.p)
          (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i) :
          Set (C3LogShellTensorBlock C3))) = 1 :=
  c3NormalizedTensorHaar_unit_smul_lattice (l := l) (V := V) (I := I) C3 T e w

theorem C3Lattice_unit_image_logVolume_zero
    (T : SourceNativeInitialThetaData.{0} fiveLabel)
    [Fintype (Bad (nativePlaceSelection T))]
    (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
    (w : (PadicInt C3.p)ˣ) :
    haarLogVolume (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3)
      ((fun x : C3LogShellTensorBlock C3 =>
        ((unitQHom (p := C3.p) w : ℚ_[C3.p]) • x)) ''
        (tensorLattice (p := C3.p)
          (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i) :
          Set (C3LogShellTensorBlock C3))) = 0 := by
  unfold haarLogVolume
  rw [C3Lattice_unit_image_measure_one (l := l) (V := V) (I := I) C3 T e w]
  simp

#check C3Lattice_unit_image_logVolume_zero

end LeanFormal.IUT.XiFPaper.S2924C3LatticeUnitImageLogVolumeConsumerActual
end
