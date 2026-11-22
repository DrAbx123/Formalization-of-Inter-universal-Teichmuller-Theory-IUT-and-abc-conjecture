import tmp.sheaf.xif.paper.S2794C3NormalizedUnitLatticeInvarianceActual
import tmp.sheaf.xif.paper.S2811C3LatticeHaarSummaryActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2795C3NormalizedUnitLatticeLogVolumeActual

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
open LeanFormal.IUT.XiFPaper.C3LogShellTensorInstancesActual
open LeanFormal.IUT.XiFPaper.C3NormalizedHaarInstancesActual
open LeanFormal.IUT.XiFPaper.S2734LatticeActual
open LeanFormal.IUT.XiFPaper.S2736cTensorLatticeActual
open LeanFormal.IUT.XiFPaper.S2736dTLCompactActual
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual
open LeanFormal.IUT.XiFPaper.S2794C3NormalizedUnitLatticeInvarianceActual
open LeanFormal.IUT.XiFPaper.S2811C3LatticeHaarSummaryActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measO : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelO : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩
local instance normFinite : IsFiniteMeasureOnCompacts
    (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3) :=
  c3NormalizedTensorHaar_isFiniteMeasureOnCompacts (l := l) (V := V) (I := I) C3


theorem c3NormalizedTensorHaar_unit_smul_lattice_logVolume
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
  have hmeas := c3NormalizedTensorHaar_unit_smul_lattice (l := l) (V := V) (I := I) C3 T e w
  rw [haarLogVolume_of_lt_top]
  · rw [hmeas]; simp
  · rw [hmeas]; exact ENNReal.one_lt_top

#check c3NormalizedTensorHaar_unit_smul_lattice_logVolume
end LeanFormal.IUT.XiFPaper.S2795C3NormalizedUnitLatticeLogVolumeActual
end
