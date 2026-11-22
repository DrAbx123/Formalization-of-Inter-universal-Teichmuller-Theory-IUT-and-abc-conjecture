import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2821C3BlockUnitQCharOneActual

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
open LeanFormal.IUT.XiFPaper.S2734LatticeActual
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

local instance s2821Meas : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance s2821Borel : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩
local instance s2821Proper : ProperSpace (C3LogShellTensorBlock C3) := inferInstance
local instance s2821LC : LocallyCompactSpace (C3LogShellTensorBlock C3) := inferInstance

theorem C3Block_unitQ_char_one (w : (PadicInt C3.p)ˣ) :
    (distribHaarChar (C3LogShellTensorBlock C3) (unitQHom (p := C3.p) w) : ℝ≥0) = 1 :=
  tensor_unit_char_eq_one (p := C3.p)
    (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i) w

theorem C3Block_unitQ_char_toReal_one (w : (PadicInt C3.p)ˣ) :
    (distribHaarChar (C3LogShellTensorBlock C3) (unitQHom (p := C3.p) w) : ℝ) = 1 := by
  have h := C3Block_unitQ_char_one (l := l) (V := V) (I := I) C3 w
  exact_mod_cast h

#check C3Block_unitQ_char_one
#check C3Block_unitQ_char_toReal_one
end LeanFormal.IUT.XiFPaper.S2821C3BlockUnitQCharOneActual
end
