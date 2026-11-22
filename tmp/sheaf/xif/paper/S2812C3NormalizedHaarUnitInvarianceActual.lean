import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 800000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2812C3NormalizedHaarUnitInvarianceActual

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

local instance measAA : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelAA : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩
local instance smulAA : SMul ℚ_[C3.p]ˣ (Set (C3LogShellTensorBlock C3)) :=
  ⟨fun u S => (fun x => ((u : ℚ_[C3.p]) • x)) '' S⟩

theorem c3NormalizedTensorHaar_unit_smul
    (w : (PadicInt C3.p)ˣ) (S : Set (C3LogShellTensorBlock C3)) :
    c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      (unitQHom (p := C3.p) w • S) =
      c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3 S := by
  rw [(distribHaarChar_mul (μ := c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3)
    (unitQHom (p := C3.p) w) S).symm]
  have hchar : (distribHaarChar (C3LogShellTensorBlock C3)
      (unitQHom (p := C3.p) w) : ENNReal) = 1 :=
    congrArg (fun r : NNReal => (r : ENNReal))
      (tensor_unit_char_eq_one (p := C3.p)
        (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i) w)
  rw [hchar, one_mul]

#check c3NormalizedTensorHaar_unit_smul
end LeanFormal.IUT.XiFPaper.S2812C3NormalizedHaarUnitInvarianceActual
end
