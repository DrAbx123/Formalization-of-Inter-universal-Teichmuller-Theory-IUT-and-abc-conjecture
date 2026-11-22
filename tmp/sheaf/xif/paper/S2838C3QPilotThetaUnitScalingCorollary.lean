import tmp.sheaf.xif.paper.S2834C3QPilotThetaComparisonDataConsumer
import tmp.sheaf.xif.paper.C3SetSmulGlobalActual
import tmp.sheaf.xif.paper.S2836C3QPilotThetaUnitScaleConsumer

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2838C3QPilotThetaUnitScalingCorollary

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
open LeanFormal.IUT.XiFPaper.S2726PerPlaceUpdateRegionActual
open LeanFormal.IUT.XiFPaper.S2734LatticeActual
open LeanFormal.IUT.XiFPaper.S2736cTensorLatticeActual
open LeanFormal.IUT.XiFPaper.S2736dTLCompactActual
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual
open LeanFormal.IUT.XiFPaper.S2834C3QPilotThetaComparisonDataConsumer
open LeanFormal.IUT.XiFPaper.S2836C3QPilotThetaUnitScaleConsumer

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measAP : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelAP : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

theorem C3QPilotThetaData_unit_scale_eq_theta (w : (PadicInt C3.p)ˣ) :
    Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      (unitQHom (p := C3.p) w • C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) =
      (c3QPilotThetaComparisonData (l := l) (V := V) (I := I) C3 T e).thetaVolume +
        Real.log ((distribHaarChar (C3LogShellTensorBlock C3) (unitQHom (p := C3.p) w) : ℝ)) :=
  (c3QPilotThetaComparisonData (l := l) (V := V) (I := I) C3 T e).thetaVolume_scale_eq
    (unitQHom (p := C3.p) w)

theorem C3QPilotThetaData_unit_scale_char_one (w : (PadicInt C3.p)ˣ) :
    (distribHaarChar (C3LogShellTensorBlock C3) (unitQHom (p := C3.p) w) : ℝ) = 1 :=
  by
    have h : (distribHaarChar (C3LogShellTensorBlock C3)
        (unitQHom (p := C3.p) w) : ℝ≥0) = 1 :=
      tensor_unit_char_eq_one (p := C3.p)
        (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i) w
    exact_mod_cast h

#check C3QPilotThetaData_unit_scale_eq_theta
#check C3QPilotThetaData_unit_scale_char_one
end LeanFormal.IUT.XiFPaper.S2838C3QPilotThetaUnitScalingCorollary
end
