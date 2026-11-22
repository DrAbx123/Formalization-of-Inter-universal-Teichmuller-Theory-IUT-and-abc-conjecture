import tmp.sheaf.xif.paper.S2834C3QPilotThetaComparisonDataConsumer
import tmp.sheaf.xif.paper.C3SetSmulGlobalActual
import tmp.sheaf.xif.paper.S2835C3QPilotThetaDataConsumer

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2836C3QPilotThetaUnitScaleConsumer

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
open LeanFormal.IUT.XiFPaper.S2835C3QPilotThetaDataConsumer

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measAO : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelAO : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩


theorem C3QPilotThetaData_unit_theta_eq (w : (PadicInt C3.p)ˣ) :
    Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      (unitQHom (p := C3.p) w • C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) =
      (c3QPilotThetaComparisonData (l := l) (V := V) (I := I) C3 T e).thetaVolume :=
  (c3QPilotThetaComparisonData (l := l) (V := V) (I := I) C3 T e).thetaVolume_unit_eq w

theorem C3QPilotThetaData_theta_eq_scaled_one :
    Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      ((1 : ℚ_[C3.p]ˣ) • C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) =
      (c3QPilotThetaComparisonData (l := l) (V := V) (I := I) C3 T e).thetaVolume :=
  by
    simpa using
      (c3QPilotThetaComparisonData (l := l) (V := V) (I := I) C3 T e).thetaVolume_scale_eq (1 : ℚ_[C3.p]ˣ)

#check C3QPilotThetaData_unit_theta_eq
#check C3QPilotThetaData_theta_eq_scaled_one

end LeanFormal.IUT.XiFPaper.S2836C3QPilotThetaUnitScaleConsumer
end
