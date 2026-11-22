import tmp.sheaf.xif.paper.S2745C3RegionAllFiniteActual
import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2830C3RegionUnitSmulCompactActual

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
open LeanFormal.IUT.XiFPaper.C3NormalizedHaarInstancesActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorInstancesActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measAK : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelAK : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩
local instance normAK : IsFiniteMeasureOnCompacts
    (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3) :=
  c3NormalizedTensorHaar_isFiniteMeasureOnCompacts (l := l) (V := V) (I := I) C3

theorem C3PerPlaceUpdateRegionAll_unit_smul_compact (w : (PadicInt C3.p)ˣ) :
    IsCompact ((fun x : C3LogShellTensorBlock C3 =>
      ((unitQHom (p := C3.p) w : ℚ_[C3.p]) • x)) ''
      C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) :=
  (C3PerPlaceUpdateRegionAll_compact (l := l) (V := V) (I := I) C3 T e).image
    (continuous_const_smul _)

theorem C3PerPlaceUpdateRegionAll_unit_smul_measure_lt_top (w : (PadicInt C3.p)ˣ) :
    c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      ((fun x : C3LogShellTensorBlock C3 =>
        ((unitQHom (p := C3.p) w : ℚ_[C3.p]) • x)) ''
        C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) < ⊤ :=
  IsCompact.measure_lt_top (C3PerPlaceUpdateRegionAll_unit_smul_compact (l := l) (V := V) (I := I) C3 T e w)

#check C3PerPlaceUpdateRegionAll_unit_smul_compact
end LeanFormal.IUT.XiFPaper.S2830C3RegionUnitSmulCompactActual
end
