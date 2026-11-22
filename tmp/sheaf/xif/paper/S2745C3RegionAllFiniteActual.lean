import tmp.sheaf.xif.paper.S2744PerPlaceRegionAllCoordsActual
import tmp.sheaf.xif.paper.S2726C3PerPlaceUpdateRegionActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2726PerPlaceUpdateRegionActual
open LeanFormal.IUT.XiFPaper.S2726C3PerPlaceUpdateRegionActual
open LeanFormal.IUT.XiFPaper.S2744PerPlaceRegionAllCoordsActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance s2745FiberNAG :
    ∀ i, NormedAddCommGroup (C3LogShellFiber C3 i) := fun i => inferInstance

local instance s2745FiberNS :
    ∀ i, NormedSpace ℚ_[C3.p] (C3LogShellFiber C3 i) := fun i => inferInstance

local instance s2745FiberFD :
    ∀ i, FiniteDimensional ℚ_[C3.p] (C3LogShellFiber C3 i) := fun i => inferInstance

local instance s2745Meas : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance s2745Borel : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩
local instance s2745Proper : ProperSpace (C3LogShellTensorBlock C3) := inferInstance
local instance s2745LC : LocallyCompactSpace (C3LogShellTensorBlock C3) := inferInstance

noncomputable def C3PerPlaceUpdateRho : C3.tensorIndex → ℝ :=
  fun i => S2726C3PerPlaceUpdateRho (l := l) (V := V) (I := I) C3 T e i

noncomputable def C3PerPlaceUpdateRegionAll :
    Set (C3LogShellTensorBlock C3) :=
  S2726PerPlaceUpdateRegionAll (p := C3.p) (ι := C3.tensorIndex)
    (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i)
    (C3PerPlaceUpdateRho (l := l) (V := V) (I := I) C3 T e)

theorem C3PerPlaceUpdateRho_nonneg :
    ∀ i, 0 ≤ C3PerPlaceUpdateRho (l := l) (V := V) (I := I) C3 T e i :=
  fun i => le_of_lt (localLogMagnitude_pos
    (badPlaceQCandidate (nativePlaceSelection T) (e i)))

theorem C3PerPlaceUpdateRegionAll_compact :
    IsCompact (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) :=
  letI : ∀ i, NormedAddCommGroup (C3LogShellFiber C3 i) := fun i => inferInstance
  letI : ∀ i, NormedSpace ℚ_[C3.p] (C3LogShellFiber C3 i) := fun i => inferInstance
  letI : ∀ i, FiniteDimensional ℚ_[C3.p] (C3LogShellFiber C3 i) := fun i => inferInstance
  isCompact_perPlaceUpdateRegionAll (p := C3.p) (ι := C3.tensorIndex)
    (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i)
    (C3PerPlaceUpdateRho (l := l) (V := V) (I := I) C3 T e)
    (C3PerPlaceUpdateRho_nonneg (l := l) (V := V) (I := I) C3 T e)

theorem C3PerPlaceUpdateRegionAll_measure_lt_top
    [∀ i, NormedSpace ℚ_[C3.p] (C3LogShellFiber C3 i)]
    [∀ i, FiniteDimensional ℚ_[C3.p] (C3LogShellFiber C3 i)]
    (μ : Measure (C3LogShellTensorBlock C3))
    [IsFiniteMeasureOnCompacts μ] :
    μ (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) < ⊤ :=
  (C3PerPlaceUpdateRegionAll_compact (l := l) (V := V) (I := I) C3 T e).measure_lt_top

#check C3PerPlaceUpdateRegionAll_compact

theorem C3PerPlaceUpdateRegionAll_haar_measure_lt_top :
    actualC3LogShellTensorHaar C3
      (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) < ⊤ :=
  C3PerPlaceUpdateRegionAll_measure_lt_top (l := l) (V := V) (I := I) C3 T e
    (actualC3LogShellTensorHaar C3)

#check C3PerPlaceUpdateRegionAll_haar_measure_lt_top

#check C3PerPlaceUpdateRegionAll_measure_lt_top
end LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
end
