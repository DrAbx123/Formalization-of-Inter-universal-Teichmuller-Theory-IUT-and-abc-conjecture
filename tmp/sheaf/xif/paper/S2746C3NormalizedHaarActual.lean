import tmp.sheaf.xif.paper.S2745C3RegionAllFiniteActual
import tmp.sheaf.xif.paper.S2736dTLCompactActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.PadicIntegerProductLattice
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2726PerPlaceUpdateRegionActual
open LeanFormal.IUT.XiFPaper.S2744PerPlaceRegionAllCoordsActual
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2736cTensorLatticeActual
open LeanFormal.IUT.XiFPaper.S2736dTLCompactActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance s2746Meas : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance s2746Borel : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩
local instance s2746Proper : ProperSpace (C3LogShellTensorBlock C3) := inferInstance
local instance s2746LC : LocallyCompactSpace (C3LogShellTensorBlock C3) := inferInstance

noncomputable def c3TensorLatticeCompacts :
    TopologicalSpace.PositiveCompacts (C3LogShellTensorBlock C3) :=
  ⟨⟨tensorLattice (p := C3.p)
      (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i),
    tensorLattice_compact (p := C3.p)
      (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i)⟩, by
    refine ⟨0, ?_⟩
    change (0 : C3LogShellTensorBlock C3) ∈
      interior (tensorLattice (p := C3.p)
        (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i))
    rw [(tensorLattice_isOpen (p := C3.p)
      (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i)).interior_eq]
    exact tensorLattice_zero_mem (p := C3.p)
      (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i)⟩

noncomputable def c3NormalizedTensorHaar :
    Measure (C3LogShellTensorBlock C3) :=
  Measure.addHaarMeasure (c3TensorLatticeCompacts (l := l) (V := V) (I := I) C3)

theorem c3TensorLattice_self_measure :
    c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      (tensorLattice (p := C3.p)
        (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i)) = 1 :=
  Measure.addHaarMeasure_self

theorem tensorLattice_subset_C3RegionAll
    (hρ : ∀ i, 0 ≤ C3PerPlaceUpdateRho (l := l) (V := V) (I := I) C3 T e i) :
    tensorLattice (p := C3.p)
      (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i)
      ⊆ C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e := by
  intro x hx
  rw [C3PerPlaceUpdateRegionAll, S2726PerPlaceUpdateRegionAll, Set.mem_preimage]
  rcases ((tensorLattice_mem_iff (p := C3.p)
      (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i) x).mp hx) with ⟨z, hz⟩
  refine log_le_sum_of_norm_le_one (p := C3.p)
    (ι := C3.tensorIndex)
    (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i)
    (C3PerPlaceUpdateRho (l := l) (V := V) (I := I) C3 T e) hρ
    (finitePadicTensorCoordinates (p := C3.p)
      (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i) x) ?_
  intro j
  rw [← hz]
  exact (z j).2

theorem c3NormalizedTensorHaar_region_lt_top
    [IsFiniteMeasureOnCompacts
      (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3)] :
    c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) < ⊤ :=
  C3PerPlaceUpdateRegionAll_measure_lt_top (l := l) (V := V) (I := I) C3 T e
    (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3)

theorem c3NormalizedTensorHaar_hge1
    [IsFiniteMeasureOnCompacts
      (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3)] :
    1 ≤ (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal := by
  have hρ := C3PerPlaceUpdateRho_nonneg (l := l) (V := V) (I := I) C3 T e
  have hsub := tensorLattice_subset_C3RegionAll (l := l) (V := V) (I := I) C3 T e hρ
  have hle : c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      (tensorLattice (p := C3.p) (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i))
      ≤ c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) :=
    measure_mono hsub
  have hTL : c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      (tensorLattice (p := C3.p) (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i)) = 1 :=
    c3TensorLattice_self_measure (l := l) (V := V) (I := I) C3
  have hfin : c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) ≠ ⊤ :=
    ne_of_lt (c3NormalizedTensorHaar_region_lt_top (l := l) (V := V) (I := I) C3 T e)
  calc 1 = (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (tensorLattice (p := C3.p) (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i))).toReal := by
        rw [hTL]; simp
    _ ≤ _ := ENNReal.toReal_mono hfin hle

#check c3NormalizedTensorHaar_hge1
#check c3NormalizedTensorHaar_region_lt_top
end LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual
end
