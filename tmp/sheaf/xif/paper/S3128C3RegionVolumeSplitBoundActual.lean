import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapReduction
import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000
open scoped BigOperators NNReal ENNReal
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
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual
open LeanFormal.IUT.XiFPaper.S2736cTensorLatticeActual
open LeanFormal.IUT.XiFPaper.S2736dTLCompactActual

namespace LeanFormal.IUT.XiFPaper.S3128C3RegionVolumeSplitBoundActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measC3 : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelC3 : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-- The concrete C3 carrier with actual normalized Haar log-volume: unit region and
hull are the tensor lattice, the scaling is the identity, and the log-volume is
`c3NormalizedTensorHaar` (the Haar measure of `S2746C3NormalizedHaarActual`,
normalized by the compact open tensor lattice).

This is a carrier-level supply used by the split-form gap-2 reduction: it is *not*
the paper's inductive-system carrier and the named point datum used downstream is
the constant zero point, not the image of `x = a/c`.  The honest content is that
the unit region/hull/volume are actual C3 objects (tensor lattice + normalized Haar
measure), so the two structural inputs `hsplit` (measure subadditivity) and
`hptfin` (finite point measure) hold without assumptions. -/
noncomputable def S3128C3HullInterface : IQHullLogVolumeInterface (C3LogShellTensorBlock C3) where
  imageSet := tensorLattice (p := C3.p) (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i)
  hull := tensorLattice (p := C3.p) (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i)
  imageSet_subset_hull := subset_rfl
  logVolume := fun S => c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3 S
  logVolume_mono := fun h => measure_mono h
  unitRegion := tensorLattice (p := C3.p) (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i)
  scaleShift := id
  hull_subset_scaleShift := by simp
  unitRegion_logVolume_lt_top := by
    rw [c3TensorLattice_self_measure (l := l) (V := V) (I := I) C3]
    exact ENNReal.one_lt_top
  scaleShift_unitRegion_logVolume_le := by simp

/-- **Actual C3 split-form bound at the constant zero point.**  For the concrete C3
carrier the gap-2 field shape holds with `D = 1`, at the named point datum which is
(the constant) zero point: the comparison region is then the tensor lattice itself,
of actual normalized Haar log-volume `1`.

The point datum is deliberately *not* claimed to be the paper's `x = a/c` image;
this theorem only supplies the carrier-level split shape (real tensor lattice, real
normalized Haar) consumed by `ABCGap2FiniteC3SupplyActual`. -/
theorem S3128C3RegionVolume_le_weight_split
    {eps : ℝ} (heps : 0 < eps) :
    ∃ D : ℝ, ∀ a b c : Nat, IsABCTriple a b c →
      ((S3128C3HullInterface (l := l) (V := V) (I := I) C3).logVolume
        (normalizedComparisonRegion (S3128C3HullInterface (l := l) (V := V) (I := I) C3)
          (fun _ _ _ => 0) a b c)).toReal ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) +
          ((S3128C3HullInterface (l := l) (V := V) (I := I) C3).logVolume
            (S3128C3HullInterface (l := l) (V := V) (I := I) C3).hull).toReal + D := by
  have hmem : (0 : C3LogShellTensorBlock C3) ∈
      tensorLattice (p := C3.p) (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i) :=
    tensorLattice_zero_mem (p := C3.p) (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i)
  have hsub : ({0} : Set (C3LogShellTensorBlock C3)) ⊆
      tensorLattice (p := C3.p) (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i) :=
    Set.singleton_subset_iff.mpr hmem
  have hTL : c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      (tensorLattice (p := C3.p) (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i)) = 1 :=
    c3TensorLattice_self_measure (l := l) (V := V) (I := I) C3
  have hpt : c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      ({0} : Set (C3LogShellTensorBlock C3)) ≤ 1 := by
    calc c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
          ({0} : Set (C3LogShellTensorBlock C3))
        ≤ c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
          (tensorLattice (p := C3.p) (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i)) :=
          measure_mono hsub
      _ = 1 := hTL
  have hptReal : (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      ({0} : Set (C3LogShellTensorBlock C3))).toReal ≤ 1 := by
    calc (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
          ({0} : Set (C3LogShellTensorBlock C3))).toReal
        ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono ENNReal.one_ne_top hpt
      _ = 1 := ENNReal.toReal_one
  refine ⟨1, fun a b c habc => ?_⟩
  have hregion : normalizedComparisonRegion
      (S3128C3HullInterface (l := l) (V := V) (I := I) C3) (fun _ _ _ => 0) a b c =
      tensorLattice (p := C3.p) (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i) := by
    unfold normalizedComparisonRegion
    change id '' (tensorLattice (p := C3.p)
        (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i) ∪
      ({0} : Set (C3LogShellTensorBlock C3))) =
      tensorLattice (p := C3.p) (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i)
    rw [Set.image_id]
    exact Set.union_eq_left.mpr hsub
  rw [hregion]
  have hvolEq : (S3128C3HullInterface (l := l) (V := V) (I := I) C3).logVolume
      (tensorLattice (p := C3.p) (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i)) =
      c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (tensorLattice (p := C3.p) (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i)) :=
    rfl
  have hhullEq : (S3128C3HullInterface (l := l) (V := V) (I := I) C3).logVolume
      (S3128C3HullInterface (l := l) (V := V) (I := I) C3).hull =
      c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (tensorLattice (p := C3.p) (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i)) :=
    rfl
  rw [hvolEq, hhullEq, hTL, ENNReal.toReal_one]
  have hw : 0 ≤ arithmeticWeight (abcRationalPoint a c) := arithmeticWeight_nonneg _
  have hcoef : 0 ≤ 1 + eps := by linarith
  nlinarith [mul_nonneg hcoef hw]

#check S3128C3HullInterface
#check S3128C3RegionVolume_le_weight_split

end LeanFormal.IUT.XiFPaper.S3128C3RegionVolumeSplitBoundActual
end
