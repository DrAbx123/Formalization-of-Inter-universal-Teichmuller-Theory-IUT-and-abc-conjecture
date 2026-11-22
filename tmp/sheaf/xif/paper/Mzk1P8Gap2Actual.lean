/- P8 gap-2 actual point/unit-region bounds from the C3 carrier: the unit
region bound is definitional for the S3128 C3 interface, and the point bound
at the constant zero point is the actual normalized tensor-lattice measure 1. -/
import tmp.sheaf.xif.paper.S3128C3RegionVolumeSplitBoundActual
import tmp.sheaf.xif.paper.ABCGap2FiniteC3SupplyActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S3128C3RegionVolumeSplitBoundActual

namespace LeanFormal.IUT.XiFPaper.Mzk1P8Gap2Actual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

/-- Actual unit-region bound for the C3 carrier: the hull is the unit region,
so the normalization constant `D₀ = 1` works. -/
theorem p8_unitRegionBound_c3 :
    ∃ D₀ : ℝ, 0 ≤ D₀ ∧
      (S3128C3HullInterface (l := l) (V := V) (I := I) C3).logVolume
          (S3128C3HullInterface (l := l) (V := V) (I := I) C3).unitRegion ≤
        (S3128C3HullInterface (l := l) (V := V) (I := I) C3).logVolume
            (S3128C3HullInterface (l := l) (V := V) (I := I) C3).hull +
          ENNReal.ofReal D₀ := by
  refine ⟨1, zero_le_one, ?_⟩
  simp [S3128C3HullInterface, ENNReal.ofReal_one]

/-- Actual point bound at the constant zero point: the point measure is at
most the normalized tensor-lattice measure `1`, hence at most
`(1+eps) * arithmeticWeight + 1`. -/
theorem p8_pointBound_c3 (eps : ℝ) (heps : 0 < eps) :
    ∃ D₁ : ℝ, ∀ a b c : Nat, IsABCTriple a b c →
      ((S3128C3HullInterface (l := l) (V := V) (I := I) C3).logVolume
        {(S3128C3HullInterface (l := l) (V := V) (I := I) C3).scaleShift
          (0 : C3LogShellTensorBlock C3))}.toReal ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + D₁ := by
  refine ⟨1, fun a b c habc => ?_⟩
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
  have hw : 0 ≤ arithmeticWeight (abcRationalPoint a c) :=
    arithmeticWeight_nonneg _
  have hR : (1 : ℝ) ≤ (1 + eps) * arithmeticWeight (abcRationalPoint a c) + 1 := by
    nlinarith [heps, hw, mul_nonneg (by positivity : (0:ℝ) ≤ 1 + eps) hw]
  simp only [S3128C3HullInterface]
  linarith

#print axioms p8_unitRegionBound_c3
#print axioms p8_pointBound_c3

end LeanFormal.IUT.XiFPaper.Mzk1P8Gap2Actual
end
