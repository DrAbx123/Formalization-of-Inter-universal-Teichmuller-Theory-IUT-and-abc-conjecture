import tmp.sheaf.n8.closure.C7ConstructedDivisors

/-!
# C7 edge law constructed: decisive symbolic counterexample

The proposed edge law is
  hTensor - edgeIndex * Q = -log edgeIndex
and the corrected one is
  hTensor - Q = -log edgeIndex.

Both are false for **every** actual input X.  The actual sign facts give
  hTensor - edgeIndex*Q > 0,   -log edgeIndex <= 0,
so equality is impossible.  This is a symbolic counterexample, not an
arbitrary numeric choice.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C7EdgeLawConstructed

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C7ConstructedDivisors
open LeanFormal.IUT.N8Closure.EtaUniformizerRelationActual
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaVaryingCalibrationQOActual
open LeanFormal.IUT.N8Closure.O4ActualTensorHullTarget
open LeanFormal.IUT.N8Closure.EtaTensorHullMeasureActual
open LeanFormal.IUT.N8Closure.EtaNNOrbitHullBoundActual
open LeanFormal.IUT.N8Closure.EtaOrbitNonnegativeBounded
open LeanFormal.IUT.N8Closure.EtaNNHullVolumeActual
open LeanFormal.IUT.N8Closure.EtaNNHullVolumeEqualityActual
open LeanFormal.IUT.N8Closure.EtaLvSubmoduleSetActual
open LeanFormal.IUT.N8Closure.EtaTensorAutomorphismInterfaceActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open MeasureTheory
open scoped NNReal ENNReal Pointwise NormedField TensorProduct BigOperators

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

/-- Actual edge index cast to Real is nonnegative. -/
theorem edgeIndex_nonneg : (0 : ℝ) ≤ (c7LatticeIndex X : ℝ) :=
  Nat.cast_nonneg _

theorem edgeLaw_lhs_pos :
    0 < hTensor X 1 - (c7LatticeIndex X : ℝ) * qORegionLogVolume X := by
  have hH : 0 < hTensor X 1 := by
    have := c7H_pos X
    simpa [c7H] using this
  have hQ : qORegionLogVolume X < 0 := by
    have := c7Q_neg X
    simpa [c7Q] using this
  have hn : (0 : ℝ) ≤ (c7LatticeIndex X : ℝ) := edgeIndex_nonneg X
  nlinarith

theorem edgeLaw_rhs_nonpos :
    -Real.log (c7LatticeIndex X) ≤ 0 :=
  neg_nonpos.mpr (c7A_nonneg X)

/-- Symbolic counterexample: the proposed edge law fails for every X. -/
theorem edgeLaw_fails :
    ¬ (hTensor X 1 - (c7LatticeIndex X : ℝ) * qORegionLogVolume X =
        -Real.log (c7LatticeIndex X)) := by
  intro h
  have hpos := edgeLaw_lhs_pos X
  have hle := edgeLaw_rhs_nonpos X
  linarith

/-- Symbolic counterexample: the corrected law also fails for every X. -/
theorem correctedEdgeLaw_fails :
    ¬ (hTensor X 1 - qORegionLogVolume X =
        -Real.log (c7LatticeIndex X)) := by
  intro h
  have hH : 0 < hTensor X 1 := by
    have := c7H_pos X
    simpa [c7H] using this
  have hQ : qORegionLogVolume X < 0 := by
    have := c7Q_neg X
    simpa [c7Q] using this
  have hA : 0 ≤ Real.log (c7LatticeIndex X) := c7A_nonneg X
  nlinarith

end LeanFormal.IUT.N8Closure.C7EdgeLawConstructed