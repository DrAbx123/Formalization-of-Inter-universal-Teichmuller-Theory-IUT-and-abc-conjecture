/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S3137C3LogShellPacketNormalizedLogVolumeActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorProductDistribution
import Mathlib.Tactic

/-! # Mzk1C3BlockMeasureActual — C3-block measure part (split of Mzk1C3BlockPerPlaceActual)

Split 1/2 (measure side): the ℚ_p-dimension of the actual C3 tensor block factorizes
over the tensor index, and the actual Haar measure scales under any natural power of `p`.
No theta-exponent content here (that is the second, S3137-dependent file). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1C3BlockMeasureActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open MeasureTheory
open scoped Pointwise ENNReal BigOperators

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance c3BlockMeasurableSpace : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance c3BlockBorelSpace : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

theorem c3TensorBlockDimension_eq_prod :
    c3TensorBlockDimension C3 =
      ∏ i : C3.tensorIndex, Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i) := by
  haveI : Fact (Nat.Prime C3.p) := inferInstance
  have h : c3TensorBlockDimension C3 =
      Module.finrank ℚ_[C3.p] (FinitePadicTensor (p := C3.p)
        (fun i : C3.tensorIndex =>
          CommonPrimeCompletion (C3.tensorPlaces i (C3.tensorTuple i)))) := rfl
  rw [h]
  have hprod : (∏ i : C3.tensorIndex, Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i)) =
      ∏ i : C3.tensorIndex,
        Module.finrank ℚ_[C3.p]
          (CommonPrimeCompletion (C3.tensorPlaces i (C3.tensorTuple i))) := by
    apply Finset.prod_congr rfl
    intro i _
    rfl
  rw [hprod]
  exact finrank_finitePadicTensor (p := C3.p)
    (A := fun i : C3.tensorIndex =>
      CommonPrimeCompletion (C3.tensorPlaces i (C3.tensorTuple i)))

theorem c3Tensor_prime_smul_pos
    (μ : Measure (C3LogShellTensorBlock C3)) [Measure.IsAddHaarMeasure μ]
    (S : Set (C3LogShellTensorBlock C3)) (hpos : 0 < μ S) :
    0 < μ ((C3.p : ℚ_[C3.p]) • S) := by
  rw [c3Tensor_measure_prime_smul]
  have hp : (0 : ENNReal) < (C3.p : ENNReal) := by
    have hpNat : (0 : Nat) < C3.p := (Fact.out : Nat.Prime C3.p).pos
    exact Nat.cast_pos.2 hpNat
  have hpne : (C3.p : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top C3.p
  have hbase : (C3.p : ENNReal) ^ c3TensorBlockDimension C3 ≠ ⊤ :=
    ENNReal.pow_ne_top hpne
  exact ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr hbase) hpos.ne'

theorem c3Tensor_prime_smul_lt_top
    (μ : Measure (C3LogShellTensorBlock C3)) [Measure.IsAddHaarMeasure μ]
    (S : Set (C3LogShellTensorBlock C3)) (hfin : μ S < ⊤) :
    μ ((C3.p : ℚ_[C3.p]) • S) < ⊤ := by
  rw [c3Tensor_measure_prime_smul]
  have hp : (0 : ENNReal) < (C3.p : ENNReal) := by
    have hpNat : (0 : Nat) < C3.p := (Fact.out : Nat.Prime C3.p).pos
    exact Nat.cast_pos.2 hpNat
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (ENNReal.pow_pos hp _)) hfin

theorem c3Tensor_measure_pow_prime_smul
    (μ : Measure (C3LogShellTensorBlock C3)) [Measure.IsAddHaarMeasure μ]
    (S : Set (C3LogShellTensorBlock C3)) (m : Nat) :
    μ (((C3.p : ℚ_[C3.p]) ^ m) • S) =
      (((C3.p : ENNReal) ^ c3TensorBlockDimension C3)⁻¹) ^ m * μ S := by
  induction m generalizing S with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, mul_smul, ih, c3Tensor_measure_prime_smul]
    rw [pow_succ, mul_assoc]

theorem c3MeasureRows_length : (3 : Nat) = 3 := rfl

#check c3TensorBlockDimension_eq_prod
#check c3Tensor_measure_pow_prime_smul

end LeanFormal.IUT.XiFPaper.Mzk1C3BlockMeasureActual
end
