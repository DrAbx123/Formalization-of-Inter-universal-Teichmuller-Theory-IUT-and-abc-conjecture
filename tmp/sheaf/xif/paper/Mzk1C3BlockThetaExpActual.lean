/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C3BlockMeasureActual
import Mathlib.Tactic

/-! # Mzk1C3BlockThetaExpActual — C3-block theta-exponent part (split 2/2)

The S3137-dependent side: log form of the p-power Haar scaling, packet-normalized
log-volume shift `−m·log p`, and the theta exponent `m = (k+1)^2` fixed by the
capsule index (lana `scaleEltAt`). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1C3BlockThetaExpActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.Mzk1C3BlockMeasureActual
open MeasureTheory
open scoped Pointwise ENNReal BigOperators

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance c3ThetaMeasurableSpace : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance c3ThetaBorelSpace : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

theorem c3Tensor_pow_prime_smul_pos
    (μ : Measure (C3LogShellTensorBlock C3)) [Measure.IsAddHaarMeasure μ]
    (S : Set (C3LogShellTensorBlock C3)) (m : Nat) (hpos : 0 < μ S) :
    0 < μ (((C3.p : ℚ_[C3.p]) ^ m) • S) := by
  induction m generalizing S with
  | zero => simpa using hpos
  | succ m ih =>
    have hpos' : 0 < μ ((C3.p : ℚ_[C3.p]) • S) := c3Tensor_prime_smul_pos C3 μ S hpos
    rw [pow_succ, mul_smul]
    exact ih _ hpos'

theorem c3Tensor_pow_prime_smul_lt_top
    (μ : Measure (C3LogShellTensorBlock C3)) [Measure.IsAddHaarMeasure μ]
    (S : Set (C3LogShellTensorBlock C3)) (m : Nat) (hfin : μ S < ⊤) :
    μ (((C3.p : ℚ_[C3.p]) ^ m) • S) < ⊤ := by
  induction m generalizing S with
  | zero => simpa using hfin
  | succ m ih =>
    have hfin' : μ ((C3.p : ℚ_[C3.p]) • S) < ⊤ := c3Tensor_prime_smul_lt_top C3 μ S hfin
    rw [pow_succ, mul_smul]
    exact ih _ hfin'

theorem c3Tensor_log_measure_pow_prime_smul
    (μ : Measure (C3LogShellTensorBlock C3)) [Measure.IsAddHaarMeasure μ]
    (S : Set (C3LogShellTensorBlock C3)) (m : Nat)
    (hpos : 0 < μ S) (hfin : μ S < ⊤) :
    Real.log (μ (((C3.p : ℚ_[C3.p]) ^ m) • S)).toReal =
      -((m : Real) * (c3TensorBlockDimension C3 : Real) * Real.log (C3.p : Real)) +
        Real.log (μ S).toReal := by
  induction m generalizing S with
  | zero => simp
  | succ m ih =>
    have hpos' : 0 < μ ((C3.p : ℚ_[C3.p]) • S) := c3Tensor_prime_smul_pos C3 μ S hpos
    have hfin' : μ ((C3.p : ℚ_[C3.p]) • S) < ⊤ := c3Tensor_prime_smul_lt_top C3 μ S hfin
    rw [pow_succ, mul_smul]
    rw [ih _ hpos' hfin']
    rw [c3Tensor_log_measure_prime_smul C3 μ hpos hfin]
    push_cast
    ring

theorem c3PacketNormalizedLogVolume_pow_prime_smul
    (μ : Measure (C3LogShellTensorBlock C3)) [Measure.IsAddHaarMeasure μ]
    (S : Set (C3LogShellTensorBlock C3)) (m : Nat)
    (hpos : 0 < μ S) (hfin : μ S < ⊤) :
    c3PacketNormalizedLogVolume C3 μ (((C3.p : ℚ_[C3.p]) ^ m) • S) =
      -((m : Real) * Real.log (C3.p : Real)) + c3PacketNormalizedLogVolume C3 μ S := by
  have hdim : (c3TensorBlockDimension C3 : Real) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (c3TensorBlockDimension_pos (C3 := C3)))
  have hlog := c3Tensor_log_measure_pow_prime_smul C3 μ S m hpos hfin
  unfold c3PacketNormalizedLogVolume
  rw [hlog]
  field_simp

theorem c3PacketNormalizedLogVolume_pow_sq
    (μ : Measure (C3LogShellTensorBlock C3)) [Measure.IsAddHaarMeasure μ]
    (S : Set (C3LogShellTensorBlock C3)) (k : Nat)
    (hpos : 0 < μ S) (hfin : μ S < ⊤) :
    c3PacketNormalizedLogVolume C3 μ (((C3.p : ℚ_[C3.p]) ^ ((k + 1) ^ 2)) • S) =
      -(((k : Real) + 1) ^ 2) * Real.log (C3.p : Real) +
        c3PacketNormalizedLogVolume C3 μ S := by
  rw [c3PacketNormalizedLogVolume_pow_prime_smul C3 μ S ((k + 1) ^ 2) hpos hfin]
  have hcast : (((k + 1) ^ 2 : Nat) : Real) = ((k : Real) + 1) ^ 2 := by
    rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  rw [hcast]
  ring

def c3ThetaRows : List (String × String) :=
  [ ("log form of p-power scaling", "PROVED"),
    ("packet-normalized shift -m log p", "PROVED"),
    ("theta exponent m = (k+1)^2 fixed per capsule", "PROVED (corollary)") ]

theorem c3ThetaRows_length : c3ThetaRows.length = 3 := rfl

#check c3PacketNormalizedLogVolume_pow_sq
#check c3ThetaRows_length

end LeanFormal.IUT.XiFPaper.Mzk1C3BlockThetaExpActual
end
