/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S3137C3LogShellPacketNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1N3SharedContainerRealActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorProductDistribution
import Mathlib.Tactic

/-! # Mzk1C3BlockPerPlaceActual — C3-block per-place computation, green first steps (A769)

Per `coord/DIRECT-GAP-ATTACK.md` Step 2-3 (green part): the ℚ_p-dimension of the actual
C3 tensor block factorizes over the tensor index; the actual Haar measure scales under any
natural power of `p` with the exact factor; the packet-normalized log-volume therefore shifts
by `−m·log p` under `p^m` (IUT III Prop. 3.9(i) at the actual C3 carrier), in particular for
the theta exponent `m = (k+1)^2` fixed by the capsule index (lana `scaleEltAt`).

Still missing (documented, not assumed): the general tensor-product Haar product formula
(per-prime `ρ_j` against the maximal order) and the archimedean term. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1C3BlockPerPlaceActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.Mzk1N3SharedContainerRealActual
open MeasureTheory
open scoped Pointwise ENNReal BigOperators

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance c3BlockMeasurableSpace : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance c3BlockBorelSpace : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-! ### 1. Dimension factorization over the tensor index -/

/-- The actual ℚ_p-dimension of the C3 tensor block is the product of the fiber dimensions
(algebraic side of the tensor measure product formula). -/
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

/-! ### 2. Positivity/finiteness helpers for a single `p` -/

theorem c3Tensor_prime_smul_pos
    (μ : Measure (C3LogShellTensorBlock C3)) [Measure.IsAddHaarMeasure μ]
    (S : Set (C3LogShellTensorBlock C3)) (hpos : 0 < μ S) :
    0 < μ ((C3.p : ℚ_[C3.p]) • S) := by
  rw [c3Tensor_measure_prime_smul]
  have hp : (0 : ENNReal) < (C3.p : ENNReal) := by
    have hpNat : (0 : ℕ) < C3.p := (Fact.out : Nat.Prime C3.p).pos
    exact_mod_cast hpNat
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
    have hpNat : (0 : ℕ) < C3.p := (Fact.out : Nat.Prime C3.p).pos
    exact_mod_cast hpNat
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (ENNReal.pow_pos hp _)) hfin

/-! ### 3. Power scaling of the measure -/

/-- The actual Haar measure of `p^m • S` is `(p^{−dim})^m·μ(S)`. -/
theorem c3Tensor_measure_pow_prime_smul
    (μ : Measure (C3LogShellTensorBlock C3)) [Measure.IsAddHaarMeasure μ]
    (S : Set (C3LogShellTensorBlock C3)) (m : ℕ) :
    μ (((C3.p : ℚ_[C3.p]) ^ m) • S) =
      (((C3.p : ENNReal) ^ c3TensorBlockDimension C3)⁻¹) ^ m * μ S := by
  induction m generalizing S with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, mul_smul, ih, c3Tensor_measure_prime_smul]
    rw [pow_succ, mul_assoc]

/-! ### 4. Positivity/finiteness under powers -/

theorem c3Tensor_pow_prime_smul_pos
    (μ : Measure (C3LogShellTensorBlock C3)) [Measure.IsAddHaarMeasure μ]
    (S : Set (C3LogShellTensorBlock C3)) (m : ℕ) (hpos : 0 < μ S) :
    0 < μ (((C3.p : ℚ_[C3.p]) ^ m) • S) := by
  induction m generalizing S with
  | zero => simpa using hpos
  | succ m ih =>
    have hpos' : 0 < μ ((C3.p : ℚ_[C3.p]) • S) := c3Tensor_prime_smul_pos C3 μ S hpos
    rw [pow_succ, mul_smul]
    exact ih _ hpos'

theorem c3Tensor_pow_prime_smul_lt_top
    (μ : Measure (C3LogShellTensorBlock C3)) [Measure.IsAddHaarMeasure μ]
    (S : Set (C3LogShellTensorBlock C3)) (m : ℕ) (hfin : μ S < ⊤) :
    μ (((C3.p : ℚ_[C3.p]) ^ m) • S) < ⊤ := by
  induction m generalizing S with
  | zero => simpa using hfin
  | succ m ih =>
    have hfin' : μ ((C3.p : ℚ_[C3.p]) • S) < ⊤ := c3Tensor_prime_smul_lt_top C3 μ S hfin
    rw [pow_succ, mul_smul]
    exact ih _ hfin'

/-! ### 5. Logarithmic form of the power scaling law -/

/-- Logarithmic form: `log μ(p^m • S) = −m·dim·log p + log μ(S)`. -/
theorem c3Tensor_log_measure_pow_prime_smul
    (μ : Measure (C3LogShellTensorBlock C3)) [Measure.IsAddHaarMeasure μ]
    (S : Set (C3LogShellTensorBlock C3)) (m : ℕ)
    (hpos : 0 < μ S) (hfin : μ S < ⊤) :
    Real.log (μ (((C3.p : ℚ_[C3.p]) ^ m) • S)).toReal =
      -((m : ℝ) * (c3TensorBlockDimension C3 : ℝ) * Real.log (C3.p : ℝ)) +
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

/-! ### 6. Packet-normalized log-volume under p-powers -/

/-- Packet-normalized log-volume shifts by exactly `−m·log p` under `p^m`. -/
theorem c3PacketNormalizedLogVolume_pow_prime_smul
    (μ : Measure (C3LogShellTensorBlock C3)) [Measure.IsAddHaarMeasure μ]
    (S : Set (C3LogShellTensorBlock C3)) (m : ℕ)
    (hpos : 0 < μ S) (hfin : μ S < ⊤) :
    c3PacketNormalizedLogVolume C3 μ (((C3.p : ℚ_[C3.p]) ^ m) • S) =
      -((m : ℝ) * Real.log (C3.p : ℝ)) + c3PacketNormalizedLogVolume C3 μ S := by
  have hdim : (c3TensorBlockDimension C3 : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (c3TensorBlockDimension_pos (C3 := C3)))
  have hlog := c3Tensor_log_measure_pow_prime_smul C3 μ S m hpos hfin
  unfold c3PacketNormalizedLogVolume
  rw [hlog]
  field_simp

/-- Theta exponent form: for the capsule index `k`, `m = (k+1)^2` (the fixed theta exponent
of lana `scaleEltAt`), the normalized log-volume shifts by `−(k+1)^2·log p`. -/
theorem c3PacketNormalizedLogVolume_pow_sq
    (μ : Measure (C3LogShellTensorBlock C3)) [Measure.IsAddHaarMeasure μ]
    (S : Set (C3LogShellTensorBlock C3)) (k : ℕ)
    (hpos : 0 < μ S) (hfin : μ S < ⊤) :
    c3PacketNormalizedLogVolume C3 μ (((C3.p : ℚ_[C3.p]) ^ ((k + 1) ^ 2)) • S) =
      -(((k : ℝ) + 1) ^ 2) * Real.log (C3.p : ℝ) +
        c3PacketNormalizedLogVolume C3 μ S := by
  rw [c3PacketNormalizedLogVolume_pow_prime_smul C3 μ S ((k + 1) ^ 2) hpos hfin]
  have hcast : (((k + 1) ^ 2 : ℕ) : ℝ) = ((k : ℝ) + 1) ^ 2 := by
    rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  rw [hcast]
  ring

/-! ### 7. Rows / remaining gaps -/

def c3PerPlaceRows : List (String × String) :=
  [ ("block dimension factorizes over tensor index", "PROVED"),
    ("Haar scaling under p^m: μ(p^m • S) = (p^{−dim})^m μ(S)", "PROVED"),
    ("log form: −m·dim·log p shift", "PROVED"),
    ("packet-normalized: −m·log p shift", "PROVED"),
    ("theta exponent m = (k+1)^2", "PROVED (corollary)"),
    ("tensor-product Haar product formula (per-prime ρ_j)", "MISSING"),
    ("archimedean term exact value", "MISSING"),
    ("dictionary θ-hull volume = V", "PENDING (see Mzk1FinalBoundarySzpiroActual)") ]

theorem c3PerPlaceRows_length : c3PerPlaceRows.length = 8 := rfl

#check c3TensorBlockDimension_eq_prod
#check c3PacketNormalizedLogVolume_pow_prime_smul
#check c3PacketNormalizedLogVolume_pow_sq
#check c3PerPlaceRows_length

end LeanFormal.IUT.XiFPaper.Mzk1C3BlockPerPlaceActual
end
