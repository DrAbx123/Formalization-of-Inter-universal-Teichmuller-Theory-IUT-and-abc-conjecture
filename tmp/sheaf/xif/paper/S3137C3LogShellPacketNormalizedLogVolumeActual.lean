import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicHaarScaling
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorNontrivial

/-!
# S3137: p-adic normalization of the actual C3 log-shell tensor packet

IUT III, Proposition 3.9, (i) (p. 115): the p_v-adic log-volume on the local
holomorphic packets is normalized so that multiplication by p_v corresponds to
adding -log(p_v); IUT III, Proposition 1.2, (iii) (p. 31), is the matching
compatibility of the log-link with log-volumes.

The actual C3 tensor packet of local log-shells (C3LogShellTensorPacketActual)
carries the actual compact tensor region, its actual additive Haar measure and
its Haar log-volume.  This file proves at that actual carrier, with no new
carrier and no surrogate (the block is the actual finite p-adic tensor of the
actual completions at the selected C3 tensor places): the actual Haar
p-scaling law for every region of the block, its logarithmic form, and its
specialization to the actual C3 log-shell tensor region (whose Haar finiteness
is proved from compactness; positivity remains an ordinary hypothesis).

No sorry, no axiom, no True/PUnit.  WRITE-ONLY; no local compile.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open MeasureTheory
open scoped Pointwise ENNReal

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance c3PacketBlockMeasurableSpace :
    MeasurableSpace (C3LogShellTensorBlock C3) := borel _

local instance c3PacketBlockBorelSpace :
    BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-- The actual Q_p-dimension of the C3 log-shell tensor block. -/
noncomputable def c3TensorBlockDimension : ℕ :=
  Module.finrank ℚ_[C3.p] (C3LogShellTensorBlock C3)

/-- The actual Q_p-dimension of the C3 tensor block is positive. -/
theorem c3TensorBlockDimension_pos : 0 < c3TensorBlockDimension C3 := by
  unfold c3TensorBlockDimension
  exact Module.finrank_pos

/-- IUT III, Proposition 3.9, (i): the actual Haar measure of the p-scaled region
of the C3 log-shell tensor block is p^{-[block : Q_p]} times the original. -/
theorem c3Tensor_measure_prime_smul
    (μ : Measure (C3LogShellTensorBlock C3)) [Measure.IsAddHaarMeasure μ]
    (S : Set (C3LogShellTensorBlock C3)) :
    μ ((C3.p : ℚ_[C3.p]) • S) =
      ((C3.p : ENNReal) ^ c3TensorBlockDimension C3)⁻¹ * μ S := by
  unfold c3TensorBlockDimension
  exact FinitePadicHaarScaling.measure_prime_smul_finiteDimensional
    (M := C3LogShellTensorBlock C3) (p := C3.p) μ S

/-- The logarithmic form of the actual p-scaling law on the C3 log-shell tensor
block: multiplication by p shifts the Haar log-volume by -[block : Q_p] log p. -/
theorem c3Tensor_log_measure_prime_smul
    (μ : Measure (C3LogShellTensorBlock C3)) [Measure.IsAddHaarMeasure μ]
    {S : Set (C3LogShellTensorBlock C3)} (hpos : 0 < μ S) (hfin : μ S < ⊤) :
    Real.log (μ ((C3.p : ℚ_[C3.p]) • S)).toReal =
      -(c3TensorBlockDimension C3 : ℝ) * Real.log (C3.p : ℝ) +
        Real.log (μ S).toReal := by
  unfold c3TensorBlockDimension
  exact FinitePadicHaarScaling.log_measure_prime_smul_finiteDimensional
    (M := C3LogShellTensorBlock C3) (p := C3.p) μ hpos hfin

/-- The actual p-adic normalized log-volume of a region of the C3 log-shell
tensor packet: the Haar log-volume divided by the actual Q_p-dimension. -/
noncomputable def c3PacketNormalizedLogVolume
    (μ : Measure (C3LogShellTensorBlock C3))
    (S : Set (C3LogShellTensorBlock C3)) : ℝ :=
  Real.log (μ S).toReal / (c3TensorBlockDimension C3 : ℝ)

/-- The packet-normalized log-volume of the C3 log-shell tensor packet shifts by
exactly -log p under multiplication by p: the packet normalization of
IUT III, Proposition 3.9, (i), at the actual C3 carrier. -/
theorem c3PacketNormalizedLogVolume_prime_smul
    (μ : Measure (C3LogShellTensorBlock C3)) [Measure.IsAddHaarMeasure μ]
    {S : Set (C3LogShellTensorBlock C3)} (hpos : 0 < μ S) (hfin : μ S < ⊤) :
    c3PacketNormalizedLogVolume C3 μ ((C3.p : ℚ_[C3.p]) • S) =
      -Real.log (C3.p : ℝ) + c3PacketNormalizedLogVolume C3 μ S := by
  have hdim : (c3TensorBlockDimension C3 : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (c3TensorBlockDimension_pos (C3 := C3)))
  have hlog := c3Tensor_log_measure_prime_smul (C3 := C3) μ hpos hfin
  unfold c3PacketNormalizedLogVolume
  rw [hlog]
  field_simp
/-- The actual C3 log-shell tensor region has finite Haar measure: it is a
compact subset of the locally compact actual tensor block. -/
theorem c3TensorRegion_measure_lt_top :
    (actualC3LogShellTensorHaar C3) (actualC3LogShellTensorRegion C3) < ⊤ :=
  IsCompact.measure_lt_top (actualC3LogShellTensorRegion_compact C3)

/-- The p-scaling law specialized to the actual C3 log-shell tensor region, with
finiteness proved from compactness and positivity as the one hypothesis. -/
theorem c3TensorRegion_measure_prime_smul
    (hpos : 0 < (actualC3LogShellTensorHaar C3) (actualC3LogShellTensorRegion C3)) :
    Real.log ((actualC3LogShellTensorHaar C3)
        ((C3.p : ℚ_[C3.p]) • actualC3LogShellTensorRegion C3)).toReal =
      -(c3TensorBlockDimension C3 : ℝ) * Real.log (C3.p : ℝ) +
        Real.log ((actualC3LogShellTensorHaar C3)
          (actualC3LogShellTensorRegion C3)).toReal :=
  c3Tensor_log_measure_prime_smul (C3 := C3) (actualC3LogShellTensorHaar C3)
    hpos (c3TensorRegion_measure_lt_top (C3 := C3))

/-- The packet-normalized log-volume p-scaling on the actual C3 log-shell tensor
region (positivity is the one ordinary hypothesis; finiteness is proved). -/
theorem c3TensorRegion_packetNormalizedLogVolume_prime_smul
    (hpos : 0 < (actualC3LogShellTensorHaar C3) (actualC3LogShellTensorRegion C3)) :
    c3PacketNormalizedLogVolume C3 (actualC3LogShellTensorHaar C3)
        ((C3.p : ℚ_[C3.p]) • actualC3LogShellTensorRegion C3) =
      -Real.log (C3.p : ℝ) +
        c3PacketNormalizedLogVolume C3 (actualC3LogShellTensorHaar C3)
          (actualC3LogShellTensorRegion C3) :=
  c3PacketNormalizedLogVolume_prime_smul (C3 := C3)
    (actualC3LogShellTensorHaar C3) hpos (c3TensorRegion_measure_lt_top (C3 := C3))
end LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual