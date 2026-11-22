/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S3137C3LogShellPacketNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import Mathlib.Tactic

/-! # P7 / #5: explicit raw θ read vs candidate packet-normalized V (factor [C3 block:Q_p]) -/

/-
| field | value |
|---|---|
| Status | PARTIAL: explicit formula chain `raw θ = [C3 block:Q_p] * candidateNormalizedV`, p-scaling both sides; paper normalized V exact identification remains GAP |
| Reuse | `S3137C3LogShellPacketNormalizedLogVolumeActual:54/64/75/87/95/114/126`（dimension, p-scaling, packetNormalized）; `S3137QThetaPilotLogVolumeReadingsActual:128/102`（raw theta read; hull=region） |
| GAP | GAP-P7-THETA-V: paper normalized V's actual definition/identification (ThetaVAlignmentAudit is not green) and C3-vs-D dictionary are missing; `[C3 block:Q_p] = Module.finrank ℚ_[p] block` is only a definition, not identified with paper local-degree factor |
| 纪律 | no sorry/axiom; no new assumptions; candidate normalized V is named as candidate, not paper |
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaRawPacketFactorActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open MeasureTheory
open scoped Pointwise ENNReal

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance thetaRawBlockMeasurableSpace :
    MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance thetaRawBlockBorelSpace :
    BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-- The raw θ Haar log-volume of the actual C3 log-shell tensor region. -/
noncomputable def rawThetaLogVolume : ℝ :=
  Real.log ((actualC3LogShellTensorHaar C3)
    (actualC3LogShellTensorRegion C3)).toReal

/-- It is definitionally the S3137 raw θ reading (hull = region). -/
theorem rawThetaLogVolume_eq_s3137 :
    rawThetaLogVolume C3 =
      LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual.thetaPilotHullLogVolumeReal
        C3 := by
  unfold rawThetaLogVolume
    LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual.thetaPilotHullLogVolumeReal
  rw [LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual.thetaPilotHull_eq_region]

/-- **Explicit formula chain**: raw θ read = `[C3 block : Q_p] * candidateNormalizedV`, where
`[C3 block : Q_p] = Module.finrank ℚ_[p] (C3LogShellTensorBlock C3)`
(`c3TensorBlockDimension`, `S3137C3…:54`), and the candidate normalized V is the
packet-normalized log-volume (`:87-90`). -/
theorem rawThetaLogVolume_eq_dim_mul_candidateNormalized
    (hdim : (c3TensorBlockDimension C3 : ℝ) ≠ 0) :
    rawThetaLogVolume C3 =
      (c3TensorBlockDimension C3 : ℝ) *
        c3PacketNormalizedLogVolume C3 (actualC3LogShellTensorHaar C3)
          (actualC3LogShellTensorRegion C3) := by
  unfold rawThetaLogVolume c3PacketNormalizedLogVolume
  field_simp [hdim]

/-- p-scaling of the raw θ read: shifts by `-[C3 block:Q_p]·log p`. -/
theorem rawThetaLogVolume_prime_smul
    (hpos : 0 < (actualC3LogShellTensorHaar C3)
      (actualC3LogShellTensorRegion C3)) :
    Real.log ((actualC3LogShellTensorHaar C3)
        ((C3.p : ℚ_[C3.p]) • actualC3LogShellTensorRegion C3)).toReal =
      rawThetaLogVolume C3 -
        (c3TensorBlockDimension C3 : ℝ) * Real.log (C3.p : ℝ) := by
  have h := c3Tensor_log_measure_prime_smul (C3 := C3)
    (actualC3LogShellTensorHaar C3) hpos
    (c3TensorRegion_measure_lt_top (C3 := C3))
  unfold rawThetaLogVolume
  linarith

/-- p-scaling of the candidate normalized V: shifts by `-log p`. -/
theorem candidateNormalized_prime_smul
    (hpos : 0 < (actualC3LogShellTensorHaar C3)
      (actualC3LogShellTensorRegion C3)) :
    c3PacketNormalizedLogVolume C3 (actualC3LogShellTensorHaar C3)
        ((C3.p : ℚ_[C3.p]) • actualC3LogShellTensorRegion C3) =
      -Real.log (C3.p : ℝ) +
        c3PacketNormalizedLogVolume C3 (actualC3LogShellTensorHaar C3)
          (actualC3LogShellTensorRegion C3) :=
  c3TensorRegion_packetNormalizedLogVolume_prime_smul (C3 := C3) hpos

def thetaRawPacketRows : List (String × String) :=
  [ ("rawThetaLogVolume", "raw θ Haar log = S3137 thetaPilotHullLogVolumeReal (hull=region)") ,
    ("rawThetaLogVolume_eq_dim_mul_candidateNormalized", "raw θ = [C3 block:Q_p] * packetNormalized (dim≠0)") ,
    ("rawThetaLogVolume_prime_smul", "raw θ p-shift = -dim*log p") ,
    ("candidateNormalized_prime_smul", "normalized p-shift = -log p") ,
    ("c3TensorBlockDimension", "[C3 block:Q_p] = Module.finrank ℚ_[p] (C3LogShellTensorBlock C3)") ,
    ("GAP-P7-THETA-V", "paper normalized V definition/C3-vs-D dictionary missing") ]

theorem thetaRawPacketRows_length : thetaRawPacketRows.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ThetaRawPacketFactorActual