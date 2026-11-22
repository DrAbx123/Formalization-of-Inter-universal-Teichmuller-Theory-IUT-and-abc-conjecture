import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.S3137C3LogShellPacketNormalizedLogVolumeActual
import Mathlib.Tactic

/-! # A824 theta = V normalization alignment audit

Two different real numbers appear on the Theta side:
* `thetaPilotHullLogVolumeReal C3 = Real.log (actualC3LogShellTensorHaar C3
    (thetaPilotHull C3)).toReal` — the RAW Haar log-volume;
* `c3PacketNormalizedLogVolume C3 μ S = Real.log (μ S).toReal / [block : Q_p]`
  — the paper-normalized log-volume (IUT III, Prop 3.9(i) normalization).

They differ by the actual `Q_p`-dimension of the C3 tensor block:
`thetaPilotHullLogVolumeReal C3 = [block : Q_p] * c3PacketNormalizedLogVolume ...`.
Therefore identifying `thetaPilotHullLogVolumeReal` with paper `V` is NOT
definitional: one must either use the normalized quantity or prove the block
dimension is one (false in general).  The C3-vs-paper-D dictionary is a second,
separate gap. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaVAlignmentAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual

variable {l : PrimeGeFive} {V : Type} {I : LeanFormal.IUT.Theorem311Source.OriginalInput l V}
variable (C3 : LeanFormal.IUT.N8Closure.SourcePilotRegionData (l := l) (V := V) I)

/-- Paper-normalized Theta-side volume: raw Haar log divided by the actual
`Q_p`-dimension of the C3 tensor block. -/
noncomputable def paperVNormalized : Real :=
  c3PacketNormalizedLogVolume C3 (actualC3LogShellTensorHaar C3) (thetaPilotHull C3)

/-- Exact alignment: the raw theta reading is the block dimension times the
paper-normalized volume. -/
theorem thetaPilotHullLogVolumeReal_eq_dim_mul_normalized :
    thetaPilotHullLogVolumeReal C3 =
      (c3TensorBlockDimension C3 : Real) * paperVNormalized C3 := by
  unfold thetaPilotHullLogVolumeReal paperVNormalized
  unfold LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual.thetaPilotHull
  rw [LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual.thetaPilotHull_eq_region C3]
  unfold LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual.c3PacketNormalizedLogVolume
  have hdim : (c3TensorBlockDimension C3 : Real) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (c3TensorBlockDimension_pos (C3 := C3)))
  field_simp

/-- Consequently the raw reading equals the paper-normalized volume only when
the block dimension is one or the raw log-volume is zero. -/
theorem thetaV_eq_normalized_iff :
    thetaPilotHullLogVolumeReal C3 = paperVNormalized C3 ↔
      (c3TensorBlockDimension C3 : Real) = 1 ∨
        Real.log ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal = 0 := by
  have hdim : (c3TensorBlockDimension C3 : Real) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (c3TensorBlockDimension_pos (C3 := C3)))
  rw [thetaPilotHullLogVolumeReal_eq_dim_mul_normalized C3]
  unfold paperVNormalized
  unfold LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual.c3PacketNormalizedLogVolume
  constructor
  · intro h
    have hmult : ((c3TensorBlockDimension C3 : Real) - 1) *
        (Real.log ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal /
          (c3TensorBlockDimension C3 : Real)) = 0 := by
      field_simp [hdim] at h ⊢
      linarith
    rcases mul_eq_zero.mp hmult with h1 | h2
    · left; linarith
    · right
      have : Real.log ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal = 0 := by
        field_simp [hdim] at h2
        exact h2
      exact this
  · intro h
    rcases h with h1 | h2
    · rw [h1]; ring
    · rw [h2]; ring

structure ThetaVAlignmentRow where
  item : String
  formula : String
  status : String

def thetaVAlignmentRows : List ThetaVAlignmentRow :=
  [ { item := "raw theta reading", formula := "thetaPilotHullLogVolumeReal = log (haar(hull)).toReal", status := "GREEN (S3137)" },
    { item := "paper-normalized volume", formula := "log (haar(S)).toReal / [C3 block : Q_p]", status := "GREEN (S3137C3 normalized)" },
    { item := "exact alignment", formula := "raw = [block:Q_p] * normalized", status := "PROVED here" },
    { item := "paper V identification", formula := "thetaPilotHullLogVolumeReal = V", status := "MISSING: requires block dimension = 1 or zero log, plus C3-vs-D dictionary" },
    { item := "q-side identification", formula := "qPilotLogVolumeReading = -A, A = log q/(2l)", status := "MISSING: currently only -|log q|" },
    { item := "qTheta comparison", formula := "qPilotLogVolumeReading <= thetaPilotHullLogVolumeReal", status := "PENDING Audit obligation" } ]

def thetaVAlignmentMissing : List String :=
  [ "C3 block dimension [C3 block : Q_p] versus paper [T : Q_p] normalization",
    "C3 carrier versus paper D/global hull carrier",
    "q reading -|log q| versus paper -A = -log q/(2l)",
    "qTheta comparison Q_C <= H_C",
    "actual Haar positivity / finite measure hypotheses in normalization" ]

theorem thetaVAlignmentRows_length : thetaVAlignmentRows.length = 6 := rfl
theorem thetaVAlignmentMissing_length : thetaVAlignmentMissing.length = 5 := rfl

#print axioms thetaPilotHullLogVolumeReal_eq_dim_mul_normalized

end LeanFormal.IUT.XiFPaper.Mzk1ThetaVAlignmentAuditActual
