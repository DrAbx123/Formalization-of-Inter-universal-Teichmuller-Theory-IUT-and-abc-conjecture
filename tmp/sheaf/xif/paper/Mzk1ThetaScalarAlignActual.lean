/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P7ThetaDegCancelActual
import tmp.sheaf.xif.paper.Mzk1P7ThetaDegWeightActual
import tmp.sheaf.xif.paper.Mzk1P7ThetaDegC3Actual
import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual
import Mathlib.Tactic

/-! # P7/#1: #7-cancel scalar alignment for `theta_eq` (reduction, not fake) -/

/-
| field | value |
|---|---|
| Status | PROVED: `thetaPilotHullLogVolumeReal = (Σdeg)·c3PacketNormalizedLogVolume` (definitional via `c3PacketNormalizedLogVolume = log μ / dim`); `theta_eq` reduces to one scalar equation `(Σdeg)·packetNorm = s1915ClosedForm` |
| GAP | the reduced scalar equation is NOT a consequence of #7 (cancel theorem is definitional); it still needs the C3↔S1902 hull mass identification |
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaScalarAlignActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.Mzk1P7ThetaDegCancelActual
open LeanFormal.IUT.XiFPaper.Mzk1P7ThetaDegWeightActual
open LeanFormal.IUT.XiFPaper.Mzk1P7ThetaDegC3Actual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open MeasureTheory
open scoped ENNReal BigOperators

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Definitional identity: the raw theta log-volume is the block dimension times
the packet-normalized log-volume (because `c3PacketNormalizedLogVolume = log μ / dim`). -/
theorem thetaPilotHullLogVolumeReal_eq_dim_mul_packetNormalized :
    thetaPilotHullLogVolumeReal C3 =
      (c3TensorBlockDimension C3 : ℝ) *
        c3PacketNormalizedLogVolume C3 (actualC3LogShellTensorHaar C3) (thetaPilotHull C3) := by
  unfold c3PacketNormalizedLogVolume thetaPilotHullLogVolumeReal
  have hd : (c3TensorBlockDimension C3 : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (c3TensorBlockDimension_pos (C3 := C3)))
  field_simp [hd]

/-- With a field decomposition, the same identity with `Σ_j [E_j : Q_p]`. -/
theorem thetaPilotHullLogVolumeReal_eq_sumDegree_mul_packetNormalized
    {J : Type*} [Fintype J] (E : J → Type*)
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[C3.p] (E j)]
    [∀ j, FiniteDimensional ℚ_[C3.p] (E j)]
    [∀ j, Module.Free ℚ_[C3.p] (E j)] [∀ j, Module.Finite ℚ_[C3.p] (E j)]
    (e : C3LogShellTensorBlock C3 ≃ₐ[ℚ_[C3.p]] ((j : J) → E j)) :
    thetaPilotHullLogVolumeReal C3 =
      (((∑ j, Module.finrank ℚ_[C3.p] (E j) : ℕ) : ℝ)) *
        c3PacketNormalizedLogVolume C3 (actualC3LogShellTensorHaar C3) (thetaPilotHull C3) := by
  rw [thetaPilotHullLogVolumeReal_eq_dim_mul_packetNormalized C3]
  rw [c3TensorBlockDimension_eq_sum_fieldProduct C3 E e]

/-- **Reduction of `theta_eq`**: the dictionary field is equivalent to the single
scalar equation `(Σdeg)·packetNorm = s1915ClosedForm`. -/
theorem theta_eq_iff_sumDegree_mul_packetNormalized_eq
    {J : Type*} [Fintype J] (E : J → Type*)
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[C3.p] (E j)]
    [∀ j, FiniteDimensional ℚ_[C3.p] (E j)]
    [∀ j, Module.Free ℚ_[C3.p] (E j)] [∀ j, Module.Finite ℚ_[C3.p] (E j)]
    (e : C3LogShellTensorBlock C3 ≃ₐ[ℚ_[C3.p]] ((j : J) → E j)) :
    thetaPilotHullLogVolumeReal C3 = s1915ClosedForm T ↔
      ((∑ j, Module.finrank ℚ_[C3.p] (E j) : ℕ) : ℝ) *
        c3PacketNormalizedLogVolume C3 (actualC3LogShellTensorHaar C3) (thetaPilotHull C3) =
          s1915ClosedForm T := by
  rw [thetaPilotHullLogVolumeReal_eq_sumDegree_mul_packetNormalized C3 E e]

end LeanFormal.IUT.XiFPaper.Mzk1ThetaScalarAlignActual