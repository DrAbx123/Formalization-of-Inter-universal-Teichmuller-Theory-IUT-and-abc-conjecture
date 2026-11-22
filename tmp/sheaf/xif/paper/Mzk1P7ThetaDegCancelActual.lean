import tmp.sheaf.xif.paper.Mzk1P7ThetaDegWeightActual
import tmp.sheaf.xif.paper.S3137ThetaHullVolumeScalingActual
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual

/-! P7 #7 (c)+(d): raw normalized log-volume as `(Σ actual local degrees)^{-1}`
times the raw theta log-volume; final cancellation of the degree normalization. -/
noncomputable section
open scoped BigOperators
open MeasureTheory MeasureTheory.Measure
namespace LeanFormal.IUT.XiFPaper.Mzk1P7ThetaDegCancelActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.Mzk1S3137ThetaRawEqActual
open LeanFormal.IUT.XiFPaper.Mzk1P7ThetaDegWeightActual
open LeanFormal.IUT.XiFPaper.S3137ThetaHullVolumeScalingActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance cancelMeasurableSpace : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance cancelBorelSpace : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-- (d) The packet-normalized log-volume is the inverse-degree-sum times the
raw Haar log-volume. -/
theorem c3PacketNormalizedLogVolume_eq_inv_sumDegree_mul_log
    {J : Type*} [Fintype J] (E : J → Type*)
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[C3.p] (E j)]
    [∀ j, FiniteDimensional ℚ_[C3.p] (E j)]
    [∀ j, Module.Free ℚ_[C3.p] (E j)] [∀ j, Module.Finite ℚ_[C3.p] (E j)]
    (e : C3LogShellTensorBlock C3 ≃ₐ[ℚ_[C3.p]] ((j : J) → E j))
    (μ : Measure (C3LogShellTensorBlock C3))
    (S : Set (C3LogShellTensorBlock C3)) :
    c3PacketNormalizedLogVolume C3 μ S =
      (1 / (((∑ j, Module.finrank ℚ_[C3.p] (E j)) : ℕ) : ℝ)) *
        Real.log (μ S).toReal := by
  rw [c3PacketNormalizedLogVolume_eq_sum_localDegree C3 E e]
  rw [div_eq_inv_mul, one_div]

/-- (c) For the actual C3 log-shell tensor region, the normalized volume is the
inverse-degree-sum times the raw theta log-volume. -/
theorem c3PacketNormalizedLogVolume_actualRegion_eq_inv_sumDegree_mul_theta
    {J : Type*} [Fintype J] (E : J → Type*)
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[C3.p] (E j)]
    [∀ j, FiniteDimensional ℚ_[C3.p] (E j)]
    [∀ j, Module.Free ℚ_[C3.p] (E j)] [∀ j, Module.Finite ℚ_[C3.p] (E j)]
    (e : C3LogShellTensorBlock C3 ≃ₐ[ℚ_[C3.p]] ((j : J) → E j)) :
    c3PacketNormalizedLogVolume C3 (actualC3LogShellTensorHaar C3)
        (actualC3LogShellTensorRegion C3) =
      (1 / (((∑ j, Module.finrank ℚ_[C3.p] (E j)) : ℕ) : ℝ)) *
        thetaPilotHullLogVolumeReal C3 := by
  rw [c3PacketNormalizedLogVolume_eq_inv_sumDegree_mul_log C3 E e]
  rw [thetaRaw_eq_log_actualRegion]

end LeanFormal.IUT.XiFPaper.Mzk1P7ThetaDegCancelActual
end 