import tmp.sheaf.xif.paper.Mzk1S3137ThetaRawEqActual
import tmp.sheaf.xif.paper.Mzk1P7ThetaDegC3Actual
import tmp.sheaf.xif.paper.S3137C3LogShellPacketNormalizedLogVolumeActual

/-! P7 #7 (a)+(b): theta block log factor and packet normalized log-volume
in terms of the sum of actual local degrees from the field decomposition. -/
noncomputable section
open scoped BigOperators
open MeasureTheory MeasureTheory.Measure
namespace LeanFormal.IUT.XiFPaper.Mzk1P7ThetaDegWeightActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.Mzk1S3137ThetaRawEqActual
open LeanFormal.IUT.XiFPaper.Mzk1P7ThetaDegC3Actual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance weightMeasurableSpace : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance weightBorelSpace : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-- (a) The theta block log-p factor is `-(Σ actual local degrees) * log p`. -/
theorem thetaBlockLogFactor_eq_sum_localDegree
    {J : Type*} [Fintype J] (E : J → Type*)
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[C3.p] (E j)]
    [∀ j, FiniteDimensional ℚ_[C3.p] (E j)]
    [∀ j, Module.Free ℚ_[C3.p] (E j)] [∀ j, Module.Finite ℚ_[C3.p] (E j)]
    (e : C3LogShellTensorBlock C3 ≃ₐ[ℚ_[C3.p]] ((j : J) → E j)) :
    thetaBlockLogFactor C3 =
      -(((∑ j, Module.finrank ℚ_[C3.p] (E j)) : ℝ) * Real.log (C3.p : ℝ)) := by
  rw [thetaBlockLogFactor_eq, c3TensorBlockDimension_eq_sum_fieldProduct C3 E e]
  push_cast
  ring

/-- (b) The packet normalized log-volume uses the sum of actual local degrees
as its denominator. -/
theorem c3PacketNormalizedLogVolume_eq_sum_localDegree
    {J : Type*} [Fintype J] (E : J → Type*)
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[C3.p] (E j)]
    [∀ j, FiniteDimensional ℚ_[C3.p] (E j)]
    [∀ j, Module.Free ℚ_[C3.p] (E j)] [∀ j, Module.Finite ℚ_[C3.p] (E j)]
    (e : C3LogShellTensorBlock C3 ≃ₐ[ℚ_[C3.p]] ((j : J) → E j))
    (μ : Measure (C3LogShellTensorBlock C3))
    (S : Set (C3LogShellTensorBlock C3)) :
    c3PacketNormalizedLogVolume C3 μ S =
      Real.log (μ S).toReal / ((∑ j, Module.finrank ℚ_[C3.p] (E j) : ℕ) : ℝ) := by
  unfold c3PacketNormalizedLogVolume
  rw [c3TensorBlockDimension_eq_sum_fieldProduct C3 E e]

end LeanFormal.IUT.XiFPaper.Mzk1P7ThetaDegWeightActual
end