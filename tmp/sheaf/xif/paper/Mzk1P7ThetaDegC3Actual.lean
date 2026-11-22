import tmp.sheaf.xif.paper.S3137C3LogShellPacketNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! P7 #7 C3 specialization: block:Q_p dimension = sum of actual local
degrees in a field-product decomposition of the C3 tensor block. -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1P7ThetaDegC3Actual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

theorem c3TensorBlockDimension_eq_sum_fieldProduct
    {J : Type*} [Fintype J] (E : J → Type*)
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[C3.p] (E j)]
    [∀ j, FiniteDimensional ℚ_[C3.p] (E j)]
    [∀ j, Module.Free ℚ_[C3.p] (E j)] [∀ j, Module.Finite ℚ_[C3.p] (E j)]
    (e : C3LogShellTensorBlock C3 ≃ₐ[ℚ_[C3.p]] ((j : J) → E j)) :
    c3TensorBlockDimension C3 = ∑ j, Module.finrank ℚ_[C3.p] (E j) := by
  have hblock : c3TensorBlockDimension C3 =
      Module.finrank ℚ_[C3.p] (C3LogShellTensorBlock C3) := rfl
  rw [hblock, e.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]

end LeanFormal.IUT.XiFPaper.Mzk1P7ThetaDegC3Actual
end