import LeanFormal.IUT.IUTI.InitialTheta.SourceTorsionCarrierReduction
import Mathlib.RepresentationTheory.Basic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1S1LargeImageActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource.TorsionCarrierReduction
open scoped Classical

variable {F : Type*} [Field F]
variable (X : PuncturedEllipticCurve F) (l : PrimeGeFive)

/-- Exact interface for the S1 large-image input; the Serre-style statement is the
actual source condition, not a theorem derived from weak data. -/
structure S1LargeImageSource where
  serre_style : SerreStyleLargeImageStatement X l

def S1LargeImageRequired : Prop :=
  Nonempty (S1LargeImageSource X l)

theorem largeImageContainsSL2_iff (h : S1LargeImageSource X l) :
    ∃ basis : (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] X.LTorsion l,
      LargeImageContainsSL2 (X.galoisLTorsionMatrixRepresentation l basis) := by
  obtain ⟨basis, hbasis⟩ := h.serre_style
  refine ⟨basis, ?_⟩
  rw [← largeImageSL2_iff_forall]
  exact hbasis

end LeanFormal.IUT.XiFPaper.Mzk1S1LargeImageActual
end
