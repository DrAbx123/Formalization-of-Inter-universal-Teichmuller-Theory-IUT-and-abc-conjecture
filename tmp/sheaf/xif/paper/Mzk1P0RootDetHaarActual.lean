/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1RouteC0RootQLatticeActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic
/-! # P0.6 gap①/②: class-B root-extension det-Haar scaling and qhat scalar image -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0RootDetHaarActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open MeasureTheory
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
/-- Class-B external standard theorem on the actual root extension: Haar scales by
the norm of the determinant under a Qp-linear automorphism (image form). -/
def RootExtensionHaarDetScaling : Prop :=
  ∀ (mu : Measure (rootNormedExtension T b)) [Measure.IsAddHaarMeasure mu]
    (f : rootNormedExtension T b ≃ₗ[ℚ_[(qVFamTensorP T b)]]
      rootNormedExtension T b) (s : Set (rootNormedExtension T b)),
    mu (f '' s) =
      ENNReal.ofReal ‖(LinearMap.det (f : rootNormedExtension T b →ₗ[ℚ_[(qVFamTensorP T b)]]
        rootNormedExtension T b) : ℚ_[(qVFamTensorP T b)])‖ * mu s
theorem c0QHat_ne_zero : c0QHat T b ≠ 0 := by
  unfold c0QHat
  exact pow_ne_zero _ (c0Alpha_ne_zero T b)
/-- Multiplication by qhat as a Qp-linear automorphism. -/
noncomputable def rootMulQHatLinearEquiv :
    rootNormedExtension T b ≃ₗ[ℚ_[(qVFamTensorP T b)]] rootNormedExtension T b :=
  LinearEquiv.ofBijective
    (LinearMap.mulLeft ℚ_[(qVFamTensorP T b)] (c0QHat T b))
    (by
      constructor
      · intro x y h
        apply mul_left_cancel₀ (c0QHat_ne_zero T b)
        simpa using h
      · intro y
        refine ⟨y / c0QHat T b, ?_⟩
        field_simp [c0QHat_ne_zero T b])
theorem rootMulQHat_det :
    LinearMap.det ((rootMulQHatLinearEquiv T b :
      rootNormedExtension T b →ₗ[ℚ_[(qVFamTensorP T b)]] rootNormedExtension T b)) =
      (c0QHat T b) ^ Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) := by
  change LinearMap.det (LinearMap.mulLeft ℚ_[(qVFamTensorP T b)] (c0QHat T b)) =
    (c0QHat T b) ^ Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)
  simpa [LinearMap.mulLeft] using Algebra.det_lsmul (c0QHat T b)
theorem c0QLattice_image_eq :
    c0QLattice T b = (rootMulQHatLinearEquiv T b) '' c0UnitBall T b := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
/-- Block Haar scaling: mu(qhat*O_b) = ||qhat||^d * mu(O_b). -/
theorem c0QLattice_haar_eq
    (h : RootExtensionHaarDetScaling T b) :
    rootExtensionHaar T b (c0QLattice T b) =
      ENNReal.ofReal (‖c0QHat T b‖ ^
        Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)) *
        rootExtensionHaar T b (c0UnitBall T b) := by
  rw [c0QLattice_image_eq]
  rw [h (rootExtensionHaar T b) (rootMulQHatLinearEquiv T b) (c0UnitBall T b)]
  congr 1
  rw [rootMulQHat_det, norm_pow]
end LeanFormal.IUT.XiFPaper.Mzk1P0RootDetHaarActual
end
