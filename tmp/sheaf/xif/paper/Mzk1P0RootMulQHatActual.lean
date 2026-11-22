/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1RouteC0RootQLatticeActual
import tmp.sheaf.xif.paper.Mzk1P0RootCoordEquivActual
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic
/-! # P0.6: multiplication-by-qhat as a continuous linear automorphism and its determinant -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0RootMulQHatActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1P0RootCoordEquivActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [Fintype (Bad (nativePlaceSelection T))]
theorem c0QHat_ne_zero : c0QHat T b ≠ 0 := by
  unfold c0QHat
  exact pow_ne_zero _ (c0Alpha_ne_zero T b)
/-- Multiplication by qhat as a Qp-linear automorphism of the root extension. -/
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
/-- The same automorphism as a continuous linear equivalence. -/
noncomputable def rootMulQHatContinuousLinearEquiv :
    rootNormedExtension T b ≃L[ℚ_[(qVFamTensorP T b)]] rootNormedExtension T b :=
  (rootMulQHatLinearEquiv T b).toContinuousLinearEquiv
/-- The determinant of multiplication by qhat is qhat^d. -/
theorem rootMulQHat_det :
    LinearMap.det (rootMulQHatLinearEquiv T b : rootNormedExtension T b →ₗ[ℚ_[(qVFamTensorP T b)]] rootNormedExtension T b) =
      (c0QHat T b) ^ Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) := by
  change LinearMap.det (LinearMap.mulLeft ℚ_[(qVFamTensorP T b)] (c0QHat T b)) = _
  rw [show LinearMap.mulLeft ℚ_[(qVFamTensorP T b)] (c0QHat T b) =
      Algebra.lsmul ℚ_[(qVFamTensorP T b)] ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) (c0QHat T b) from rfl]
  exact Algebra.det_lsmul (c0QHat T b)
end LeanFormal.IUT.XiFPaper.Mzk1P0RootMulQHatActual
end
