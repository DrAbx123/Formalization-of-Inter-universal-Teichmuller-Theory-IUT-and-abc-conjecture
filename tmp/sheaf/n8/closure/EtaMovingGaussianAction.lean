import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Analysis.Normed.Field.Basic

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaMovingGaussianAction

universe u

open scoped Padic
open Metric

/-! ## General scaling movement -/

/-- Actual scaling by a non-unit moves the unit sphere: `1` lies on the
sphere and its image is `g`, whose norm is not one. -/
theorem scaling_image_sphere_ne_of_norm_ne_one
    {K : Type u} [NormedField K] (g : K) (h : ‖g‖ ≠ 1) :
    (fun x : K => g * x) '' (Metric.sphere (0 : K) 1) ≠
      Metric.sphere (0 : K) 1 := by
  intro heq
  have hone : (1 : K) ∈ Metric.sphere (0 : K) 1 := by
    simp [Metric.mem_sphere]
  have hg_image : g * 1 ∈
      (fun x : K => g * x) '' (Metric.sphere (0 : K) 1) :=
    ⟨1, hone, rfl⟩
  have hg_sphere : g ∈ Metric.sphere (0 : K) 1 := by
    rw [← heq]
    simpa using hg_image
  have hnorm : ‖g‖ = 1 := by
    simpa [Metric.mem_sphere] using hg_sphere
  exact h hnorm

/-! ## Actual p-adic Gaussian action -/

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- Actual nonarchimedean Gaussian scalar `a^(j^2)` with `a = p`, the
actual uniformizer in `Q_p`. -/
def padicGaussianScalar (j : ℕ) : ℚ_[p] := (p : ℚ_[p]) ^ (j ^ 2)

/-- Actual unit-sphere region in `Q_p`. -/
def padicUnitSphere : Set ℚ_[p] := Metric.sphere (0 : ℚ_[p]) 1

/-- Actual Gaussian multiplication action on the unit-sphere region. -/
def padicGaussianAction (j : ℕ) :
    Set ℚ_[p] := (fun x : ℚ_[p] => padicGaussianScalar p j * x) ''
      padicUnitSphere p

theorem padicGaussianScalar_norm_lt_one (j : ℕ) (hj : j ≠ 0) :
    ‖padicGaussianScalar p j‖ < 1 := by
  have hbase_lt : ‖(p : ℚ_[p])‖ < 1 := Padic.norm_p_lt_one (p := p)
  have hbase_nonneg : 0 ≤ ‖(p : ℚ_[p])‖ := norm_nonneg _
  have hpow_lt : ‖(p : ℚ_[p])‖ ^ (j ^ 2) < 1 :=
    pow_lt_one₀ hbase_nonneg hbase_lt (pow_ne_zero 2 hj)
  rw [padicGaussianScalar, norm_pow]
  exact hpow_lt

theorem padicGaussianScalar_norm_ne_one (j : ℕ) (hj : j ≠ 0) :
    ‖padicGaussianScalar p j‖ ≠ 1 :=
  ne_of_lt (padicGaussianScalar_norm_lt_one p j hj)

/-- Actual movement: for any nonzero `j`, `a^(j^2)` maps the unit sphere
to a different region. -/
theorem padicGaussianAction_ne_unitSphere (j : ℕ) (hj : j ≠ 0) :
    padicGaussianAction p j ≠ padicUnitSphere p := by
  exact scaling_image_sphere_ne_of_norm_ne_one
    (padicGaussianScalar p j) (padicGaussianScalar_norm_ne_one p j hj)

/-! ## Source no-go condition -/

/-- Exact source condition for movement of the actual Gaussian action: the
Gaussian scalar must have norm different from one.  A norm-one scalar
preserves the unit sphere and gives no movement. -/
def GaussianScalarMovesSphere {K : Type u} [NormedField K] (g : K) : Prop :=
  ‖g‖ ≠ 1

theorem gaussianScalarMovesSphere_of_norm_ne_one
    {K : Type u} [NormedField K] (g : K) (h : ‖g‖ ≠ 1) :
    GaussianScalarMovesSphere g := h

theorem gaussian_action_moves_of_norm_ne_one
    {K : Type u} [NormedField K] (g : K) (h : ‖g‖ ≠ 1) :
    (fun x : K => g * x) '' (Metric.sphere (0 : K) 1) ≠
      Metric.sphere (0 : K) 1 :=
  scaling_image_sphere_ne_of_norm_ne_one g h

end LeanFormal.IUT.N8Closure.EtaMovingGaussianAction
