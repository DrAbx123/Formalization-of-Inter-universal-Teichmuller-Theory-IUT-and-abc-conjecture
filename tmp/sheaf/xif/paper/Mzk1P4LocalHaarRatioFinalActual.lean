/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicHaarScaling
import Mathlib.Tactic
/-! # P4: iterated p-scaling and conditional local Haar ratio -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P4LocalHaarRatioFinalActual
open MeasureTheory
open scoped ENNReal Pointwise
variable {p : Nat} [Fact p.Prime] {K : Type*}
variable [NormedField K] [NormedAlgebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable [MeasurableSpace K] [BorelSpace K]
/-- Iterated p-scaling of an additive Haar measure. -/
theorem measure_prime_pow_smul (μ : Measure K) [Measure.IsAddHaarMeasure μ]
    (n : Nat) (S : Set K) :
    μ (((p : ℚ_[p]) ^ n) • S) =
      ((p : ENNReal) ^ (Module.finrank ℚ_[p] K * n))⁻¹ * μ S := by
  induction n generalizing S with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ', mul_smul]
      rw [LeanFormal.IUT.FinitePadicHaarScaling.measure_prime_smul_finiteDimensional]
      rw [ih]
      rw [Nat.mul_succ, pow_add, pow_mul]
      rw [← mul_assoc]
      rw [ENNReal.mul_inv]
      · ring
      all_goals
        first
        | exact Or.inl (pow_ne_zero (Module.finrank ℚ_[p] K) (by
            exact_mod_cast (Fact.out : Nat.Prime p).ne_zero))
        | exact Or.inl (ENNReal.pow_ne_top
            (ENNReal.pow_ne_top (ENNReal.natCast_ne_top p)) (n := n))
        | exact Or.inl (ENNReal.pow_ne_top (ENNReal.natCast_ne_top p))
        | exact Or.inr (pow_ne_zero (Module.finrank ℚ_[p] K) (by
            exact_mod_cast (Fact.out : Nat.Prime p).ne_zero))
        | exact Or.inr (ENNReal.pow_ne_top (ENNReal.natCast_ne_top p))
/-- Conditional local Haar ratio: a = (p^n • 1) * u with u preserving O. -/
theorem local_haar_ratio_of_decomposition
    (μ : Measure K) [Measure.IsAddHaarMeasure μ]
    (O : Set K) (n : Nat) (u : K) (a : K)
    (ha : a = ((p : ℚ_[p]) ^ n • (1 : K)) * u)
    (hu : (fun x : K => u * x) '' O = O) :
    μ ((fun x : K => a * x) '' O) =
      ((p : ENNReal) ^ (Module.finrank ℚ_[p] K * n))⁻¹ * μ O := by
  rw [ha]
  rw [show (fun x : K => (((p : ℚ_[p]) ^ n • (1 : K)) * u) * x) '' O =
      (fun x : K => (p : ℚ_[p]) ^ n • x) '' ((fun x : K => u * x) '' O) by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨u * x, ⟨x, hx, rfl⟩, ?_⟩
      simp only [Algebra.smul_def, mul_assoc]
      ring
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      simp only [Algebra.smul_def, mul_assoc]
      ring]
  rw [hu]
  change μ ((p : ℚ_[p]) ^ n • O) = _
  exact measure_prime_pow_smul μ n O
#check local_haar_ratio_of_decomposition
end LeanFormal.IUT.XiFPaper.Mzk1P4LocalHaarRatioFinalActual
end
