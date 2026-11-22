import tmp.sheaf.n8.closure.EtaUnitHaarInvarianceAttempt
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicHaarScaling
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Analysis.Normed.Algebra.Basic
import tmp.sheaf.n8.closure.C3TensorTargetCorrection

/-!
# EtaPStepNormLink

Actual p-step normalization: for the rational-prime unit
`pU = algebraMap ℚ_[p] K p`, prove

  distribHaarChar K pU = toNNReal (‖pU‖ ^ d),   d = finrank ℚ_[p] K.

The Haar character side is the production p-scaling theorem
`measure_prime_smul_finiteDimensional` (factor `p^(-d)`).  The norm side is
the production norm formula for the rational prime (`norm_algebraMap'` plus
`Padic.norm_p`).  No arbitrary factor or link is assumed.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaPStepNormLink

universe u

open MeasureTheory
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped NNReal Pointwise ENNReal

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {K : Type u} [NormedField K] [NormedAlgebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K] [LocallyCompactSpace K] [IsUltrametricDist K]
  [MeasurableSpace K] [BorelSpace K]

local notation "d" => Module.finrank ℚ_[p] K

/-- The rational-prime unit in `K`. -/
noncomputable def pUnit : Kˣ :=
  Units.mk0 (algebraMap ℚ_[p] K (p : ℚ_[p])) (by
    have hnorm : ‖algebraMap ℚ_[p] K (p : ℚ_[p])‖ = ‖(p : ℚ_[p])‖ := by
      simpa using norm_algebraMap' K (p : ℚ_[p])
    rw [← norm_ne_zero_iff, hnorm, Padic.norm_p]
    exact inv_ne_zero (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero))

theorem pUnit_coe : (pUnit (p := p) (K := K) : K) =
    algebraMap ℚ_[p] K (p : ℚ_[p]) := rfl

/-- Actual p-step normalization of the distributive Haar character. -/
theorem distribHaarChar_pUnit_eq_toNNReal_norm_pow
    (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular]
    (h0 : μ (Integers K : Set K) ≠ 0)
    (hfin : μ (Integers K : Set K) ≠ ∞) :
    distribHaarChar K (pUnit (p := p) (K := K)) =
      Real.toNNReal (‖((pUnit (p := p) (K := K)) : K)‖ ^ d) := by
  have hscale := FinitePadicHaarScaling.measure_prime_smul_finiteDimensional
    (p := p) (M := K) μ (Integers K : Set K)
  have hact : (pUnit (p := p) (K := K)) • (Integers K : Set K) =
      (p : ℚ_[p]) • (Integers K : Set K) := by
    ext x
    simp only [Set.mem_smul_set, Units.smul_def, pUnit_coe, Algebra.smul_def,
      Algebra.algebraMap_self_apply]
  have hscale' : μ ((pUnit (p := p) (K := K)) • (Integers K : Set K)) =
      (((p : ℝ≥0) ^ d)⁻¹ : ℝ≥0) * μ (Integers K : Set K) := by
    rw [hact, hscale]
    congr 1
    rw [ENNReal.coe_inv (pow_ne_zero d (by
      exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)),
      ENNReal.coe_pow, ENNReal.coe_natCast]
  have hchar : distribHaarChar K (pUnit (p := p) (K := K)) =
      ((p : ℝ≥0) ^ d)⁻¹ := by
    exact distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) h0 hfin hscale'
  have hnorm : ‖((pUnit (p := p) (K := K)) : K)‖ = (p : ℝ)⁻¹ := by
    rw [pUnit_coe]
    have hnormp : ‖algebraMap ℚ_[p] K (p : ℚ_[p])‖ = ‖(p : ℚ_[p])‖ := by
      simpa using norm_algebraMap' K (p : ℚ_[p])
    rw [hnormp, Padic.norm_p]
  rw [hchar, hnorm]
  apply NNReal.coe_injective
  rw [NNReal.coe_inv, NNReal.coe_pow, NNReal.coe_natCast,
    Real.coe_toNNReal _ (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p)) d),
    inv_pow]

section NativeSpecialization

open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The actual native F-place completion as a Q_p-local field. -/
abbrev NativePCompletion (X : N8NativeInput l) : Type :=
  CommonPrimeCompletion (nativeFPlaceAtPrime X)

local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

noncomputable instance nativePMeasurableSpace : MeasurableSpace (NativePCompletion X) :=
  borel (NativePCompletion X)

instance nativePBorelSpace : BorelSpace (NativePCompletion X) := ⟨rfl⟩

/-- Actual p-step normalization at the native F-place completion. -/
theorem distribHaarChar_nativePUnit_eq_toNNReal_norm_pow
    (μ : Measure (NativePCompletion X)) [μ.IsAddHaarMeasure] [μ.Regular]
    (h0 : μ (Integers (NativePCompletion X) : Set (NativePCompletion X)) ≠ 0)
    (hfin : μ (Integers (NativePCompletion X) : Set (NativePCompletion X)) ≠ ∞) :
    distribHaarChar (NativePCompletion X)
        (pUnit (p := nativePrime X) (K := NativePCompletion X)) =
      Real.toNNReal (‖((pUnit (p := nativePrime X) (K := NativePCompletion X)) :
        NativePCompletion X)‖ ^ Module.finrank ℚ_[nativePrime X] (NativePCompletion X)) :=
  distribHaarChar_pUnit_eq_toNNReal_norm_pow
    (p := nativePrime X) (K := NativePCompletion X) μ h0 hfin

end NativeSpecialization

end LeanFormal.IUT.N8Closure.EtaPStepNormLink