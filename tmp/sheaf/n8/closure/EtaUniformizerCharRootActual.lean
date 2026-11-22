import tmp.sheaf.n8.closure.EtaUniformizerHaarCharActual

/-!
# EtaUniformizerCharRootActual

From the actual root relation `char(π)^e = char(p)` and the p-step
normalization `char(p) = ‖p‖^d`, derive `char(π) = ‖π‖^d` by positive-root
uniqueness (assuming `π^e = p * u` with `u` norm-one and fixing `O`).

The derivation is actual algebra on the production distributive Haar character.
The p-step normalization `char(p) = ‖p‖^d` is kept as an explicit hypothesis
whose production proof would use `measure_prime_smul_finiteDimensional` plus
the norm of the rational prime; no arbitrary root is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaUniformizerCharRootActual

universe u

open MeasureTheory
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.N8Closure.EtaUnitHaarInvarianceAttempt
open LeanFormal.IUT.N8Closure.EtaUniformizerHaarCharActual
open scoped NNReal Pointwise ENNReal

variable {K : Type*} [NormedField K] [LocallyCompactSpace K]
  [IsUltrametricDist K] [MeasurableSpace K] [BorelSpace K]

/-- Positive-root uniqueness in `ℝ≥0`. -/
theorem NNReal.eq_of_pow_eq_of_pos {x y : ℝ≥0} {e : ℕ}
    (hx : 0 < x) (hy : 0 < y) (he : e ≠ 0)
    (h : x ^ e = y ^ e) : x = y := by
  apply NNReal.coe_injective
  apply (pow_left_inj₀ (show (0 : ℝ) ≤ (x : ℝ) from x.coe_nonneg)
    (show (0 : ℝ) ≤ (y : ℝ) from y.coe_nonneg) he).mp
  simpa using congrArg (fun z : ℝ≥0 => (z : ℝ)) h

/-- `Real.toNNReal` commutes with natural powers on nonnegative arguments. -/
theorem Real.toNNReal_pow' {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (Real.toNNReal x) ^ n = Real.toNNReal (x ^ n) := by
  apply NNReal.coe_injective
  simp [NNReal.coe_pow, Real.coe_toNNReal x hx,
    Real.coe_toNNReal (x ^ n) (pow_nonneg hx n)]

/-- Actual uniformizer character root: `char(π) = ‖π‖^d` from the p-step
normalization and the uniformizer relation. -/
theorem uniformizer_char_eq_norm_pow_d
    (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular]
    (π pU u : Kˣ) (e d : ℕ) (he : e ≠ 0)
    (hp : distribHaarChar K pU = Real.toNNReal ((‖(pU : K)‖) ^ d))
    (hrel : π ^ e = pU * u)
    (huO : u • (Integers K : Set K) = (Integers K : Set K))
    (hu_norm : ‖(u : K)‖ = 1)
    (h0 : μ (Integers K : Set K) ≠ 0)
    (hfin : μ (Integers K : Set K) ≠ ∞) :
    distribHaarChar K π = Real.toNNReal ((‖(π : K)‖) ^ d) := by
  have hchar_root : distribHaarChar K π ^ e = distribHaarChar K pU := by
    simpa using distribHaarChar_pow_eq_of_uniformizer_relation
      (K := K) μ π pU u e hrel huO h0 hfin
  have hrelK : ((π : K) ^ e) = (pU : K) * (u : K) := by
    simpa using congrArg (fun x : Kˣ => (x : K)) hrel
  have hnorm_root : ‖(π : K)‖ ^ e = ‖(pU : K)‖ := by
    rw [← norm_pow, hrelK, norm_mul, hu_norm, mul_one]
  have hπpos : 0 < ‖(π : K)‖ := norm_pos_iff.mpr (Units.ne_zero π)
  have hcharπ_pos : 0 < distribHaarChar K π := distribHaarChar_pos
  have htarget_pos : 0 < Real.toNNReal ((‖(π : K)‖) ^ d) := by
    rw [Real.toNNReal_pos]
    exact pow_pos hπpos d
  apply NNReal.eq_of_pow_eq_of_pos hcharπ_pos htarget_pos he
  rw [hchar_root, hp]
  have hpow : (‖(π : K)‖) ^ (e * d) = (‖(pU : K)‖) ^ d := by
    rw [← hnorm_root]
    rw [pow_mul]
  have hE : Real.toNNReal ((‖(pU : K)‖) ^ d) =
      Real.toNNReal (((‖(π : K)‖) ^ d) ^ e) := by
    rw [← hpow]
    congr 1
    rw [← pow_mul, Nat.mul_comm]
  rw [hE, ← Real.toNNReal_pow' (pow_nonneg hπpos.le d)]

end LeanFormal.IUT.N8Closure.EtaUniformizerCharRootActual
