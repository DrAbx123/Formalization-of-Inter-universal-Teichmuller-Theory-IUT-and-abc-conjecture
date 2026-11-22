import tmp.sheaf.n8.closure.EtaUnitHaarInvarianceAttempt

/-!
# EtaUniformizerHaarCharActual

Attempt at the uniformizer Haar character via the relation `π^e = p * u` and
multiplicativity of the production distributive Haar character.

Actual result: if `u` is a unit fixing the integral unit ball `O` (so its
Haar character is `1`) and `π^e = p * u`, then
`distribHaarChar K π ^ e = distribHaarChar K p`.

The remaining step is the exact missing evaluation of `distribHaarChar` in
terms of the norm (`UniformizerDistribHaarCharTarget`).  No arbitrary root or
factor is assumed.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaUniformizerHaarCharActual

universe u

open MeasureTheory
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.N8Closure.EtaUnitHaarInvarianceAttempt
open scoped NNReal Pointwise ENNReal

variable {K : Type*} [NormedField K] [LocallyCompactSpace K]
  [IsUltrametricDist K] [MeasurableSpace K] [BorelSpace K]

/-- Haar character of a unit fixing the integral unit ball is one. -/
theorem distribHaarChar_eq_one_of_fixes_integers
    (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular]
    (u : Kˣ) (hu : u • (Integers K : Set K) = (Integers K : Set K))
    (h0 : μ (Integers K : Set K) ≠ 0)
    (hfin : μ (Integers K : Set K) ≠ ∞) :
    distribHaarChar K u = 1 := by
  apply ENNReal.coe_injective
  have hmul := distribHaarChar_mul (A := K) (μ := μ) u (Integers K : Set K)
  rw [hu] at hmul
  have h1 : (distribHaarChar K u : ENNReal) * μ (Integers K : Set K) =
      (1 : ENNReal) * μ (Integers K : Set K) := by
    simpa [ENNReal.coe_one] using hmul
  exact (ENNReal.mul_left_inj h0 hfin).mp h1

/-- Actual root relation: `char(π)^e = char(p)` from `π^e = p * u` and a
unit `u` fixing `O`. -/
theorem distribHaarChar_pow_eq_of_uniformizer_relation
    (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular]
    (π p u : Kˣ) (e : ℕ) (hrel : π ^ e = p * u)
    (huO : u • (Integers K : Set K) = (Integers K : Set K))
    (h0 : μ (Integers K : Set K) ≠ 0)
    (hfin : μ (Integers K : Set K) ≠ ∞) :
    distribHaarChar K π ^ e = distribHaarChar K p := by
  rw [← map_pow, hrel, map_mul,
    distribHaarChar_eq_one_of_fixes_integers μ u huO h0 hfin, mul_one]

end LeanFormal.IUT.N8Closure.EtaUniformizerHaarCharActual