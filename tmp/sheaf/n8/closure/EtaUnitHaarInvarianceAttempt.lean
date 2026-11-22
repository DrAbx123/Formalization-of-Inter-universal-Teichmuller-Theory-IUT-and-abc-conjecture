import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

/-!
# EtaUnitHaarInvarianceAttempt

Unit part of the general q Haar scaling, via the production distributive Haar
character (`Mathlib.MeasureTheory.Measure.Haar.DistribChar`).

Actual result: if a unit `u : Kˣ` fixes the production integral unit ball `O`,
then its additive-Haar scaling is `1`: `μ (u • S) = μ S`.  This is proved by
evaluating `distribHaarChar` on `O`: `char(u) * μ O = μ O`, hence `char(u)=1`,
then applying `distribHaarChar_mul` to `S`.

Missing theorem (uniformizer/e-th-root part): production does not identify
`distribHaarChar K π` with `ofReal (‖π‖ ^ f)` for a uniformizer π.  That exact
identification is stated below as the remaining source theorem; no arbitrary
invariance/factor is assumed.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaUnitHaarInvarianceAttempt

universe u

open MeasureTheory
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped NNReal Pointwise ENNReal

variable {K : Type*} [NormedField K] [LocallyCompactSpace K]
  [IsUltrametricDist K] [MeasurableSpace K] [BorelSpace K]

/-- Actual unit Haar invariance for a unit fixing the integral unit ball. -/
theorem unit_haar_invariance_of_fixes_integers
    (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular]
    (u : Kˣ) (hu : u • (Integers K : Set K) = (Integers K : Set K))
    (h0 : μ (Integers K : Set K) ≠ 0)
    (hfin : μ (Integers K : Set K) ≠ ∞)
    (S : Set K) : μ (u • S) = μ S := by
  have hchar : distribHaarChar K u = 1 := by
    apply ENNReal.coe_injective
    have hmul := distribHaarChar_mul (A := K) (μ := μ) u (Integers K : Set K)
    rw [hu] at hmul
    have h1 : (distribHaarChar K u : ENNReal) * μ (Integers K : Set K) =
        (1 : ENNReal) * μ (Integers K : Set K) := by
      simpa [ENNReal.coe_one] using hmul
    exact (ENNReal.mul_left_inj h0 hfin).mp h1
  have hmul := distribHaarChar_mul (A := K) (μ := μ) u S
  rw [hchar] at hmul
  simpa using hmul.symm

/-- Exact missing production theorem: the distributive Haar character of a
uniformizer equals the f-th power of its norm. -/
def UniformizerDistribHaarCharTarget (π : Kˣ) (f : ℕ) : Prop :=
  distribHaarChar K π = Real.toNNReal (‖(π : K)‖ ^ f)

end LeanFormal.IUT.N8Closure.EtaUnitHaarInvarianceAttempt