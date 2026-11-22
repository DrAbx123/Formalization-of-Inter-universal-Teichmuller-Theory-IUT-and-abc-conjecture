import tmp.sheaf.n8.closure.EtaQHaarScalingCalibration
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicHaarScaling

/-!
# Eta Haar character / norm identification

At an actual finite extension K/Q_p:

- pUnit is the unit (p : Q_p) in K;
- mK(pUnit) = (p : R)^(-[K:Q_p]) is proved actually from the production
  finite-dimensional p-scaling theorem;
- the integral-unit case is proved from invariance of O = Integers K;
- the general identification mK(q) = ||q||^[K:Q_p] is recorded as an exact
  missing theorem (norm-one unit scaling via a uniformizer decomposition).

No arbitrary scaling factor is introduced.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaHaarCharNormIdentification

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal Pointwise
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.N8Closure.EtaQHaarScalingCalibration

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
  [IsUltrametricDist K] [ProperSpace K]
  [MeasurableSpace K] [BorelSpace K]
  {p : Nat} [Fact p.Prime] [NormedAlgebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

/-- The unit (p : Q_p) inside Kˣ. -/
def primeUnit : Kˣ :=
  Units.mk0 ((p : ℚ_[p]) • (1 : K)) (by
    have hp : (p : ℚ_[p]) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero
    exact smul_ne_zero hp one_ne_zero)

theorem primeUnit_smul_set (S : Set K) :
    primeUnit (K := K) (p := p) • S = (p : ℚ_[p]) • S := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by
      simp [primeUnit, Units.smul_def, smul_smul]⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by
      simp [primeUnit, Units.smul_def, smul_smul]⟩

/-- Actual p-scalar Haar character: mK(pUnit) = (p : NNReal)^(-d). -/
theorem distribHaarChar_primeUnit_eq :
    (distribHaarChar K) (primeUnit (K := K) (p := p)) =
      ((p : NNReal) ^ localDimension (K := K) (p := p))⁻¹ := by
  let r : NNReal := ((p : NNReal) ^ localDimension (K := K) (p := p))⁻¹
  have hmeasure :
      (Measure.addHaar : Measure K) (primeUnit (K := K) (p := p) • O K) =
        (r : ENNReal) * (Measure.addHaar : Measure K) (O K) := by
    rw [primeUnit_smul_set (K := K) (p := p)]
    rw [FinitePadicHaarScaling.measure_prime_smul_finiteDimensional
      (p := p) (M := K) (Measure.addHaar : Measure K) (O K)]
    rw [show ((p : ENNReal) ^ Module.finrank ℚ_[p] K)⁻¹ = (r : ENNReal) by
      unfold r localDimension
      have hp0 : (p : NNReal) ≠ 0 := by
        exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
      rw [ENNReal.coe_inv (pow_ne_zero _ hp0), ENNReal.coe_pow,
        ENNReal.coe_natCast]]
  have hO := measure_O_pos_lt_top (K := K) (Measure.addHaar : Measure K)
  have h := distribHaarChar_eq_of_measure_smul_eq_mul
    (A := K) (μ := (Measure.addHaar : Measure K))
    hO.1.ne' hO.2.ne hmeasure
  simpa [r] using h

/-- mK of the p-unit, as a real number. -/
theorem mK_primeUnit :
    mK (K := K) (primeUnit (K := K) (p := p)) =
      ((p : Real) ^ localDimension (K := K) (p := p))⁻¹ := by
  unfold mK
  rw [distribHaarChar_primeUnit_eq (K := K) (p := p)]
  rw [NNReal.coe_inv, NNReal.coe_pow, NNReal.coe_natCast]

/-- General identification target: mK(q) = ||q||^[K:Q_p]. -/
def HaarNormIdentificationTarget : Prop :=
  ∀ q : Kˣ, mK (K := K) q =
    (‖(q : K)‖ : Real) ^ localDimension (K := K) (p := p)

/-- The p-unit satisfies the general norm-power formula (actual). -/
theorem haarNorm_pUnit :
    mK (K := K) (primeUnit (K := K) (p := p)) =
      (‖((primeUnit (K := K) (p := p) : Kˣ) : K)‖ : Real) ^
        localDimension (K := K) (p := p) := by
  rw [mK_primeUnit (K := K) (p := p)]
  have hpnorm : ‖((p : ℚ_[p]) • (1 : K))‖ = (p : Real)⁻¹ := by
    rw [norm_smul, norm_one, mul_one]
    exact Padic.norm_p (p := p)
  have hunit : ((primeUnit (K := K) (p := p) : Kˣ) : K) =
      (p : ℚ_[p]) • (1 : K) := rfl
  rw [hunit, hpnorm, inv_pow]

end LeanFormal.IUT.N8Closure.EtaHaarCharNormIdentification
