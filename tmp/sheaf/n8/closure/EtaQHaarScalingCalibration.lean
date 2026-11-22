import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellHaarIndex
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

/-!
# ETA v2: local q Haar scaling calibration

At an actual local field K over Q_p, with additive Haar measure mu, d = [K:Q_p],
and the actual integer shell O = Integers K and log-shell I = integralLogShell:

- mu(q A) = m_K(q) * mu(A), m_K(q) = distribHaarChar K q;
- nu_O(q O) = log m_K(q) / d;
- nu_O(q I) = log m_K(q) / d + log(logShellIntegerIndex) / d;
- nu_I(q I) = log m_K(q) / d,

where nu_O is log-volume normalized by O and nu_I normalized by I.
The q norm/degree identification is kept separate: no fixed shell = ±q and no
scalar common-Real comparison is asserted.
-/

set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaQHaarScalingCalibration

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal Pointwise
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
  [IsUltrametricDist K] [ProperSpace K]
  [MeasurableSpace K] [BorelSpace K]
  {p : Nat} [Fact p.Prime] [NormedAlgebra ℚ_[p] K] [Module.Finite ℚ_[p] K]

/-- Actual local dimension d = [K : Q_p]. -/
def localDimension : Nat := Module.finrank ℚ_[p] K

def localDimensionReal : Real := (localDimension (K := K) (p := p) : Real)

theorem localDimension_pos : 0 < localDimension (K := K) (p := p) := by
  unfold localDimension
  exact Module.finrank_pos

theorem localDimensionReal_pos : 0 < localDimensionReal (K := K) (p := p) := by
  unfold localDimensionReal
  exact_mod_cast localDimension_pos (K := K) (p := p)

/-- Actual multiplicative Haar scaling factor m_K(q). -/
def mK (q : Kˣ) : Real := ((distribHaarChar K) q : Real)

theorem mK_pos (q : Kˣ) : 0 < mK (K := K) q := by
  unfold mK
  exact_mod_cast distribHaarChar_pos (A := K) (g := q)

/-- Local q-scaling of an additive Haar measure. -/
theorem measure_units_smul (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular]
    (q : Kˣ) (A : Set K) :
    μ (q • A) = ENNReal.ofReal (mK (K := K) q) * μ A := by
  have h := distribHaarChar_mul (A := K) μ q A
  rw [← h, mK, ENNReal.ofReal_coe_nnreal]

/-- Actual integral unit ball O = Integers K. -/
abbrev O (K : Type*) [NormedField K] [IsUltrametricDist K] : Set K := (Integers K : Set K)

/-- Actual log-shell I = integralLogShell. -/
abbrev I : Set K := (integralLogShell (K := K) (p := p) : Set K)

/-- q-scaling of O. -/
def qO (q : Kˣ) : Set K := q • O K

/-- q-scaling of the log-shell I. -/
def qI (q : Kˣ) : Set K := q • I (K := K) (p := p)

/-- O-normalized log-volume. -/
def nuO (μ : Measure K) (A : Set K) : Real :=
  (localDimensionReal (K := K) (p := p))⁻¹ *
    (Real.log (μ A).toReal - Real.log (μ (O K)).toReal)

/-- I-normalized log-volume. -/
def nuI (μ : Measure K) (A : Set K) : Real :=
  (localDimensionReal (K := K) (p := p))⁻¹ *
    (Real.log (μ A).toReal - Real.log (μ (I (K := K) (p := p))).toReal)

theorem measure_O_pos_lt_top (μ : Measure K) [μ.IsAddHaarMeasure] :
    0 < μ (O K) ∧ μ (O K) < ⊤ :=
  measure_localIntegers_pos_lt_top (K := K) μ

theorem measure_I_pos_lt_top (μ : Measure K) [μ.IsAddHaarMeasure] :
    0 < μ (I (K := K) (p := p)) ∧ μ (I (K := K) (p := p)) < ⊤ :=
  measure_integralLogShell_pos_lt_top (K := K) (p := p) μ

/-- mu(q O) = m_K(q) mu(O). -/
theorem measure_qO (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular]
    (q : Kˣ) :
    μ (qO (K := K) q) = ENNReal.ofReal (mK (K := K) q) * μ (O K) :=
  measure_units_smul (K := K) μ q (O K)

/-- mu(q I) = m_K(q) mu(I). -/
theorem measure_qI (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular]
    (q : Kˣ) :
    μ (qI (K := K) (p := p) q) =
      ENNReal.ofReal (mK (K := K) q) * μ (I (K := K) (p := p)) :=
  measure_units_smul (K := K) μ q (I (K := K) (p := p))

theorem measure_qO_toReal (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular]
    (q : Kˣ) :
    (μ (qO (K := K) q)).toReal = mK (K := K) q * (μ (O K)).toReal := by
  rw [measure_qO (K := K) μ q]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt (mK_pos (K := K) q))]

theorem measure_qI_toReal (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular]
    (q : Kˣ) :
    (μ (qI (K := K) (p := p) q)).toReal =
      mK (K := K) q * (μ (I (K := K) (p := p))).toReal := by
  rw [measure_qI (K := K) (p := p) μ q]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt (mK_pos (K := K) q))]

/-- Formula 1: nu_O(q O) = log m_K(q) / d. -/
theorem nuO_qO (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular]
    (q : Kˣ) :
    nuO (K := K) (p := p) μ (qO (K := K) q) =
      Real.log (mK (K := K) q) / localDimensionReal (K := K) (p := p) := by
  unfold nuO
  rw [measure_qO_toReal (K := K) μ q]
  have ho_pos : 0 < (μ (O K)).toReal :=
    ENNReal.toReal_pos (measure_O_pos_lt_top (K := K) μ).1.ne'
      (measure_O_pos_lt_top (K := K) μ).2.ne
  rw [Real.log_mul (mK_pos (K := K) q).ne' ho_pos.ne']
  field_simp [localDimensionReal_pos (K := K) (p := p).ne']
  ring


/-- The actual q norm readout, kept separate from the Haar scaling factor. -/
def qNormReadout (q : Kˣ) : Real := ‖(q : K)‖

theorem qNormReadout_pos (q : Kˣ) : 0 < qNormReadout (K := K) q :=
  norm_pos_iff.mpr (Units.ne_zero q)

/-- mu(I) = index * mu(O) in real masses. -/
theorem measure_I_toReal_eq_index_mul (μ : Measure K) [μ.IsAddHaarMeasure] :
    (μ (I (K := K) (p := p))).toReal =
      (logShellIntegerIndex (K := K) (p := p) : Real) * (μ (O K)).toReal := by
  rw [show I (K := K) (p := p) = (integralLogShell (K := K) (p := p) : Set K) from rfl]
  rw [measure_integralLogShell_eq_index_mul (K := K) (p := p) μ]
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]

theorem indexReal_pos : 0 < (logShellIntegerIndex (K := K) (p := p) : Real) := by
  exact_mod_cast logShellIntegerIndex_pos (K := K) (p := p)

theorem indexReal_ne_zero : (logShellIntegerIndex (K := K) (p := p) : Real) ≠ 0 :=
  (indexReal_pos (K := K) (p := p)).ne'

/-- Formula 2: nu_O(q I) = log m_K(q)/d + log(logShellIntegerIndex)/d. -/
theorem nuO_qI (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular]
    (q : Kˣ) :
    nuO (K := K) (p := p) μ (qI (K := K) (p := p) q) =
      Real.log (mK (K := K) q) / localDimensionReal (K := K) (p := p) +
        Real.log (logShellIntegerIndex (K := K) (p := p) : Real) /
          localDimensionReal (K := K) (p := p) := by
  unfold nuO
  rw [measure_qI_toReal (K := K) (p := p) μ q]
  rw [measure_I_toReal_eq_index_mul (K := K) (p := p) μ]
  have hm_pos : 0 < mK (K := K) q := mK_pos (K := K) q
  have hi_pos : 0 < (logShellIntegerIndex (K := K) (p := p) : Real) :=
    indexReal_pos (K := K) (p := p)
  have ho_pos : 0 < (μ (O K)).toReal :=
    ENNReal.toReal_pos (measure_O_pos_lt_top (K := K) μ).1.ne'
      (measure_O_pos_lt_top (K := K) μ).2.ne
  rw [Real.log_mul hm_pos.ne' (mul_pos hi_pos ho_pos).ne',
    Real.log_mul hi_pos.ne' ho_pos.ne']
  field_simp [(localDimensionReal_pos (K := K) (p := p)).ne']
  ring

/-- Formula 3: nu_I(q I) = log m_K(q)/d. -/
theorem nuI_qI (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular]
    (q : Kˣ) :
    nuI (K := K) (p := p) μ (qI (K := K) (p := p) q) =
      Real.log (mK (K := K) q) / localDimensionReal (K := K) (p := p) := by
  unfold nuI
  rw [measure_qI_toReal (K := K) (p := p) μ q]
  have hm_pos : 0 < mK (K := K) q := mK_pos (K := K) q
  have hi_pos : 0 < (μ (I (K := K) (p := p))).toReal :=
    ENNReal.toReal_pos (measure_I_pos_lt_top (K := K) (p := p) μ).1.ne'
      (measure_I_pos_lt_top (K := K) (p := p) μ).2.ne
  rw [Real.log_mul hm_pos.ne' hi_pos.ne']
  field_simp [(localDimensionReal_pos (K := K) (p := p)).ne']
  ring

end LeanFormal.IUT.N8Closure.EtaQHaarScalingCalibration
