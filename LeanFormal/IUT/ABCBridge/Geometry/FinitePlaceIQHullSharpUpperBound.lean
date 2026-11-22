import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterfaceScaledUnit
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompactHullScaling
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Group.Measure

/-!
# Explicit Haar-log upper bound for the canonical hull

This file gives an explicit Haar-log upper bound for the actual canonical hull
`arithmeticTupleCanonicalHull` relative to the genuine scaled integral unit
region `lambda • O` of `FinitePlaceIQHullInterfaceScaledUnit.lean`.  The bound
is not a self-certification through the hull volume: the right-hand side is the
log-volume of the strictly larger scaled unit region, and the hull enters only
through the proved inclusion `hull ⊆ lambda • O` and monotonicity of the Haar
log-volume.

Main objects:

* `arithmeticTupleIQHullUnitRegion` is the concrete region
  `lambda • arithmeticTupleCanonicalUnitReference`, where `lambda` is the
  nonzero compactness-to-scaling scalar;
* `arithmeticTupleIQHullUnitLogTheta` is the normalized log-volume
  `log (mu unitRegion).toReal`;
* `arithmeticTupleIQHull_hull_logVolume_le_unitRegion` is the bound
  `haarLogVolume mu hull ≤ ofReal theta`.

## Normalization caveat

`theta` is not nonnegative for an arbitrary additive Haar measure: an additive
Haar measure is determined only up to a positive scalar, so `mu unitRegion` can
be any positive real number.  The lemma
`arithmeticTupleIQHullUnitLogTheta_nonneg` therefore assumes the normalization
`1 ≤ (mu unitRegion).toReal`, and
`exists_normalized_addHaar_arithmeticTupleIQHullUnitRegion` shows that every
additive Haar measure can be rescaled to one with `nu unitRegion = 1`, for which
`theta = 0`.  This is the paper's convention that the unit region carries
log-volume zero.

## Boundary

Everything is stated on the actual finite-place arithmetic tensor carrier.  No
identification with the source `1,circ U` carrier is claimed, and no O-module
equality between the hull and the scaled unit region is asserted.  The bound is
explicit but is not claimed to be optimal.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open MeasureTheory
open scoped Pointwise

noncomputable section

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)

variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]

/-! ## 1. The scaled integral unit region and its mass -/

/-- The scaled integral unit region `lambda • O` of the scaled-unit IQ hull
interface.  The scalar is the nonzero value supplied by the
compactness-to-scaling theorem for the actual canonical hull. -/
def arithmeticTupleIQHullUnitRegion :
    Set (ArithmeticTensorTupleBlock places tuple) :=
  arithmeticTupleIQHullUnitScale places tuple •
    arithmeticTupleCanonicalUnitReference places tuple

/-- The scaled unit region has positive Haar mass. -/
theorem arithmeticTupleIQHullUnitRegion_measure_pos
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    0 < μ (arithmeticTupleIQHullUnitRegion places tuple) :=
  (measure_smul_arithmeticTupleCanonicalUnitReference_pos_lt_top places tuple μ
    (arithmeticTupleIQHullUnitScale places tuple)
    (arithmeticTupleIQHullUnitScale_ne_zero places tuple)).1

/-- The scaled unit region has finite Haar mass. -/
theorem arithmeticTupleIQHullUnitRegion_measure_lt_top
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    μ (arithmeticTupleIQHullUnitRegion places tuple) < ⊤ :=
  (measure_smul_arithmeticTupleCanonicalUnitReference_pos_lt_top places tuple μ
    (arithmeticTupleIQHullUnitScale places tuple)
    (arithmeticTupleIQHullUnitScale_ne_zero places tuple)).2

/-- The scaled unit region does not have zero Haar mass. -/
theorem arithmeticTupleIQHullUnitRegion_measure_ne_zero
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    μ (arithmeticTupleIQHullUnitRegion places tuple) ≠ 0 :=
  (arithmeticTupleIQHullUnitRegion_measure_pos places tuple μ).ne'

/-- The scaled unit region does not have infinite Haar mass. -/
theorem arithmeticTupleIQHullUnitRegion_measure_ne_top
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    μ (arithmeticTupleIQHullUnitRegion places tuple) ≠ ⊤ :=
  (arithmeticTupleIQHullUnitRegion_measure_lt_top places tuple μ).ne

/-- The real-valued Haar mass of the scaled unit region is positive. -/
theorem arithmeticTupleIQHullUnitRegion_measure_toReal_pos
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    0 < (μ (arithmeticTupleIQHullUnitRegion places tuple)).toReal :=
  ENNReal.toReal_pos
    (arithmeticTupleIQHullUnitRegion_measure_ne_zero places tuple μ)
    (arithmeticTupleIQHullUnitRegion_measure_ne_top places tuple μ)

/-! ## 2. The normalized log-volume `theta` of the unit region -/

/-- The normalized log-volume `log (mu unitRegion).toReal` of the scaled
integral unit region.  This is the `theta` consumed by the `hθ` slot of
`CertificateHullWiring.iqHullCertificate`. -/
def arithmeticTupleIQHullUnitLogTheta
    (μ : Measure (ArithmeticTensorTupleBlock places tuple)) : ℝ :=
  Real.log (μ (arithmeticTupleIQHullUnitRegion places tuple)).toReal

omit [BorelSpace (ArithmeticTensorTupleBlock places tuple)] in
/-- Nonnegativity of `theta` under the normalization `1 ≤ mu unitRegion`.

This hypothesis is necessary: rescaling an additive Haar measure rescales the
mass of the unit region by an arbitrary positive factor, so `theta` has no
fixed sign without a normalization of the Haar measure. -/
theorem arithmeticTupleIQHullUnitLogTheta_nonneg
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    (hunit : 1 ≤ (μ (arithmeticTupleIQHullUnitRegion places tuple)).toReal) :
    0 ≤ arithmeticTupleIQHullUnitLogTheta places tuple μ :=
  Real.log_nonneg hunit

omit [BorelSpace (ArithmeticTensorTupleBlock places tuple)] in
/-- If the scaled unit region has mass one, then `theta` vanishes. -/
theorem arithmeticTupleIQHullUnitLogTheta_eq_zero_of_measure_eq_one
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    (hunit : μ (arithmeticTupleIQHullUnitRegion places tuple) = 1) :
    arithmeticTupleIQHullUnitLogTheta places tuple μ = 0 := by
  simp [arithmeticTupleIQHullUnitLogTheta, hunit]

/-! ## 3. The hull bound -/

omit [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
  [BorelSpace (ArithmeticTensorTupleBlock places tuple)] in
/-- The actual canonical hull is contained in the scaled integral unit region. -/
theorem arithmeticTupleCanonicalHull_subset_IQHullUnitRegion :
    arithmeticTupleCanonicalHull places tuple ⊆
      arithmeticTupleIQHullUnitRegion places tuple :=
  arithmeticTupleCanonicalHull_subset_IQHullUnitScale_smul_unitReference places tuple

/-- **Explicit Haar-log upper bound.**  The log-volume of the actual canonical
hull is at most the log-volume of the genuine scaled integral unit region
`lambda • O` that contains it.  Both the hull and the unit region have finite
Haar mass, so the right-hand side is a finite real log-volume and not the
self-referential hull volume. -/
theorem arithmeticTupleIQHull_hull_logVolume_le_unitRegion
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    haarLogVolume μ (arithmeticTupleCanonicalHull places tuple) ≤
      ENNReal.ofReal (arithmeticTupleIQHullUnitLogTheta places tuple μ) := by
  calc
    haarLogVolume μ (arithmeticTupleCanonicalHull places tuple)
        ≤ haarLogVolume μ (arithmeticTupleIQHullUnitRegion places tuple) :=
          haarLogVolume_mono
            (arithmeticTupleCanonicalHull_subset_IQHullUnitRegion places tuple)
    _ = ENNReal.ofReal (arithmeticTupleIQHullUnitLogTheta places tuple μ) := by
          rw [haarLogVolume_of_lt_top
            (arithmeticTupleIQHullUnitRegion_measure_lt_top places tuple μ)]
          rfl

/-- The bound stated for the scaled-unit `IQHullLogVolumeInterface` instance
itself.  Its hull log-volume is at most `ENNReal.ofReal theta`, which provides a
nonvacuous input for the `hθ` slot of `CertificateHullWiring.iqHullCertificate`
once `0 ≤ theta` is supplied by a normalization of the Haar measure. -/
theorem arithmeticTupleIQHullLogVolumeInterfaceScaledUnit_hull_logVolume_le_theta
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit places tuple μ).logVolume
        (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit places tuple μ).hull ≤
      ENNReal.ofReal (arithmeticTupleIQHullUnitLogTheta places tuple μ) := by
  simpa [arithmeticTupleIQHullLogVolumeInterfaceScaledUnit]
    using arithmeticTupleIQHull_hull_logVolume_le_unitRegion places tuple μ

/-! ## 4. Normalization of the additive Haar measure -/

/-- Every additive Haar measure can be rescaled so that the scaled integral
unit region has mass exactly one. -/
theorem exists_normalized_addHaar_arithmeticTupleIQHullUnitRegion
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    ∃ ν : Measure (ArithmeticTensorTupleBlock places tuple),
      Measure.IsAddHaarMeasure ν ∧
        ν (arithmeticTupleIQHullUnitRegion places tuple) = 1 := by
  classical
  set m : ℝ := (μ (arithmeticTupleIQHullUnitRegion places tuple)).toReal with hm
  have hmass_pos : 0 < m :=
    arithmeticTupleIQHullUnitRegion_measure_toReal_pos places tuple μ
  have hmass_ne : m ≠ 0 := hmass_pos.ne'
  have hmass_fin : μ (arithmeticTupleIQHullUnitRegion places tuple) ≠ ⊤ :=
    arithmeticTupleIQHullUnitRegion_measure_ne_top places tuple μ
  refine ⟨ENNReal.ofReal m⁻¹ • μ, ?_, ?_⟩
  · exact Measure.IsAddHaarMeasure.smul μ (c := ENNReal.ofReal m⁻¹)
      (ENNReal.ofReal_pos.mpr (inv_pos.mpr hmass_pos)).ne' ENNReal.ofReal_ne_top
  · calc
      (ENNReal.ofReal m⁻¹ • μ) (arithmeticTupleIQHullUnitRegion places tuple)
          = ENNReal.ofReal m⁻¹ * μ (arithmeticTupleIQHullUnitRegion places tuple) := by
            rw [Measure.smul_apply, smul_eq_mul]
      _ = ENNReal.ofReal m⁻¹ * ENNReal.ofReal m := by
            rw [show μ (arithmeticTupleIQHullUnitRegion places tuple) = ENNReal.ofReal m from
              (ENNReal.ofReal_toReal hmass_fin).symm]
      _ = ENNReal.ofReal (m⁻¹ * m) :=
            (ENNReal.ofReal_mul (inv_nonneg.mpr ENNReal.toReal_nonneg)).symm
      _ = ENNReal.ofReal 1 := by rw [inv_mul_cancel₀ hmass_ne]
      _ = 1 := ENNReal.ofReal_one

/-- After normalizing the unit region to mass one, `theta` vanishes and the
explicit hull bound becomes an `ENNReal.ofReal theta` bound with nonnegative
`theta`.  This is the form consumed by `CertificateHullWiring.iqHullCertificate`. -/
theorem exists_normalized_addHaar_hull_logVolume_le_theta
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    ∃ ν : Measure (ArithmeticTensorTupleBlock places tuple),
      Measure.IsAddHaarMeasure ν ∧
        ν (arithmeticTupleIQHullUnitRegion places tuple) = 1 ∧
        arithmeticTupleIQHullUnitLogTheta places tuple ν = 0 ∧
        haarLogVolume ν (arithmeticTupleCanonicalHull places tuple) ≤
          ENNReal.ofReal (arithmeticTupleIQHullUnitLogTheta places tuple ν) := by
  obtain ⟨ν, hν, hunit⟩ :=
    exists_normalized_addHaar_arithmeticTupleIQHullUnitRegion places tuple μ
  haveI : Measure.IsAddHaarMeasure ν := hν
  exact ⟨ν, hν, hunit,
    arithmeticTupleIQHullUnitLogTheta_eq_zero_of_measure_eq_one places tuple ν hunit,
    arithmeticTupleIQHull_hull_logVolume_le_unitRegion places tuple ν⟩

end

end LeanFormal.IUT.NumberFieldFinitePlace
