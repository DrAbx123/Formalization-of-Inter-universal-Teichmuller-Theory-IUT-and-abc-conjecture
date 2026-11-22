import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompactHullScaling
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicHaarScaling
import Mathlib.Tactic

/-!
# A scaled unit-reference log-shell region on the actual arithmetic tuple carrier

This file upgrades the R1 normalization placeholder of
`FinitePlaceIQHullInterface` on the actual carrier
`ArithmeticTensorTupleBlock places tuple`.

* The R1 witness supplies the image set, the canonical hull and the Haar
  log-volume.  The hull is `arithmeticTupleCanonicalHull` and the log-volume is
  `haarLogVolume μ`.
* The compactness-to-scaling theorem
  `arithmeticTupleCanonicalHull_subset_smul_unitReference` supplies a nonzero
  scalar `lam` with
  `arithmeticTupleCanonicalHull ⊆ lam • arithmeticTupleCanonicalUnitReference`.
* The new unit region is
  `(p : ℚ_[p])⁻¹ • (lam • arithmeticTupleCanonicalUnitReference)`, and the new
  scaling is multiplication by `(p : ℚ_[p])`.  Hence the image of the unit
  region under the scaling is exactly the scaled canonical unit reference.
* The `p`-scaling formula of `FinitePadicHaarScaling` gives
  `μ (p • unitRegion) = (p ^ finrank)⁻¹ * μ unitRegion ≤ μ unitRegion`.

The scaling is genuine: `(p : ℚ_[p])` is nonzero, its norm is strictly less
than one, and the resulting `scaleShift` is not the identity.

## Boundary

This is a scaled unit-reference region on the actual finite-place arithmetic
tensor carrier.  It is not the paper's `O_{vQ}`-module region, and it is not an
identification with the source `ThetaPilotPoint`/`OriginalInput` IQ carrier.
No identification with the paper's `1,◦U` construction is claimed.  This file
does not by itself close N4--N7.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

namespace LeanFormal.IUT.NumberFieldFinitePlace

open MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)

/-! ## The selected compactness scaling -/

/-- A compactness-to-scaling constant for the actual canonical hull: it is
nonzero and the canonical hull is contained in the corresponding multiple of
the canonical unit reference. -/
def arithmeticTupleLogShellScaling : ℚ_[p] :=
  Classical.choose (arithmeticTupleCanonicalHull_subset_smul_unitReference places tuple)

theorem arithmeticTupleLogShellScaling_ne_zero :
    arithmeticTupleLogShellScaling places tuple ≠ 0 :=
  (Classical.choose_spec
    (arithmeticTupleCanonicalHull_subset_smul_unitReference places tuple)).1

/-- The defining containment of the selected scaling. -/
theorem arithmeticTupleCanonicalHull_subset_smul_logShellUnitReference :
    arithmeticTupleCanonicalHull places tuple ⊆
      arithmeticTupleLogShellScaling places tuple •
        arithmeticTupleCanonicalUnitReference places tuple :=
  (Classical.choose_spec
    (arithmeticTupleCanonicalHull_subset_smul_unitReference places tuple)).2

/-! ## Basic facts about the prime scalar -/

theorem padicPrimeCast_ne_zero : (p : ℚ_[p]) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero

theorem padicPrimeCast_ne_one : (p : ℚ_[p]) ≠ 1 := by
  intro h
  have h' : (p : ℚ_[p]) = ((1 : ℕ) : ℚ_[p]) := by simpa using h
  exact (Fact.out : Nat.Prime p).ne_one (Nat.cast_injective h')

theorem padicPrimeCast_norm_lt_one : ‖(p : ℚ_[p])‖ < 1 :=
  Padic.norm_p_lt_one (p := p)

/-! ## The scaled unit-reference region and the scaling -/

/-- The unit region is the `p⁻¹`-multiple of the compactness-scaled canonical
unit reference.  The subsequent scaling by `p` returns the scaled canonical
unit reference. -/
def arithmeticTupleLogShellUnitRegion :
    Set (ArithmeticTensorTupleBlock places tuple) :=
  (p : ℚ_[p])⁻¹ •
    (arithmeticTupleLogShellScaling places tuple •
      arithmeticTupleCanonicalUnitReference places tuple)

/-- The multiplicative scaling of the log-shell region: multiplication by the
prime `p` in the actual tensor algebra. -/
def arithmeticTupleLogShellScaleShift :
    ArithmeticTensorTupleBlock places tuple → ArithmeticTensorTupleBlock places tuple :=
  fun x => (p : ℚ_[p]) • x

theorem arithmeticTupleLogShellScaleShift_apply
    (x : ArithmeticTensorTupleBlock places tuple) :
    arithmeticTupleLogShellScaleShift places tuple x = (p : ℚ_[p]) • x :=
  rfl

/-- The scaling image of the unit region is exactly the compactness-scaled
canonical unit reference. -/
theorem arithmeticTupleLogShellScaleShift_image_unitRegion :
    arithmeticTupleLogShellScaleShift places tuple ''
        arithmeticTupleLogShellUnitRegion places tuple =
      arithmeticTupleLogShellScaling places tuple •
        arithmeticTupleCanonicalUnitReference places tuple := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [arithmeticTupleLogShellUnitRegion, Set.mem_smul_set] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    simp only [arithmeticTupleLogShellScaleShift]
    rw [smul_smul, mul_inv_cancel₀ (padicPrimeCast_ne_zero (p := p)), one_smul]
    exact hz
  · intro hx
    rw [Set.mem_smul_set] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    refine ⟨(p : ℚ_[p])⁻¹ •
      (arithmeticTupleLogShellScaling places tuple • z), ?_, ?_⟩
    · rw [arithmeticTupleLogShellUnitRegion, Set.mem_smul_set]
      exact ⟨arithmeticTupleLogShellScaling places tuple • z,
        Set.smul_mem_smul_set hz, rfl⟩
    · simp only [arithmeticTupleLogShellScaleShift]
      rw [smul_smul, mul_inv_cancel₀ (padicPrimeCast_ne_zero (p := p)), one_smul]

/-- The prime scaling of the unit region, written in terms of the canonical
unit reference. -/
theorem arithmeticTupleLogShellUnitRegion_smul_eq :
    (p : ℚ_[p]) • arithmeticTupleLogShellUnitRegion places tuple =
      arithmeticTupleLogShellScaling places tuple •
        arithmeticTupleCanonicalUnitReference places tuple := by
  rw [arithmeticTupleLogShellUnitRegion, smul_smul,
    mul_inv_cancel₀ (padicPrimeCast_ne_zero (p := p)), one_smul]

theorem arithmeticTupleLogShellUnitRegion_nonempty :
    (arithmeticTupleLogShellUnitRegion places tuple).Nonempty := by
  rw [arithmeticTupleLogShellUnitRegion, smul_smul]
  exact ⟨0, zero_mem_smul_arithmeticTupleCanonicalUnitReference places tuple _
    (mul_ne_zero (inv_ne_zero (padicPrimeCast_ne_zero (p := p)))
      (arithmeticTupleLogShellScaling_ne_zero places tuple))⟩

/-- The scaling is not the identity: it sends `1` to `p • 1`, and `p` is not
`1` in characteristic zero. -/
theorem arithmeticTupleLogShellScaleShift_ne_id :
    arithmeticTupleLogShellScaleShift places tuple ≠ id := by
  intro h
  have hp_sub_ne_zero : (p : ℚ_[p]) - 1 ≠ 0 :=
    sub_ne_zero.mpr (padicPrimeCast_ne_one (p := p))
  have h_one : (p : ℚ_[p]) • (1 : ArithmeticTensorTupleBlock places tuple) = 1 := by
    have := congrFun h 1
    simpa [arithmeticTupleLogShellScaleShift] using this
  have h_zero : ((p : ℚ_[p]) - 1) •
      (1 : ArithmeticTensorTupleBlock places tuple) = 0 := by
    rw [sub_smul, h_one, one_smul, sub_self]
  have h_scalar : (p : ℚ_[p]) - 1 = 0 := by
    rcases smul_eq_zero.mp h_zero with hscalar | hone
    · exact hscalar
    · exact absurd hone one_ne_zero
  exact hp_sub_ne_zero h_scalar

/-! ## Haar mass and log-volume of the scaled region -/

variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]

theorem arithmeticTupleLogShellUnitRegion_measure_pos
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    0 < μ (arithmeticTupleLogShellUnitRegion places tuple) := by
  rw [arithmeticTupleLogShellUnitRegion, smul_smul]
  exact (measure_smul_arithmeticTupleCanonicalUnitReference_pos_lt_top places tuple μ _
    (mul_ne_zero (inv_ne_zero (padicPrimeCast_ne_zero (p := p)))
      (arithmeticTupleLogShellScaling_ne_zero places tuple))).1

theorem arithmeticTupleLogShellUnitRegion_measure_lt_top
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    μ (arithmeticTupleLogShellUnitRegion places tuple) < ⊤ := by
  rw [arithmeticTupleLogShellUnitRegion, smul_smul]
  exact (isCompact_smul_arithmeticTupleCanonicalUnitReference places tuple
    ((p : ℚ_[p])⁻¹ * arithmeticTupleLogShellScaling places tuple)).measure_lt_top

/-- The actual `p`-scaling formula for the unit region, transported from
`FinitePadicHaarScaling`. -/
theorem arithmeticTupleLogShellUnitRegion_measure_prime_smul
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    μ ((p : ℚ_[p]) • arithmeticTupleLogShellUnitRegion places tuple) =
      ((p : ENNReal) ^ Module.finrank ℚ_[p]
        (ArithmeticTensorTupleBlock places tuple))⁻¹ *
        μ (arithmeticTupleLogShellUnitRegion places tuple) :=
  FinitePadicHaarScaling.measure_prime_smul_finiteDimensional (p := p) μ _

/-- The measure of the `p`-scaled unit region is at most the measure of the
unit region, because the Haar multiplier is at most one. -/
theorem arithmeticTupleLogShellUnitRegion_measure_prime_smul_le
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    μ ((p : ℚ_[p]) • arithmeticTupleLogShellUnitRegion places tuple) ≤
      μ (arithmeticTupleLogShellUnitRegion places tuple) := by
  rw [arithmeticTupleLogShellUnitRegion_measure_prime_smul]
  have hp_one : (1 : ENNReal) ≤ (p : ENNReal) := by
    rw [← ENNReal.coe_natCast p]
    exact ENNReal.one_le_coe_iff.mpr
      (by exact_mod_cast (Fact.out : Nat.Prime p).one_le)
  have h_factor : ((p : ENNReal) ^ Module.finrank ℚ_[p]
      (ArithmeticTensorTupleBlock places tuple))⁻¹ ≤ 1 := by
    rw [ENNReal.inv_le_one]
    exact one_le_pow₀ hp_one
  calc
    ((p : ENNReal) ^ Module.finrank ℚ_[p]
        (ArithmeticTensorTupleBlock places tuple))⁻¹ *
        μ (arithmeticTupleLogShellUnitRegion places tuple)
        ≤ 1 * μ (arithmeticTupleLogShellUnitRegion places tuple) :=
      mul_le_mul_left h_factor _
    _ = μ (arithmeticTupleLogShellUnitRegion places tuple) := one_mul _

/-- A measure-monotonicity form of `haarLogVolume`, with both sets of finite
positive mass. -/
theorem haarLogVolume_le_of_measure_le {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {S T : Set X}
    (hS : 0 < μ S) (hT : μ T < ⊤) (hle : μ S ≤ μ T) :
    haarLogVolume μ S ≤ haarLogVolume μ T := by
  have hSfin : μ S < ⊤ := lt_of_le_of_lt hle hT
  rw [haarLogVolume_of_lt_top hSfin, haarLogVolume_of_lt_top hT]
  apply ENNReal.ofReal_le_ofReal
  have hleReal : (μ S).toReal ≤ (μ T).toReal := ENNReal.toReal_mono hT.ne hle
  have hSpos : 0 < (μ S).toReal := ENNReal.toReal_pos hS.ne' hSfin.ne
  exact Real.log_le_log hSpos hleReal

theorem arithmeticTupleLogShellUnitRegion_haarLogVolume_lt_top
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    haarLogVolume μ (arithmeticTupleLogShellUnitRegion places tuple) < ⊤ := by
  rw [haarLogVolume_of_lt_top
    (arithmeticTupleLogShellUnitRegion_measure_lt_top places tuple μ)]
  exact ENNReal.ofReal_lt_top

/-- The Haar log-volume of the scaled unit region is at most that of the unit
region. -/
theorem arithmeticTupleLogShellScaleShift_unitRegion_logVolume_le
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    haarLogVolume μ (arithmeticTupleLogShellScaleShift places tuple ''
        arithmeticTupleLogShellUnitRegion places tuple) ≤
      haarLogVolume μ (arithmeticTupleLogShellUnitRegion places tuple) := by
  rw [arithmeticTupleLogShellScaleShift_image_unitRegion]
  have hle : μ (arithmeticTupleLogShellScaling places tuple •
      arithmeticTupleCanonicalUnitReference places tuple) ≤
      μ (arithmeticTupleLogShellUnitRegion places tuple) := by
    rw [← arithmeticTupleLogShellUnitRegion_smul_eq]
    exact arithmeticTupleLogShellUnitRegion_measure_prime_smul_le places tuple μ
  exact haarLogVolume_le_of_measure_le
    (measure_smul_arithmeticTupleCanonicalUnitReference_pos_lt_top places tuple μ
      (arithmeticTupleLogShellScaling places tuple)
      (arithmeticTupleLogShellScaling_ne_zero places tuple)).1
    (arithmeticTupleLogShellUnitRegion_measure_lt_top places tuple μ)
    hle

/-! ## The log-shell interface instance -/

/-- Existence of an `IQHullLogVolumeInterface` on the actual tuple carrier whose
unit region is the scaled unit reference and whose scaling is multiplication by
`p`.  The image set, hull and log-volume are inherited from the R1 witness. -/
theorem exists_arithmeticTupleIQHullLogShellInterface
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    ∃ W : IQHullLogVolumeInterface (ArithmeticTensorTupleBlock places tuple),
      W.imageSet = (arithmeticTupleIQHullLogVolumeInterface places tuple μ).imageSet ∧
        W.hull = arithmeticTupleCanonicalHull places tuple ∧
          W.unitRegion = arithmeticTupleLogShellUnitRegion places tuple ∧
            W.scaleShift = arithmeticTupleLogShellScaleShift places tuple ∧
              W.logVolume = haarLogVolume μ := by
  classical
  let W0 := arithmeticTupleIQHullLogVolumeInterface places tuple μ
  refine ⟨{ imageSet := W0.imageSet
            hull := arithmeticTupleCanonicalHull places tuple
            imageSet_subset_hull := ?_
            logVolume := haarLogVolume μ
            logVolume_mono := fun hST => haarLogVolume_mono hST
            unitRegion := arithmeticTupleLogShellUnitRegion places tuple
            scaleShift := arithmeticTupleLogShellScaleShift places tuple
            hull_subset_scaleShift := ?_
            unitRegion_logVolume_lt_top := ?_
            scaleShift_unitRegion_logVolume_le := ?_ }, rfl, rfl, rfl, rfl, rfl⟩
  · have hhull : W0.hull = arithmeticTupleCanonicalHull places tuple :=
      arithmeticTupleIQHullLogVolumeInterface_hull (places := places) (tuple := tuple) μ
    rw [← hhull]
    exact W0.imageSet_subset_hull
  · intro x hx
    rw [arithmeticTupleLogShellScaleShift_image_unitRegion]
    exact arithmeticTupleCanonicalHull_subset_smul_logShellUnitReference places tuple hx
  · exact arithmeticTupleLogShellUnitRegion_haarLogVolume_lt_top places tuple μ
  · exact arithmeticTupleLogShellScaleShift_unitRegion_logVolume_le places tuple μ

/-- The canonical log-shell interface instance on the actual tuple carrier. -/
noncomputable def arithmeticTupleIQHullLogShellInterface
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    IQHullLogVolumeInterface (ArithmeticTensorTupleBlock places tuple) :=
  Classical.choose (exists_arithmeticTupleIQHullLogShellInterface places tuple μ)

@[simp] theorem arithmeticTupleIQHullLogShellInterface_imageSet
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    (arithmeticTupleIQHullLogShellInterface places tuple μ).imageSet =
      (arithmeticTupleIQHullLogVolumeInterface places tuple μ).imageSet :=
  (Classical.choose_spec
    (exists_arithmeticTupleIQHullLogShellInterface places tuple μ)).1

@[simp] theorem arithmeticTupleIQHullLogShellInterface_hull
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    (arithmeticTupleIQHullLogShellInterface places tuple μ).hull =
      arithmeticTupleCanonicalHull places tuple :=
  (Classical.choose_spec
    (exists_arithmeticTupleIQHullLogShellInterface places tuple μ)).2.1

@[simp] theorem arithmeticTupleIQHullLogShellInterface_unitRegion
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    (arithmeticTupleIQHullLogShellInterface places tuple μ).unitRegion =
      arithmeticTupleLogShellUnitRegion places tuple :=
  (Classical.choose_spec
    (exists_arithmeticTupleIQHullLogShellInterface places tuple μ)).2.2.1

@[simp] theorem arithmeticTupleIQHullLogShellInterface_scaleShift
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    (arithmeticTupleIQHullLogShellInterface places tuple μ).scaleShift =
      arithmeticTupleLogShellScaleShift places tuple :=
  (Classical.choose_spec
    (exists_arithmeticTupleIQHullLogShellInterface places tuple μ)).2.2.2.1

@[simp] theorem arithmeticTupleIQHullLogShellInterface_logVolume
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    (arithmeticTupleIQHullLogShellInterface places tuple μ).logVolume =
      haarLogVolume μ :=
  (Classical.choose_spec
    (exists_arithmeticTupleIQHullLogShellInterface places tuple μ)).2.2.2.2

end

end LeanFormal.IUT.NumberFieldFinitePlace
