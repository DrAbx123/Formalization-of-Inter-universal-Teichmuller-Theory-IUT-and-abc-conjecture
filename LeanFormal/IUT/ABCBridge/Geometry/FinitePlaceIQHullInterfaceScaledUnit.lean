import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompactHullScaling

/-!
# The actual tuple IQ interface with a scaled integral unit region

The file `FinitePlaceIQHullInterface.lean` installs `IQHullLogVolumeInterface`
on the actual arithmetic tensor tuple with the R1 placeholder
`unitRegion = canonicalHull`, `scaleShift = id`.  This file replaces the
placeholder by a genuine scaled integral region:

* `arithmeticTupleIQHullUnitScale` chooses the nonzero scalar supplied by the
  compactness-to-scaling theorem;
* `unitRegion` is `λ • arithmeticTupleCanonicalUnitReference`, an open compact
  `λ·O` region with finite positive Haar mass;
* `scaleShift` is the identity because the scalar has already been absorbed
  into the unit region.

The hull is still the canonical hull and the image set is inherited from the
previously verified interface.  No O-module equality with the hull is claimed.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open MeasureTheory
open scoped Pointwise
open LeanFormal.IUT.LocalFieldProductHull

noncomputable section

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)

/-- The nonzero scalar supplied by the compactness-to-scaling theorem for the
actual canonical hull. -/
noncomputable def arithmeticTupleIQHullUnitScale : ℚ_[p] :=
  Classical.choose (arithmeticTupleCanonicalHull_subset_smul_unitReference places tuple)

/-- The chosen scale is nonzero. -/
theorem arithmeticTupleIQHullUnitScale_ne_zero :
    arithmeticTupleIQHullUnitScale places tuple ≠ 0 :=
  (Classical.choose_spec
    (arithmeticTupleCanonicalHull_subset_smul_unitReference places tuple)).1

/-- The canonical hull is contained in the chosen scaled integral unit
reference. -/
theorem arithmeticTupleCanonicalHull_subset_IQHullUnitScale_smul_unitReference :
    arithmeticTupleCanonicalHull places tuple ⊆
      arithmeticTupleIQHullUnitScale places tuple •
        arithmeticTupleCanonicalUnitReference places tuple :=
  (Classical.choose_spec
    (arithmeticTupleCanonicalHull_subset_smul_unitReference places tuple)).2

/-- The actual tuple IQ interface with the genuine scaled integral unit region
`λ • O`, where `λ` is the compactness-to-scaling scalar. -/
noncomputable def arithmeticTupleIQHullLogVolumeInterfaceScaledUnit
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    IQHullLogVolumeInterface (ArithmeticTensorTupleBlock places tuple) :=
  { imageSet := (arithmeticTupleIQHullLogVolumeInterface places tuple μ).imageSet
    hull := arithmeticTupleCanonicalHull places tuple
    imageSet_subset_hull := by
      rw [← arithmeticTupleIQHullLogVolumeInterface_hull places tuple μ]
      exact (arithmeticTupleIQHullLogVolumeInterface places tuple μ).imageSet_subset_hull
    logVolume := haarLogVolume μ
    logVolume_mono := fun hST => haarLogVolume_mono hST
    unitRegion :=
      arithmeticTupleIQHullUnitScale places tuple •
        arithmeticTupleCanonicalUnitReference places tuple
    scaleShift := id
    hull_subset_scaleShift := by
      simpa [Set.image_id] using
        arithmeticTupleCanonicalHull_subset_IQHullUnitScale_smul_unitReference places tuple
    unitRegion_logVolume_lt_top := by
      have hfin :=
        (measure_smul_arithmeticTupleCanonicalUnitReference_pos_lt_top places tuple μ
          (arithmeticTupleIQHullUnitScale places tuple)
          (arithmeticTupleIQHullUnitScale_ne_zero places tuple)).2
      rw [haarLogVolume_of_lt_top hfin]
      exact ENNReal.ofReal_lt_top
    scaleShift_unitRegion_logVolume_le := by simp [Set.image_id] }

/-- The scaled-unit interface has finite hull log-volume. -/
theorem arithmeticTupleIQHullLogVolumeInterfaceScaledUnit_hull_lt_top
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit places tuple μ).logVolume
      (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit places tuple μ).hull < ⊤ :=
  (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit places tuple μ).hull_logVolume_lt_top

end

end LeanFormal.IUT.NumberFieldFinitePlace


