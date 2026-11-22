import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleCanonicalHull
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldProductHull
import Mathlib.Tactic

set_option linter.unusedSectionVars false

/-!
# The actual tuple tensor's IQ hull/log-volume interface (N4/N6/N7, R1)

This file installs `IQHullLogVolumeInterface` on the actual finite-place
arithmetic tensor carrier `ArithmeticTensorTupleBlock places tuple`.

* The hull is the decomposition-independent canonical hull
  `arithmeticTupleCanonicalHull`.
* The image set is the pullback of the field-product logarithmic image along
  one fixed actual field-product decomposition.  No decomposition-independence
  of this chosen image set is claimed.
* The log-volume is built from an actual additive Haar measure `μ`.

## R1 normalization placeholder

The unit region is the canonical hull itself and the scaling is the identity:
the `lambda` of the paper's `lambda * O` normalization is absorbed into the
unit region.  This fills all six interface fields with proved facts, but it is
not a construction of the paper's `O`-module region; that upgrade is recorded
as an open item in the report.

## Boundary

This is an interface realization on the actual finite-place arithmetic tensor
carrier.  It does not construct the source `ThetaPilotPoint`/`OriginalInput`
N5 card, and it does not identify the value-monoid model with this carrier.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open MeasureTheory
open LeanFormal.IUT.LocalFieldProductHull

noncomputable section

universe u v w

/-! ## 1. The Haar log-volume functional -/

/-- Finite-or-infinite Haar log-volume.  On finite-mass regions this is the
requested formula `ENNReal.ofReal (Real.log (μ S).toReal)`; the infinite-mass
case is kept as `⊤`, since `(⊤ : ENNReal).toReal = 0` would otherwise turn an
infinite-mass region into log-volume zero and destroy monotonicity. -/
def haarLogVolume {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Set X) : ENNReal :=
  if μ S = ⊤ then ⊤ else ENNReal.ofReal (Real.log (μ S).toReal)

theorem haarLogVolume_of_lt_top {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {S : Set X} (h : μ S < ⊤) :
    haarLogVolume μ S = ENNReal.ofReal (Real.log (μ S).toReal) := by
  rw [haarLogVolume, if_neg h.ne]

/-- The zero-measure case, using Mathlib's convention `Real.log 0 = 0`. -/
theorem haarLogVolume_eq_zero_of_null {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {S : Set X} (h : μ S = 0) :
    haarLogVolume μ S = 0 := by
  simp [haarLogVolume, h]

/-- Monotonicity of the Haar log-volume under inclusion.  No finiteness of the
larger set is assumed: the `⊤` case is handled separately. -/
theorem haarLogVolume_mono {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {S T : Set X} (hST : S ⊆ T) :
    haarLogVolume μ S ≤ haarLogVolume μ T := by
  by_cases hT : μ T = ⊤
  · simp [haarLogVolume, hT]
  · have hS : μ S ≠ ⊤ := ne_top_of_le_ne_top hT (measure_mono hST)
    simp only [haarLogVolume, if_neg hS, if_neg hT]
    have hle : (μ S).toReal ≤ (μ T).toReal :=
      ENNReal.toReal_mono hT (measure_mono hST)
    by_cases hzero : (μ S).toReal = 0
    · simp [hzero]
    · have hpos : 0 < (μ S).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hzero)
      exact ENNReal.ofReal_le_ofReal (Real.log_le_log hpos hle)

/-! ## 2. The interface on the actual tuple tensor -/

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)

variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]

/-- Existence of an R1 `IQHullLogVolumeInterface` instance on the actual tuple
tensor with pinned structural fields.

The image set is the pullback of `arithmeticTupleFieldLogImage` along one fixed
actual field-product decomposition chosen from
`exists_arithmeticTensorTuple_fieldProduct`.  The hull is the canonical hull,
and `arithmeticTupleCanonicalHull_eq` rewrites the chosen pullback hull to it.
The unit region is the canonical hull itself and the scaling is the identity
(R1 normalization placeholder).  All six interface fields are filled by proved
facts; the existential is stated in `Prop` so that the witness data can be
chosen classically for the definition below. -/
theorem exists_arithmeticTupleIQHullLogVolumeInterface
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    ∃ W : IQHullLogVolumeInterface (ArithmeticTensorTupleBlock places tuple),
      W.hull = arithmeticTupleCanonicalHull places tuple ∧
        W.unitRegion = arithmeticTupleCanonicalHull places tuple ∧
          W.logVolume = haarLogVolume μ := by
  classical
  obtain ⟨J, hJ, E, hfield, halgebra, e, hE, _, _⟩ :=
    exists_arithmeticTensorTuple_fieldProduct places tuple
  letI := hJ
  letI := hfield
  letI := halgebra
  letI : ∀ j, FiniteDimensional ℚ_[p] (E j) := fun j => (hE j).1
  letI : ∀ j, ProperSpace (E j) := fun j => FiniteDimensional.proper ℚ_[p] (E j)
  refine
    ⟨{ imageSet := e.symm '' arithmeticTupleFieldLogImage places tuple e
       hull := arithmeticTupleCanonicalHull places tuple
       imageSet_subset_hull := ?_
       logVolume := haarLogVolume μ
       logVolume_mono := fun hST => haarLogVolume_mono hST
       unitRegion := arithmeticTupleCanonicalHull places tuple
       scaleShift := id
       hull_subset_scaleShift := ?_
       unitRegion_logVolume_lt_top := ?_
       scaleShift_unitRegion_logVolume_le := ?_ }, rfl, rfl, rfl⟩
  · rw [arithmeticTupleCanonicalHull_eq places tuple e]
    rintro x ⟨y, hy, rfl⟩
    exact ⟨y, subset_hull _ hy, rfl⟩
  · intro x hx
    exact ⟨x, hx, rfl⟩
  · have hfin :=
      (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple μ).1.2
    rw [haarLogVolume_of_lt_top hfin]
    exact ENNReal.ofReal_lt_top
  · change haarLogVolume μ (id '' arithmeticTupleCanonicalHull places tuple) ≤
      haarLogVolume μ (arithmeticTupleCanonicalHull places tuple)
    rw [Set.image_id]

/-- The R1 `IQHullLogVolumeInterface` instance on the actual tuple tensor. -/
noncomputable def arithmeticTupleIQHullLogVolumeInterface
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    IQHullLogVolumeInterface (ArithmeticTensorTupleBlock places tuple) :=
  Classical.choose (exists_arithmeticTupleIQHullLogVolumeInterface places tuple μ)

/-- The interface's hull is the canonical hull, by the pinned witness. -/
@[simp] theorem arithmeticTupleIQHullLogVolumeInterface_hull
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    (arithmeticTupleIQHullLogVolumeInterface places tuple μ).hull =
      arithmeticTupleCanonicalHull places tuple :=
  (Classical.choose_spec
    (exists_arithmeticTupleIQHullLogVolumeInterface places tuple μ)).1

/-- The interface's unit region is the canonical hull (R1 placeholder). -/
@[simp] theorem arithmeticTupleIQHullLogVolumeInterface_unitRegion
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    (arithmeticTupleIQHullLogVolumeInterface places tuple μ).unitRegion =
      arithmeticTupleCanonicalHull places tuple :=
  (Classical.choose_spec
    (exists_arithmeticTupleIQHullLogVolumeInterface places tuple μ)).2.1

/-- The interface's log-volume is the Haar log-volume of the actual measure. -/
@[simp] theorem arithmeticTupleIQHullLogVolumeInterface_logVolume
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    (arithmeticTupleIQHullLogVolumeInterface places tuple μ).logVolume =
      haarLogVolume μ :=
  (Classical.choose_spec
    (exists_arithmeticTupleIQHullLogVolumeInterface places tuple μ)).2.2

/-! ## 3. The interface conclusions -/

/-- Finiteness of the hull log-volume for the concrete instance. -/
theorem arithmeticTupleIQHullLogVolumeInterface_hull_lt_top
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    (arithmeticTupleIQHullLogVolumeInterface places tuple μ).logVolume
      (arithmeticTupleIQHullLogVolumeInterface places tuple μ).hull < ⊤ :=
  IQHullLogVolumeInterface.hull_logVolume_lt_top _

/-- The image-set log-volume is at most the hull log-volume. -/
theorem arithmeticTupleIQHullLogVolumeInterface_imageSet_logVolume_le_hull
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    (arithmeticTupleIQHullLogVolumeInterface places tuple μ).logVolume
        (arithmeticTupleIQHullLogVolumeInterface places tuple μ).imageSet ≤
      (arithmeticTupleIQHullLogVolumeInterface places tuple μ).logVolume
        (arithmeticTupleIQHullLogVolumeInterface places tuple μ).hull :=
  IQHullLogVolumeInterface.imageSet_logVolume_le_hull _

/-! ## 4. Exact unit-relative comparison -/

/-- Exact unit-relative relation between the hull's Haar log-volume and the
constructed unit-relative volume `arithmeticTupleHullUnitLogVolume`.  The unit
reference term is not dropped: the two log-volumes differ by its
normalization. -/
theorem arithmeticTupleIQHullLogVolumeInterface_hull_logVolume_toReal
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    Real.log (μ (arithmeticTupleCanonicalHull places tuple)).toReal =
      arithmeticTupleHullUnitLogVolume places tuple +
        Real.log (μ (arithmeticTupleCanonicalUnitReference places tuple)).toReal := by
  classical
  obtain ⟨J, hJ, E, hfield, halgebra, e, hE, _, _⟩ :=
    exists_arithmeticTensorTuple_fieldProduct places tuple
  letI := hJ
  letI := hfield
  letI := halgebra
  letI : ∀ j, FiniteDimensional ℚ_[p] (E j) := fun j => (hE j).1
  letI : ∀ j, ProperSpace (E j) := fun j => FiniteDimensional.proper ℚ_[p] (E j)
  letI : MeasurableSpace ((j : J) → E j) := borel _
  letI : BorelSpace ((j : J) → E j) := ⟨rfl⟩
  have hrel := arithmeticTupleHullPullback_relativeLogVolume places tuple e μ
  rw [← arithmeticTupleCanonicalHull_eq places tuple e,
    ← arithmeticTupleCanonicalUnitReference_eq places tuple e] at hrel
  rw [← arithmeticTupleHullUnitLogVolume_eq places tuple e] at hrel
  linarith

/-- ENNReal form of the exact comparison: the instance's hull log-volume is
the `ofReal` of the unit-relative log-volume plus the unit normalization. -/
theorem arithmeticTupleIQHullLogVolumeInterface_hull_logVolume_eq_ofReal
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    (arithmeticTupleIQHullLogVolumeInterface places tuple μ).logVolume
        (arithmeticTupleIQHullLogVolumeInterface places tuple μ).hull =
      ENNReal.ofReal (arithmeticTupleHullUnitLogVolume places tuple +
        Real.log (μ (arithmeticTupleCanonicalUnitReference places tuple)).toReal) := by
  have hfin :=
    (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple μ).1.2
  rw [arithmeticTupleIQHullLogVolumeInterface_logVolume,
    arithmeticTupleIQHullLogVolumeInterface_hull,
    haarLogVolume_of_lt_top hfin]
  exact congrArg ENNReal.ofReal
    (arithmeticTupleIQHullLogVolumeInterface_hull_logVolume_toReal (places := places)
      (tuple := tuple) μ)

/-- Conditional exact equality with `arithmeticTupleHullUnitLogVolume`: it holds
once the additive Haar measure is normalized on the canonical unit reference. -/
theorem arithmeticTupleIQHullLogVolumeInterface_hull_logVolume_eq_of_unit_normalized
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ]
    (hunit : μ (arithmeticTupleCanonicalUnitReference places tuple) = 1) :
    (arithmeticTupleIQHullLogVolumeInterface places tuple μ).logVolume
        (arithmeticTupleIQHullLogVolumeInterface places tuple μ).hull =
      ENNReal.ofReal (arithmeticTupleHullUnitLogVolume places tuple) := by
  exact (arithmeticTupleIQHullLogVolumeInterface_hull_logVolume_eq_ofReal
    (places := places) (tuple := tuple) μ).trans (by simp [hunit])

end

end LeanFormal.IUT.NumberFieldFinitePlace
