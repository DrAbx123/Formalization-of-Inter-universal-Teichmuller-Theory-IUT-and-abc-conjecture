import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface

/-!
# P1 carrier design: the actual finite-place arithmetic tensor IQ hull

This file is the P1 design package for the Corollary 3.12 -> ABC bridge audit.
It installs the actual `IQHullLogVolumeInterface` on the finite-place
arithmetic tensor block

  X := ArithmeticTensorTupleBlock places tuple

with the actual additive Haar log-volume `haarLogVolume μ` and the canonical
arithmetic-tuple hull.  This carrier is not the value-monoid carrier
`I.ThetaPilotPoint v`, so it does not depend on pointwise degree faithfulness
and is not derived from the refuted `SourceUnitRegionHaarData` value package.
The source of the interface is the actual finite-place arithmetic tensor
construction, not a named hull field.

All interface fields are projections of the already-actual
`arithmeticTupleIQHullLogVolumeInterface`; no sorry, axiom, True/PUnit gate or
native_decide is used. -/

set_option linter.unusedSectionVars false

namespace LeanFormal.IUT.NumberFieldFinitePlace

open MeasureTheory

noncomputable section

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w} [∀ i, Fintype (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]

/-- The P1 carrier type: the actual finite-place arithmetic tensor block. -/
abbrev P1Carrier : Type _ := ArithmeticTensorTupleBlock places tuple

/-- The actual `IQHullLogVolumeInterface` on the P1 carrier, built from the
finite-place arithmetic tensor hull and the additive Haar log-volume. -/
noncomputable def P1Interface (μ : Measure (P1Carrier places tuple))
    [Measure.IsAddHaarMeasure μ] :
    IQHullLogVolumeInterface (P1Carrier places tuple) :=
  arithmeticTupleIQHullLogVolumeInterface places tuple μ

/-- P1 field 1: the image set. -/
def P1ImageSet (μ : Measure (P1Carrier places tuple)) [Measure.IsAddHaarMeasure μ] :
    Set (P1Carrier places tuple) :=
  (P1Interface places tuple μ).imageSet

/-- P1 field 2: the hull (the canonical arithmetic-tuple hull). -/
def P1Hull (μ : Measure (P1Carrier places tuple)) [Measure.IsAddHaarMeasure μ] :
    Set (P1Carrier places tuple) :=
  (P1Interface places tuple μ).hull

/-- P1 field 3: the image set is contained in the hull. -/
theorem P1_imageSet_subset_hull (μ : Measure (P1Carrier places tuple))
    [Measure.IsAddHaarMeasure μ] :
    P1ImageSet places tuple μ ⊆ P1Hull places tuple μ :=
  (P1Interface places tuple μ).imageSet_subset_hull

/-- P1 field 4: the log-volume (the additive Haar log-volume). -/
def P1LogVolume (μ : Measure (P1Carrier places tuple)) [Measure.IsAddHaarMeasure μ] :
    Set (P1Carrier places tuple) → ENNReal :=
  (P1Interface places tuple μ).logVolume

/-- P1 field 5: monotonicity of the log-volume. -/
theorem P1_logVolume_mono (μ : Measure (P1Carrier places tuple))
    [Measure.IsAddHaarMeasure μ] {S T : Set (P1Carrier places tuple)}
    (hST : S ⊆ T) :
    P1LogVolume places tuple μ S ≤ P1LogVolume places tuple μ T :=
  (P1Interface places tuple μ).logVolume_mono hST

/-- P1 field 6: the unit region. -/
def P1UnitRegion (μ : Measure (P1Carrier places tuple)) [Measure.IsAddHaarMeasure μ] :
    Set (P1Carrier places tuple) :=
  (P1Interface places tuple μ).unitRegion

/-- P1 field 7: the scaling shift. -/
def P1ScaleShift (μ : Measure (P1Carrier places tuple)) [Measure.IsAddHaarMeasure μ] :
    P1Carrier places tuple → P1Carrier places tuple :=
  (P1Interface places tuple μ).scaleShift

/-- P1 field 8: the hull is contained in the scaled unit region. -/
theorem P1_hull_subset_scaleShift (μ : Measure (P1Carrier places tuple))
    [Measure.IsAddHaarMeasure μ] :
    P1Hull places tuple μ ⊆ P1ScaleShift places tuple μ '' P1UnitRegion places tuple μ :=
  (P1Interface places tuple μ).hull_subset_scaleShift

/-- P1 field 9: the unit region has finite log-volume. -/
theorem P1_unitRegion_logVolume_lt_top (μ : Measure (P1Carrier places tuple))
    [Measure.IsAddHaarMeasure μ] :
    P1LogVolume places tuple μ (P1UnitRegion places tuple μ) < ⊤ :=
  (P1Interface places tuple μ).unitRegion_logVolume_lt_top

/-- P1 field 10: Haar normalization under the scaling shift. -/
theorem P1_scaleShift_unitRegion_logVolume_le
    (μ : Measure (P1Carrier places tuple)) [Measure.IsAddHaarMeasure μ] :
    P1LogVolume places tuple μ (P1ScaleShift places tuple μ '' P1UnitRegion places tuple μ)
      ≤ P1LogVolume places tuple μ (P1UnitRegion places tuple μ) :=
  (P1Interface places tuple μ).scaleShift_unitRegion_logVolume_le

/-- The P1 log-volume is the actual Haar log-volume, not a value-monoid
point-volume construction. -/
theorem P1_logVolume_eq_haarLogVolume (μ : Measure (P1Carrier places tuple))
    [Measure.IsAddHaarMeasure μ] :
    P1LogVolume places tuple μ = haarLogVolume μ :=
  arithmeticTupleIQHullLogVolumeInterface_logVolume places tuple μ

/-- The P1 hull is the actual canonical arithmetic-tuple hull. -/
theorem P1_hull_eq_canonicalHull (μ : Measure (P1Carrier places tuple))
    [Measure.IsAddHaarMeasure μ] :
    P1Hull places tuple μ = arithmeticTupleCanonicalHull places tuple :=
  arithmeticTupleIQHullLogVolumeInterface_hull places tuple μ

/-- The P1 unit region is the canonical hull in this R1 normalization design. -/
theorem P1_unitRegion_eq_canonicalHull (μ : Measure (P1Carrier places tuple))
    [Measure.IsAddHaarMeasure μ] :
    P1UnitRegion places tuple μ = arithmeticTupleCanonicalHull places tuple :=
  arithmeticTupleIQHullLogVolumeInterface_unitRegion places tuple μ

/-- The P1 interface is actual and finite on its hull. -/
theorem P1_hull_logVolume_lt_top (μ : Measure (P1Carrier places tuple))
    [Measure.IsAddHaarMeasure μ] :
    P1LogVolume places tuple μ (P1Hull places tuple μ) < ⊤ :=
  arithmeticTupleIQHullLogVolumeInterface_hull_lt_top places tuple μ

#print axioms P1_imageSet_subset_hull
#print axioms P1_logVolume_mono
#print axioms P1_hull_subset_scaleShift
#print axioms P1_unitRegion_logVolume_lt_top
#print axioms P1_scaleShift_unitRegion_logVolume_le
#print axioms P1_hull_logVolume_lt_top

end

end LeanFormal.IUT.NumberFieldFinitePlace
