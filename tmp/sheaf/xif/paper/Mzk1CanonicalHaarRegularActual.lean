/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Regular

/-! # Canonical additive Haar is outer regular (task-109, green API step) -/
noncomputable section
open scoped BigOperators
open MeasureTheory
open MeasureTheory.Measure
namespace LeanFormal.IUT.XiFPaper.Mzk1CanonicalHaarRegularActual
variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [MeasurableSpace E] [IsTopologicalAddGroup E] [BorelSpace E] [LocallyCompactSpace E]
/-- The canonical additive Haar measure is outer regular, via Mathlib's
`regular_haarMeasure` instance. -/
theorem canonical_addHaarMeasure_outerRegular
    (K₀ : TopologicalSpace.PositiveCompacts E) :
    Measure.OuterRegular (MeasureTheory.Measure.addHaarMeasure K₀) := by
  haveI : (MeasureTheory.Measure.addHaarMeasure K₀).Regular :=
    MeasureTheory.Measure.regular_addHaarMeasure (K₀ := K₀)
  infer_instance
def canonicalHaarRows : List (String × String) :=
  [ ("canonical_addHaarMeasure_outerRegular", "green from regular_haarMeasure"),
    ("apply to glAct", "GAP") ]
theorem canonicalHaarRows_length : canonicalHaarRows.length = 2 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1CanonicalHaarRegularActual
