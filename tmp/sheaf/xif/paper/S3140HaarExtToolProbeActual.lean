import Mathlib

/-! # S3140 Haar tool cross-check (for abc, task-60) — Mathlib-only, light.

Exact signatures of the existing Mathlib tool assets (coord/TOOL-INVENTORY.md A)
and one checked application to two Haar measures on a second-countable locally
compact group.  No new tool needed: Mathlib already supplies the uniqueness /
Riesz-extension tools for abc's S3135HaarUniquenessScalarStep.

No sorry/axiom/arbitrary carrier. -/

open MeasureTheory

#check @MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported
#check @MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported_nnreal
#check @MeasureTheory.Measure.isMulLeftInvariant_eq_smul
#check @MeasureTheory.Measure.isAddLeftInvariant_eq_smul
#check @MeasureTheory.Measure.measure_isHaarMeasure_eq_smul_of_isOpen
#check @MeasureTheory.Measure.measure_isAddHaarMeasure_eq_smul_of_isOpen
#check @MeasureTheory.Measure.haarScalarFactor_eq_integral_div
#check @MeasureTheory.Measure.addHaarScalarFactor_eq_integral_div

/-- Two multiplicative Haar measures on a second-countable locally compact
topological group are proportional (Mathlib `isMulLeftInvariant_eq_smul`). -/
example {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G]
    (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure] :
    ν = MeasureTheory.Measure.haarScalarFactor ν μ • μ :=
  MeasureTheory.Measure.isMulLeftInvariant_eq_smul ν μ

/-- Additive companion. -/
example {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G]
    (μ ν : Measure G) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] :
    ν = MeasureTheory.Measure.addHaarScalarFactor ν μ • μ :=
  MeasureTheory.Measure.isAddLeftInvariant_eq_smul ν μ
