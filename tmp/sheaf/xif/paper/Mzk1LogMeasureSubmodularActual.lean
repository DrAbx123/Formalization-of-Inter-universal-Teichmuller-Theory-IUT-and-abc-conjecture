/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # A1090: log-measure submodularity tool -/

/-
| field | value |
|---|---|
| Status | PARTIAL (real core PROVED; measure-level reduction uses explicit additivity hypothesis) |
| 真证 | `submodular_real`; `log_submodular_real`; `log_submodular_of_measure`（条件） |
| GAP | GAP-MEAS-ADD: the measure-level additivity identity `mu(A u B)+mu(A i B)=mu A+mu B` in Real form |
| 循环性 | no target assumed; pure measure/real algebra |
|-/

noncomputable section
open MeasureTheory

namespace LeanFormal.IUT.XiFPaper.Mzk1LogMeasureSubmodularActual

/-- Real submodularity core: if `p <= a`, `p <= b` and `q = a+b-p`, then `p*q <= a*b`. -/
theorem submodular_real (p a b q : Real) (hp : 0 < p) (hpa : p ≤ a) (hpb : p ≤ b)
    (hq : q = a + b - p) : p * q ≤ a * b := by
  have h1 : 0 ≤ (a - p) * (b - p) := mul_nonneg (sub_nonneg.mpr hpa) (sub_nonneg.mpr hpb)
  nlinarith [h1, hq]

/-- Log form: `log p + log q <= log a + log b`. -/
theorem log_submodular_real (p a b q : Real) (hp : 0 < p) (hpa : p ≤ a) (hpb : p ≤ b)
    (hq : q = a + b - p) : Real.log p + Real.log q ≤ Real.log a + Real.log b := by
  have ha : 0 < a := lt_of_lt_of_le hp hpa
  have hb : 0 < b := lt_of_lt_of_le hp hpb
  have hqpos : 0 < q := by rw [hq]; linarith
  have hle := submodular_real p a b q hp hpa hpb hq
  have hlog : Real.log (p * q) ≤ Real.log (a * b) :=
    Real.log_le_log (mul_pos hp hqpos) hle
  rw [Real.log_mul hp.ne' hqpos.ne', Real.log_mul ha.ne' hb.ne'] at hlog
  linarith

/-- **Measure-level (conditional)**: with the real additivity identity supplied, the
submodular log inequality holds for `p = mu(A i B)`, `a = mu A`, `b = mu B`, `q = mu(A u B)`. -/
theorem log_submodular_of_measure {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {A B : Set α}
    (hinter_pos : 0 < (μ (A ∩ B)).toReal)
    (hinter_le_A : (μ (A ∩ B)).toReal ≤ (μ A).toReal)
    (hinter_le_B : (μ (A ∩ B)).toReal ≤ (μ B).toReal)
    (hadd : (μ (A ∪ B)).toReal = (μ A).toReal + (μ B).toReal - (μ (A ∩ B)).toReal) :
    Real.log ((μ (A ∩ B)).toReal) + Real.log ((μ (A ∪ B)).toReal)
      ≤ Real.log ((μ A).toReal) + Real.log ((μ B).toReal) :=
  log_submodular_real ((μ (A ∩ B)).toReal) ((μ A).toReal) ((μ B).toReal)
    ((μ (A ∪ B)).toReal) hinter_pos hinter_le_A hinter_le_B hadd

/-- **Measure-level multiplicative form (conditional)**. -/
theorem submodular_of_measure {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {A B : Set α}
    (hinter_pos : 0 < (μ (A ∩ B)).toReal)
    (hinter_le_A : (μ (A ∩ B)).toReal ≤ (μ A).toReal)
    (hinter_le_B : (μ (A ∩ B)).toReal ≤ (μ B).toReal)
    (hadd : (μ (A ∪ B)).toReal = (μ A).toReal + (μ B).toReal - (μ (A ∩ B)).toReal) :
    (μ (A ∩ B)).toReal * (μ (A ∪ B)).toReal ≤ (μ A).toReal * (μ B).toReal :=
  submodular_real ((μ (A ∩ B)).toReal) ((μ A).toReal) ((μ B).toReal)
    ((μ (A ∪ B)).toReal) hinter_pos hinter_le_A hinter_le_B hadd

def submodularRows : List (String × String) :=
  [ ("submodular_real", "p*q <= a*b (PROVED, real algebra)") ,
    ("log_submodular_real", "log p + log q <= log a + log b (PROVED)") ,
    ("log_submodular_of_measure", "measure reduction with hadd hypothesis (PROVED)") ,
    ("GAP-MEAS-ADD", "Real additivity identity from measure_union_add_inter not ported") ]

theorem submodularRows_length : submodularRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1LogMeasureSubmodularActual