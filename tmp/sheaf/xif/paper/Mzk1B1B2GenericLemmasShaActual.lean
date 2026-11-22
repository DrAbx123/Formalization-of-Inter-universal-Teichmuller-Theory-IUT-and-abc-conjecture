import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # B1 single-point zero measure / B2 normalization split (generic helpers) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1B1B2GenericLemmasShaActual

open MeasureTheory

/-- B1: under `NoAtoms`, a singleton has measure zero. -/
theorem b1_single_point_zero {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [MeasureTheory.NullSingletonClass μ] (x : α) : μ {x} = 0 :=
  MeasureTheory.measure_singleton x

/-- B2: normalization split for positive reals. -/
theorem b2_log_mul {a b : Real} (ha : 0 < a) (hb : 0 < b) :
    Real.log (a * b) = Real.log a + Real.log b :=
  Real.log_mul ha.ne' hb.ne'

theorem b2_log_div {a b : Real} (ha : 0 < a) (hb : 0 < b) :
    Real.log (a / b) = Real.log a - Real.log b :=
  Real.log_div ha.ne' hb.ne'

#print axioms b1_single_point_zero
#print axioms b2_log_mul
#print axioms b2_log_div

end LeanFormal.IUT.XiFPaper.Mzk1B1B2GenericLemmasShaActual
