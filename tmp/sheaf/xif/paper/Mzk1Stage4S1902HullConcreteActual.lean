import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-! # Mzk1Stage4S1902HullConcreteActual (stage4 lane; unique filename)

A614 module: a concrete S1902-style hull data instance on `ℝ` (the interval [-1,1]) with
explicit Haar measure values, used as the reference hull for the comparison region.
Model-level instance only; no new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4S1902HullConcreteActual

open MeasureTheory
open scoped ENNReal

/-- Concrete hull data: a measurable region with finite positive Haar measure. -/
structure ConcreteHullData where
  /-- the hull region. -/
  region : Set Real
  measurable : MeasurableSet region
  measure_eq : volume region = ENNReal.ofReal 2

/-- The concrete S1902-style hull `[-1,1]`. -/
noncomputable def concreteHull : ConcreteHullData where
  region := Set.Icc (-1 : Real) 1
  measurable := measurableSet_Icc
  measure_eq := by
    rw [Real.volume_Icc]
    norm_num

/-- The concrete hull has measure `2`. -/
theorem concreteHull_measure :
    volume (concreteHull.region) = ENNReal.ofReal 2 := by
  exact concreteHull.measure_eq

/-- The concrete hull has positive measure. -/
theorem concreteHull_measure_pos : 0 < volume (concreteHull.region) := by
  rw [concreteHull_measure]
  exact ENNReal.ofReal_pos.mpr (by norm_num)

/-- The concrete hull has finite measure. -/
theorem concreteHull_measure_lt_top : volume (concreteHull.region) < ⊤ := by
  rw [concreteHull_measure]
  exact ENNReal.ofReal_lt_top

#check ConcreteHullData
#check concreteHull
#check concreteHull_measure
#check concreteHull_measure_pos
#check concreteHull_measure_lt_top

end LeanFormal.IUT.XiFPaper.Mzk1Stage4S1902HullConcreteActual
end
