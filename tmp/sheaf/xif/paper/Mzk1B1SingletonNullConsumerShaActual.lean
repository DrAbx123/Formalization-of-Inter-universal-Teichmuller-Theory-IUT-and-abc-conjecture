import tmp.sheaf.xif.paper.Mzk1StepXISinglePointNullV2Actual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
import Mathlib.Tactic

/-!
# shehdd A672 B1 single-point null consumer (Sha, read-only)

Consumes the green stepxi B1 file `Mzk1StepXISinglePointNullV2Actual` and derives
the log-volume-zero consequences used when splitting a region `unitRegion ∪ {point}`:
* `b1_single_point_measure_zero`;
* `b1_single_point_logVolume_zero`;
* `b1_finite_set_logVolume_zero`.

The hull-specific product-carrier `NoAtoms` instance is still PENDING_HULL
(`Mzk1ProductHaarSingletonActual`); this file is the generic B1 interface evidence.

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1B1SingletonNullConsumerShaActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1StepXISinglePointNullV2Actual
open MeasureTheory

section Generic

variable {X : Type*} [MeasurableSpace X]
variable (mu : Measure X) [NullSingletonClass mu]

/-- B1, measure form: singleton null. -/
theorem b1_single_point_measure_zero (x : X) : mu ({x} : Set X) = 0 :=
  single_point_null mu x

/-- B1, log-volume form: singleton log-volume zero. -/
theorem b1_single_point_logVolume_zero (x : X) :
    haarLogVolume mu ({x} : Set X) = 0 :=
  haarLogVolume_eq_zero_of_null (single_point_null mu x)

/-- B1, finite-set form: finite-set log-volume zero. -/
theorem b1_finite_set_logVolume_zero (s : Finset X) :
    haarLogVolume mu (s : Set X) = 0 :=
  haarLogVolume_eq_zero_of_null (finite_set_null mu s)

end Generic

structure B1Row where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def b1Rows : List B1Row :=
  [ ⟨"generic singleton null", "stepxi Mzk1StepXISinglePointNullV2Actual.single_point_null", "GREEN_SOURCE"⟩
  , ⟨"B1 log-volume zero", "b1_single_point_logVolume_zero", "GREEN"⟩
  , ⟨"B1 finite set", "b1_finite_set_logVolume_zero", "GREEN"⟩
  , ⟨"hull product carrier NoAtoms", "Mzk1ProductHaarSingletonActual (hull, pending)", "PENDING_HULL"⟩
  , ⟨"scope", "generic B1 interface only; no gap claimed", "INTEGRITY"⟩
  ]

theorem b1Rows_length : b1Rows.length = 5 := rfl

theorem b1Rows_statuses_ok :
    b1Rows.all (fun r =>
      r.status ∈ ["GREEN_SOURCE", "GREEN", "PENDING_HULL", "INTEGRITY"]) = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1B1SingletonNullConsumerShaActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1B1SingletonNullConsumerShaActual.b1_single_point_measure_zero
#print axioms LeanFormal.IUT.XiFPaper.Mzk1B1SingletonNullConsumerShaActual.b1_single_point_logVolume_zero
#print axioms LeanFormal.IUT.XiFPaper.Mzk1B1SingletonNullConsumerShaActual.b1_finite_set_logVolume_zero
