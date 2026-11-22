import tmp.sheaf.xif.paper.HaarUnitFactorProof

/-! # CONDITIONAL STATUS (xi-f)

Conditional on UnitReferenceNormalizationPrimitive (unit-reference measure normalization). Only positivity/finiteness are actual; the normalization choice is missing.

This module is NOT an unconditional target closure. Do not use it as evidence that paper xi-f is proved; read its exact Missing declarations and the audit ledger.
-/


/-! # Actual unit-reference measure attempt (write-only)

Task-604.  Target:

    UnitReferenceMeasureGeOne places tuple mu
    := 1 <= (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal.

## What is actually available

* `measure_arithmeticTupleCanonicalRegions_pos_lt_top` gives
  `0 < mu unitReference` and `mu unitReference < top` for every actual
  additive Haar measure `mu`.
* `arithmeticTupleCanonicalRegions_relativeLogVolume` gives the exact
  relative-log identity with the hull.
* No theorem normalizes the actual additive Haar measure at the canonical
  unit reference to `= 1` or any value `>= 1`.  Additive Haar is defined only
  up to a positive scalar, so positivity/finiteness cannot imply a lower
  bound `1`.

## Proved reduction

For the actual positive finite unit measure, the target is equivalent to
`0 <= Real.log (mu unitReference).toReal`, and follows from the exact
normalization identity `mu unitReference = 1`.  The latter is the missing
source normalization; it is an explicit primitive here, not a theorem.

No arbitrary inequality, PUnit, True, sorry, or axiom is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper

open LeanFormal.IUT
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type v} [Fintype iota] {V : iota -> Type w}
variable (places : (i : iota) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : iota) -> V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure mu]

abbrev UnitReference : Set (ArithmeticTensorTupleBlock places tuple) :=
  arithmeticTupleCanonicalUnitReference places tuple

theorem unitReference_measure_pos :
    0 < mu (UnitReference places tuple) :=
  (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu).2.1

theorem unitReference_measure_lt_top :
    mu (UnitReference places tuple) < ⊤ :=
  (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu).2.2

/-- The real unit-reference measure is positive and finite. -/
theorem unitReference_toReal_pos :
    0 < (mu (UnitReference places tuple)).toReal :=
  ENNReal.toReal_pos (unitReference_measure_pos places tuple mu).ne'
    (unitReference_measure_lt_top places tuple mu).ne

/-- The target is exactly nonnegativity of the real log of the unit measure. -/
theorem unitReferenceMeasureGeOne_iff_log_nonneg :
    UnitReferenceMeasureGeOne places tuple mu ↔
      0 ≤ Real.log (mu (UnitReference places tuple)).toReal := by
  unfold UnitReferenceMeasureGeOne
  exact (Real.log_nonneg_iff (unitReference_toReal_pos places tuple mu)).symm

/-- Exact normalization primitive: the canonical unit reference has actual
Haar measure one.  This is the missing source normalization; it is a field of
a structure here, not an asserted theorem. -/
structure UnitReferenceNormalizationPrimitive where
  unitReference_measure_eq_one : mu (UnitReference places tuple) = 1

theorem unitReferenceMeasureGeOne_of_eq_one
    (h : mu (UnitReference places tuple) = 1) :
    UnitReferenceMeasureGeOne places tuple mu := by
  unfold UnitReferenceMeasureGeOne
  rw [h, ENNReal.toReal_one]

theorem unitReferenceMeasureGeOne_of_primitive
    (P : UnitReferenceNormalizationPrimitive places tuple mu) :
    UnitReferenceMeasureGeOne places tuple mu :=
  unitReferenceMeasureGeOne_of_eq_one places tuple mu P.unitReference_measure_eq_one

/-- If the actual unit-reference log is nonnegative, the target holds. -/
theorem unitReferenceMeasureGeOne_of_log_nonneg
    (h : 0 ≤ Real.log (mu (UnitReference places tuple)).toReal) :
    UnitReferenceMeasureGeOne places tuple mu :=
  (unitReferenceMeasureGeOne_iff_log_nonneg places tuple mu).mpr h

/-- The exact missing measure identity is not derivable from positivity and
finiteness alone; this records it as a primitive proposition. -/
def UnitReferenceMeasureIdentityRequired : Prop :=
  Nonempty (UnitReferenceNormalizationPrimitive places tuple mu)

/-- Conditional canonical-hull log nonnegativity from the exact normalization. -/
theorem canonicalHullLog_nonneg_of_unitReferenceNormalization
    (P : UnitReferenceNormalizationPrimitive places tuple mu) :
    CanonicalHullLogNonneg places tuple mu :=
  canonicalHullLog_nonneg_of_unitReferenceMeasureGeOne places tuple mu
    (unitReferenceMeasureGeOne_of_primitive places tuple mu P)

end LeanFormal.IUT.XiFPaper

end
