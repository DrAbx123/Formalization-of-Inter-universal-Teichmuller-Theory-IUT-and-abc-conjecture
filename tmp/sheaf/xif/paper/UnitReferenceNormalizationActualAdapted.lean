import tmp.sheaf.xif.paper.HaarUnitFactorProof
import Mathlib

/-! # CONDITIONAL STATUS (xi-f)

Proves an obstruction (arbitrary Haar scaling can make unit-reference mass != 1). The source-selected Haar normalization is missing; no unconditional UnitReferenceMeasureGeOne.

This module is NOT an unconditional target closure. Do not use it as evidence that paper xi-f is proved; read its exact Missing declarations and the audit ledger.
-/


set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Unit-reference Haar normalization: attempted proof and exact missing theorem

Task-617 write-only attempt.

The target is

  UnitReferenceMeasureGeOne places tuple mu :
    1 <= (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal.

The actual unit-reference region is the compact canonical unit reference of
FinitePlaceArithmeticTupleCanonicalHull. Its measure is positive and finite
(measure_arithmeticTupleCanonicalRegions_pos_lt_top), but no theorem in the
tree fixes its Haar normalization.

Exact obstruction proved here: the assertion is not invariant under the
permitted Haar scaling. For any additive Haar measure mu and any positive
finite scalar c, c • mu is again an additive Haar measure, and

  ((c • mu) unitReference).toReal = c.toReal * (mu unitReference).toReal.

Choosing c.toReal = 1 / (2 * (mu unitReference).toReal) makes the scaled
unit-reference measure equal to 1/2, so UnitReferenceMeasureGeOne fails.

Therefore the target is not derivable for an arbitrary Haar measure mu; the
exact missing datum is a source normalization theorem selecting the Haar
measure with unit-reference mass at least one (or an equivalent
fundamental-domain/unit-region normalization identity).

No arbitrary inequality, toy data, True/PUnit, axiom, or sorry is used.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.UnitReferenceNormalizationActualAdapted

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

/-- The exact missing normalization theorem: the selected Haar measure has
unit-reference mass at least one. This is the existing target, not an axiom. -/
abbrev UnitReferenceNormalization : Prop :=
  UnitReferenceMeasureGeOne places tuple mu

/-- The actual unit-reference measure is positive. -/
theorem unitReference_measure_pos :
    0 < mu (arithmeticTupleCanonicalUnitReference places tuple) :=
  (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu).2.1

/-- The actual unit-reference measure is finite. -/
theorem unitReference_measure_lt_top :
    mu (arithmeticTupleCanonicalUnitReference places tuple) < ⊤ :=
  (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu).2.2

/-- The positive real unit-reference mass. -/
def unitReferenceMass : Real :=
  (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal

theorem unitReferenceMass_pos : 0 < unitReferenceMass places tuple mu :=
  ENNReal.toReal_pos (unitReference_measure_pos places tuple mu).ne'
    (unitReference_measure_lt_top places tuple mu).ne

/-- A positive finite Haar scaling that forces unit-reference mass below one. -/
noncomputable def smallHaarScalar : ENNReal :=
  ENNReal.ofReal ((2 * unitReferenceMass places tuple mu)⁻¹)

theorem smallHaarScalar_ne_zero : smallHaarScalar places tuple mu ≠ 0 := by
  unfold smallHaarScalar
  exact ENNReal.ofReal_pos.mpr
    (inv_pos.mpr (mul_pos two_pos (unitReferenceMass_pos places tuple mu))).ne'

theorem smallHaarScalar_ne_top : smallHaarScalar places tuple mu ≠ ⊤ :=
  ENNReal.ofReal_ne_top

/-- The scaled measure is again an additive Haar measure. -/
theorem smallHaarScalar_addHaar :
    Measure.IsAddHaarMeasure
      (smallHaarScalar places tuple mu • mu) :=
  IsAddHaarMeasure.smul
    (smallHaarScalar_ne_zero places tuple mu)
    (smallHaarScalar_ne_top places tuple mu)

/-- Exact computation of the scaled unit-reference mass. -/
theorem smallHaarScalar_unitReference_measure :
    (smallHaarScalar places tuple mu • mu)
        (arithmeticTupleCanonicalUnitReference places tuple) =
      smallHaarScalar places tuple mu *
        mu (arithmeticTupleCanonicalUnitReference places tuple) := by
  rw [Measure.smul_apply, smul_eq_mul]

/-- The scaled unit-reference real mass is one half. -/
theorem smallHaarScalar_unitReference_toReal :
    ((smallHaarScalar places tuple mu • mu)
        (arithmeticTupleCanonicalUnitReference places tuple)).toReal = 1 / 2 := by
  rw [smallHaarScalar_unitReference_measure, ENNReal.toReal_mul]
  unfold smallHaarScalar
  rw [ENNReal.toReal_ofReal]
  · have hM : unitReferenceMass places tuple mu ≠ 0 :=
      (unitReferenceMass_pos places tuple mu).ne'
    unfold unitReferenceMass
    field_simp [hM]
    ring
  · exact le_of_lt (inv_pos.mpr
      (mul_pos two_pos (unitReferenceMass_pos places tuple mu)))

/-- Counterexample theorem: the unit-reference normalization fails for the
canonical Haar rescaling. -/
theorem unitReferenceNormalization_fails_of_smallHaarScalar :
    ¬ UnitReferenceMeasureGeOne places tuple mu
        (smallHaarScalar places tuple mu • mu) := by
  intro h
  have hhalf := smallHaarScalar_unitReference_toReal places tuple mu
  rw [hhalf] at h
  norm_num at h

/-- The exact non-provability statement for an arbitrary additive Haar
measure: there is a positive finite Haar rescaling violating the target. -/
theorem unitReferenceMeasureGeOne_not_forall_of_haar :
    ∃ (mu' : Measure (ArithmeticTensorTupleBlock places tuple))
      (_ : Measure.IsAddHaarMeasure mu'),
      ¬ UnitReferenceMeasureGeOne places tuple mu' :=
  ⟨smallHaarScalar places tuple mu • mu,
    smallHaarScalar_addHaar places tuple mu,
    unitReferenceNormalization_fails_of_smallHaarScalar places tuple mu⟩

/-- Exact missing normalization theorem: a source-selected Haar measure (or a
fundamental-domain normalization identity) with unit-reference mass at least
one. Only this datum would discharge UnitReferenceMeasureGeOne. -/
def MissingUnitReferenceNormalizationTheorem : Prop :=
  UnitReferenceMeasureGeOne places tuple mu

end LeanFormal.IUT.XiFPaper.UnitReferenceNormalizationActualAdapted

end
