import tmp.sheaf.xif.paper.HaarUnitFactorProof
import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Actual Haar unit-reference normalization object

Task-631 write-only construction.

Given an actual additive Haar measure mu on the arithmetic tensor block, this
file constructs the canonical Haar normalization selected by the actual
canonical unit region:

  normalizationScalar := ofReal ((mu unitReference).toReal)^-1,
  normalizedMeasure   := normalizationScalar • mu.

The scalar is not an arbitrary scaling: it is exactly the reciprocal of the
actual source canonical-unit-region mass. The constructed measure has
unit-reference real mass one, hence UnitReferenceMeasureGeOne holds for it
unconditionally.

The object records:
* the actual normalized Haar measure;
* its additive Haar property;
* the source unit-reference mass data used to select the scaling;
* the proved unit-reference real-mass-one normalization.

No arbitrary scaling, inequality assumption, True/PUnit, axiom, or sorry is
used. No source-selected normalization other than the canonical unit-region
normalization is asserted.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.HaarUnitReferenceNormalizationActual

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

/-- The actual canonical unit-reference mass. -/
def canonicalUnitMass : Real :=
  (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal

theorem canonicalUnitMass_pos : 0 < canonicalUnitMass places tuple mu :=
  ENNReal.toReal_pos
    (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu).2.1.ne'
    (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu).2.2.ne

/-- The canonical normalization scalar: reciprocal of the actual unit-region
mass. -/
def normalizationScalar : ENNReal :=
  ENNReal.ofReal ((canonicalUnitMass places tuple mu)⁻¹)

theorem normalizationScalar_ne_zero : normalizationScalar places tuple mu ≠ 0 := by
  unfold normalizationScalar
  exact ENNReal.ofReal_pos.mpr
    (inv_pos.mpr (canonicalUnitMass_pos places tuple mu)).ne'

theorem normalizationScalar_ne_top : normalizationScalar places tuple mu ≠ ⊤ :=
  ENNReal.ofReal_ne_top

/-- The actual normalized Haar measure. -/
def normalizedMeasure : Measure (ArithmeticTensorTupleBlock places tuple) :=
  normalizationScalar places tuple mu • mu

/-- The normalized measure is an additive Haar measure. -/
theorem normalizedMeasure_addHaar :
    Measure.IsAddHaarMeasure (normalizedMeasure places tuple mu) :=
  IsAddHaarMeasure.smul
    (normalizationScalar_ne_zero places tuple mu)
    (normalizationScalar_ne_top places tuple mu)

/-- The normalized unit-reference mass in ENNReal form. -/
theorem normalizedMeasure_unitReference :
    normalizedMeasure places tuple mu
        (arithmeticTupleCanonicalUnitReference places tuple) =
      normalizationScalar places tuple mu *
        mu (arithmeticTupleCanonicalUnitReference places tuple) := by
  unfold normalizedMeasure
  rw [Measure.smul_apply, smul_eq_mul]

/-- The normalized unit-reference real mass is exactly one. -/
theorem normalizedMeasure_unitReference_toReal :
    (normalizedMeasure places tuple mu
        (arithmeticTupleCanonicalUnitReference places tuple)).toReal = 1 := by
  rw [normalizedMeasure_unitReference, ENNReal.toReal_mul]
  unfold normalizationScalar canonicalUnitMass
  rw [ENNReal.toReal_ofReal (le_of_lt (inv_pos.mpr (canonicalUnitMass_pos places tuple mu)))]
  have hM : (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal ≠ 0 :=
    (canonicalUnitMass_pos places tuple mu).ne'
  field_simp [hM]

/-- The constructed normalization satisfies the actual unit-reference
normalization inequality. -/
theorem normalizedMeasure_unitReference_ge_one :
    UnitReferenceMeasureGeOne places tuple mu
      (normalizedMeasure places tuple mu) := by
  unfold UnitReferenceMeasureGeOne
  rw [normalizedMeasure_unitReference_toReal]
  norm_num

/-- The actual source-selected Haar unit-reference normalization object. -/
structure HaarUnitReferenceNormalization where
  /-- The normalized measure. -/
  measure : Measure (ArithmeticTensorTupleBlock places tuple)
  /-- It is an additive Haar measure. -/
  isAddHaar : Measure.IsAddHaarMeasure measure
  /-- The actual canonical unit-region mass used as normalization factor. -/
  unitMass : Real
  unitMass_pos : 0 < unitMass
  /-- The real unit-reference mass of the normalized measure. -/
  unitReference_realMass :
    (measure (arithmeticTupleCanonicalUnitReference places tuple)).toReal = 1
  /-- The selected normalization inequality. -/
  unitReference_ge_one :
    UnitReferenceMeasureGeOne places tuple mu measure

/-- The actual constructed normalization object. -/
noncomputable def actualHaarUnitReferenceNormalization :
    HaarUnitReferenceNormalization places tuple mu where
  measure := normalizedMeasure places tuple mu
  isAddHaar := normalizedMeasure_addHaar places tuple mu
  unitMass := canonicalUnitMass places tuple mu
  unitMass_pos := canonicalUnitMass_pos places tuple mu
  unitReference_realMass := normalizedMeasure_unitReference_toReal places tuple mu
  unitReference_ge_one := normalizedMeasure_unitReference_ge_one places tuple mu

/-- The constructed object's measure is the canonical scaled measure. -/
theorem actualHaarUnitReferenceNormalization_measure :
    (actualHaarUnitReferenceNormalization places tuple mu).measure =
      normalizedMeasure places tuple mu := rfl

/-- The constructed object has unit-reference real mass one. -/
theorem actualHaarUnitReferenceNormalization_unitReference :
    ((actualHaarUnitReferenceNormalization places tuple mu).measure
        (arithmeticTupleCanonicalUnitReference places tuple)).toReal = 1 :=
  normalizedMeasure_unitReference_toReal places tuple mu

/-- Exact construction status: the canonical unit-region normalization object
is actually constructed from the source unit mass; no missing scalar. -/
theorem actualHaarUnitReferenceNormalization_status :
    Nonempty (HaarUnitReferenceNormalization places tuple mu) :=
  ⟨actualHaarUnitReferenceNormalization places tuple mu⟩

end LeanFormal.IUT.XiFPaper.HaarUnitReferenceNormalizationActual

end
