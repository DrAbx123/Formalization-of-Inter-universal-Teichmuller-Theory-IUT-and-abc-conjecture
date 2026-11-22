import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceIndTopology
import LeanFormal.IUT.Foundations.LocalFields.FiniteLocalSubfieldCofinality
import LeanFormal.IUT.Foundations.LocalFields.UnitPerfectionIndCofinality

/-!
# The actual completion gives a cofinal base for the ind topology

Its image in the actual algebraic closure is a finite Qp subfield.
Restricting to finite subfields containing this image leaves the field
ind topology unchanged, matching the finite-base-extension layers in
IUT III Proposition 3.1.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldLogarithm

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def sourceCompletionAlgHom (place : NumberField.FinitePlace K) :
    NormalizedCompletion place →ₐ[PadicScalarField place] SourceAlgebraicClosure place :=
  IsScalarTower.toAlgHom _ _ _

def sourceCompletionFieldRange (place : NumberField.FinitePlace K) :
    FiniteLocalSubfield (completionRationalPrime place).val (SourceAlgebraicClosure place) :=
  ⟨(sourceCompletionAlgHom place).fieldRange,
    FiniteDimensional.of_surjective
      (sourceCompletionAlgHom place).equivFieldRange.toLinearEquiv.toLinearMap
      (sourceCompletionAlgHom place).equivFieldRange.surjective⟩

def sourceCompletionFieldRangeEquiv (place : NumberField.FinitePlace K) :
    NormalizedCompletion place ≃ₐ[PadicScalarField place] (sourceCompletionFieldRange place).val :=
  (sourceCompletionAlgHom place).equivFieldRange

theorem mem_sourceCompletionFieldRange_iff (place : NumberField.FinitePlace K)
    (x : SourceAlgebraicClosure place) :
    x ∈ (sourceCompletionFieldRange place).val ↔
      ∃ a : NormalizedCompletion place,
        algebraMap (NormalizedCompletion place) (SourceAlgebraicClosure place) a = x := Iff.rfl

theorem sourceFiniteBaseLayers_cofinal (place : NumberField.FinitePlace K)
    (F : FiniteLocalSubfield (completionRationalPrime place).val (SourceAlgebraicClosure place)) :
    ∃ H : FiniteLocalSubfieldAbove (sourceCompletionFieldRange place), F.val ≤ H.val.val :=
  finiteLocalSubfieldAbove_cofinal _ F

theorem sourceAlgebraicFieldIndTopology_eq_baseLayers (place : NumberField.FinitePlace K) :
    sourceAlgebraicFieldIndTopology place =
      algebraicFieldIndTopologyAbove (sourceCompletionFieldRange place) :=
  (algebraicFieldIndTopologyAbove_eq _).symm

theorem sourceUnitPerfectionIndTopology_eq_baseLayers (place : NumberField.FinitePlace K) :
    sourceUnitPerfectionIndTopology place =
      algebraicUnitPerfectionIndTopologyAbove (sourceCompletionFieldRange place) :=
  (algebraicUnitPerfectionIndTopologyAbove_eq _).symm

def sourceFiniteBaseIntermediateField (place : NumberField.FinitePlace K)
    (H : FiniteLocalSubfieldAbove (sourceCompletionFieldRange place)) :
    IntermediateField (NormalizedCompletion place) (SourceAlgebraicClosure place) where
  carrier := (H.val.val : Set (SourceAlgebraicClosure place))
  zero_mem' := H.val.val.zero_mem
  one_mem' := H.val.val.one_mem
  add_mem' := H.val.val.add_mem
  mul_mem' := H.val.val.mul_mem
  inv_mem' _ hx := H.val.val.inv_mem hx
  algebraMap_mem' a := H.property
    ((mem_sourceCompletionFieldRange_iff place _).mpr ⟨a, rfl⟩)

instance sourceFiniteBaseIntermediateFieldFinite (place : NumberField.FinitePlace K)
    (H : FiniteLocalSubfieldAbove (sourceCompletionFieldRange place)) :
    FiniteDimensional (NormalizedCompletion place) (sourceFiniteBaseIntermediateField place H) := by
  letI : FiniteDimensional (PadicScalarField place) (sourceFiniteBaseIntermediateField place H) :=
    inferInstanceAs (FiniteDimensional (PadicScalarField place) H.val.val)
  exact FiniteDimensional.right (PadicScalarField place) (NormalizedCompletion place)
    (sourceFiniteBaseIntermediateField place H)

theorem sourceFiniteBaseLayer_fixingSubgroup_isOpen (place : NumberField.FinitePlace K)
    (H : FiniteLocalSubfieldAbove (sourceCompletionFieldRange place)) :
    IsOpen ((sourceFiniteBaseIntermediateField place H).fixingSubgroup :
      Set (SourceAlgebraicClosure place ≃ₐ[NormalizedCompletion place]
        SourceAlgebraicClosure place)) :=
  IntermediateField.fixingSubgroup_isOpen _

theorem sourceFiniteBaseLayer_fixedField_fixingSubgroup (place : NumberField.FinitePlace K)
    (H : FiniteLocalSubfieldAbove (sourceCompletionFieldRange place)) :
    IntermediateField.fixedField (sourceFiniteBaseIntermediateField place H).fixingSubgroup =
      sourceFiniteBaseIntermediateField place H :=
  InfiniteGalois.fixedField_fixingSubgroup _

end

end LeanFormal.IUT.NumberFieldFinitePlace
