import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceIndCofinality

/-!
# The actual finite-base layers and open absolute Galois subgroups

Restricting scalars from K_v to Qp gives the inverse of the previously
constructed finite layer. The infinite Galois correspondence then
identifies these finite layers with the actual open fixing subgroups.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldLogarithm

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

abbrev SourceFiniteBaseLayer (place : NumberField.FinitePlace K) :=
  { E : IntermediateField (NormalizedCompletion place) (SourceAlgebraicClosure place) //
    FiniteDimensional (NormalizedCompletion place) E }

def sourcePadicLayerToBaseLayer (place : NumberField.FinitePlace K)
    (H : FiniteLocalSubfieldAbove (sourceCompletionFieldRange place)) :
    SourceFiniteBaseLayer place := ⟨sourceFiniteBaseIntermediateField place H, inferInstance⟩

def sourceBaseLayerToPadicLayer (place : NumberField.FinitePlace K)
    (E : SourceFiniteBaseLayer place) :
    FiniteLocalSubfieldAbove (sourceCompletionFieldRange place) := by
  letI := E.property
  refine ⟨⟨E.val.restrictScalars (PadicScalarField place), ?_⟩, ?_⟩
  · exact FiniteDimensional.trans (PadicScalarField place) (NormalizedCompletion place) E.val
  · intro x hx
    obtain ⟨a, rfl⟩ := (mem_sourceCompletionFieldRange_iff place x).mp hx
    exact E.val.algebraMap_mem a

def sourceFiniteBaseLayerEquiv (place : NumberField.FinitePlace K) :
    FiniteLocalSubfieldAbove (sourceCompletionFieldRange place) ≃ SourceFiniteBaseLayer place where
  toFun := sourcePadicLayerToBaseLayer place
  invFun := sourceBaseLayerToPadicLayer place
  left_inv H := by
    apply Subtype.ext
    apply Subtype.ext
    ext x
    rfl
  right_inv E := by
    apply Subtype.ext
    ext x
    rfl

def sourceFiniteBaseLayerFixingSubgroup (place : NumberField.FinitePlace K)
    (E : SourceFiniteBaseLayer place) :
    OpenSubgroup (SourceAlgebraicClosure place ≃ₐ[NormalizedCompletion place]
      SourceAlgebraicClosure place) := by
  letI := E.property
  exact ⟨E.val.fixingSubgroup, IntermediateField.fixingSubgroup_isOpen E.val⟩

def sourceOpenSubgroupFixedLayer (place : NumberField.FinitePlace K)
    (U : OpenSubgroup (SourceAlgebraicClosure place ≃ₐ[NormalizedCompletion place]
      SourceAlgebraicClosure place)) : SourceFiniteBaseLayer place := by
  let C : ClosedSubgroup (SourceAlgebraicClosure place ≃ₐ[NormalizedCompletion place]
      SourceAlgebraicClosure place) := ⟨U.toSubgroup, U.isClosed⟩
  refine ⟨IntermediateField.fixedField U.toSubgroup, ?_⟩
  apply (InfiniteGalois.isOpen_iff_finite _).mp
  rw [InfiniteGalois.fixingSubgroup_fixedField C]
  exact U.isOpen'

def sourceFiniteBaseLayerOpenSubgroupEquiv (place : NumberField.FinitePlace K) :
    SourceFiniteBaseLayer place ≃
      OpenSubgroup (SourceAlgebraicClosure place ≃ₐ[NormalizedCompletion place]
        SourceAlgebraicClosure place) where
  toFun := sourceFiniteBaseLayerFixingSubgroup place
  invFun := sourceOpenSubgroupFixedLayer place
  left_inv E := by
    apply Subtype.ext
    exact InfiniteGalois.fixedField_fixingSubgroup E.val
  right_inv U := by
    let C : ClosedSubgroup (SourceAlgebraicClosure place ≃ₐ[NormalizedCompletion place]
        SourceAlgebraicClosure place) := ⟨U.toSubgroup, U.isClosed⟩
    apply SetLike.coe_injective
    exact congrArg (fun H : Subgroup (SourceAlgebraicClosure place ≃ₐ[NormalizedCompletion place]
        SourceAlgebraicClosure place) => H.carrier)
      (InfiniteGalois.fixingSubgroup_fixedField C)

end

end LeanFormal.IUT.NumberFieldFinitePlace
