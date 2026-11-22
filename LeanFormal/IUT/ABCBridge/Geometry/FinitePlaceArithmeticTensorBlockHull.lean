import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlockFields

/-!
# The actual arithmetic log-shell hull is a product of tuple hulls

The tuple field decompositions exist by finite etale classification. For
any such family, compactness and the tensor identity verify the bounded,
nondegenerate domain of the proved block-hull formula. The original pure
tensor region is not replaced by a Cartesian product.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldPadicTensor LeanFormal.IUT.LocalFieldProductHull

noncomputable section

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w} [∀ i, Fintype (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable {J : ((i : ι) → V i) → Type*}
variable {E : (tuple : (i : ι) → V i) → J tuple → Type*}
variable [∀ tuple j, NormedField (E tuple j)] [∀ tuple j, NormedAlgebra ℚ_[p] (E tuple j)]

def arithmeticBlockFieldLogImage
    (e : ∀ tuple, ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J tuple) → E tuple j)) :
    Set ((w : Sigma J) → E w.1 w.2) :=
  arithmeticBlockFieldAlgEquiv places e '' arithmeticTensorLogRegion places

theorem isCompact_arithmeticBlockFieldLogImage
    (e : ∀ tuple, ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J tuple) → E tuple j)) :
    IsCompact (arithmeticBlockFieldLogImage places e) :=
  (isCompact_arithmeticTensorLogRegion places).image
    (continuous_arithmeticBlockFieldAlgEquiv places e)

theorem one_mem_arithmeticBlockFieldLogImage
    (e : ∀ tuple, ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J tuple) → E tuple j)) :
    (1 : (w : Sigma J) → E w.1 w.2) ∈ arithmeticBlockFieldLogImage places e :=
  ⟨1, one_mem_arithmeticTensorLogRegion places, (arithmeticBlockFieldAlgEquiv places e).map_one⟩

theorem arithmeticBlockFieldLogImage_projection
    (e : ∀ tuple, ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J tuple) → E tuple j))
    (tuple : (i : ι) → V i) :
    blockProjection tuple '' arithmeticBlockFieldLogImage places e =
      e tuple '' arithmeticTensorTupleLogRegion places tuple := by
  unfold arithmeticBlockFieldLogImage
  rw [Set.image_image]
  change (fun x => e tuple (arithmeticTensorTupleProjection places tuple x)) ''
    arithmeticTensorLogRegion places = _
  rw [← Set.image_image, arithmeticTensorTupleProjection_image_logRegion]

theorem arithmeticBlockFieldHull_eq_pi
    (e : ∀ tuple, ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J tuple) → E tuple j)) :
    blockCoordinatesHomeomorph '' hull (arithmeticBlockFieldLogImage places e) =
      Set.pi Set.univ
        (fun tuple => hull (e tuple '' arithmeticTensorTupleLogRegion places tuple)) := by
  rw [blockCoordinatesHomeomorph_image_hull
    (isCompact_arithmeticBlockFieldLogImage places e)
    ⟨1, one_mem_arithmeticBlockFieldLogImage places e⟩
    (fun _ => ⟨1, one_mem_arithmeticBlockFieldLogImage places e, one_ne_zero⟩)]
  congr 1
  funext tuple
  rw [arithmeticBlockFieldLogImage_projection]

theorem exists_realized_arithmeticBlockFieldHull :
    ∃ (J : ((i : ι) → V i) → Type (max u v)) (_ : ∀ tuple, Fintype (J tuple))
      (E : (tuple : (i : ι) → V i) → J tuple → Type (max u v))
      (_ : ∀ tuple j, NontriviallyNormedField (E tuple j))
      (_ : ∀ tuple j, NormedAlgebra ℚ_[p] (E tuple j))
      (e : ∀ tuple, ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J tuple) → E tuple j)),
      (∀ tuple, (∀ j, FiniteDimensional ℚ_[p] (E tuple j) ∧ CompleteSpace (E tuple j) ∧
        IsUltrametricDist (E tuple j)) ∧ Continuous (e tuple) ∧ Continuous (e tuple).symm) ∧
      blockCoordinatesHomeomorph '' hull (arithmeticBlockFieldLogImage places e) =
        Set.pi Set.univ
          (fun tuple => hull (e tuple '' arithmeticTensorTupleLogRegion places tuple)) := by
  obtain ⟨J, hJ, E, hfield, halgebra, e, hprops⟩ :=
    exists_arithmeticTensorBlock_fieldProducts places
  letI := hJ
  letI := hfield
  letI := halgebra
  exact ⟨J, hJ, E, hfield, halgebra, e, hprops, arithmeticBlockFieldHull_eq_pi places e⟩

end

end LeanFormal.IUT.NumberFieldFinitePlace
