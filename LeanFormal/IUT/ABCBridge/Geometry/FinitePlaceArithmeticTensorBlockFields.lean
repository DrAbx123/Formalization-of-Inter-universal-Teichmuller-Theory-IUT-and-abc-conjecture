import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldProductHullBlocks

/-!
# Actual field-product decompositions inside each place-tuple block

Finite etale classification is applied to the actual completion tensor at
each tuple. The assembled field-product equivalence retains the tuple labels.
No hypothetical decomposition or compatibility field is introduced.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldPadicTensor LeanFormal.IUT.LocalFieldProductHull

noncomputable section

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w} [∀ i, Fintype (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)

omit [∀ i, Fintype (V i)] in
theorem exists_arithmeticTensorTuple_fieldProduct (tuple : (i : ι) → V i) :
    ∃ (J : Type (max u v)) (_ : Fintype J) (E : J → Type (max u v))
      (_ : ∀ j, NontriviallyNormedField (E j)) (_ : ∀ j, NormedAlgebra ℚ_[p] (E j))
      (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j)),
      (∀ j, FiniteDimensional ℚ_[p] (E j) ∧ CompleteSpace (E j) ∧ IsUltrametricDist (E j)) ∧
        Continuous e ∧ Continuous e.symm := by
  letI : ∀ i, Algebra.FormallyEtale ℚ_[p] (CommonPrimeCompletion (places i (tuple i))) :=
    fun _ => Algebra.FormallyEtale.of_isSeparable _ _
  letI : ∀ i, Algebra.Etale ℚ_[p] (CommonPrimeCompletion (places i (tuple i))) :=
    fun _ => ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  exact exists_finiteNormedFieldProduct_etaleTensor
    (fun i => CommonPrimeCompletion (places i (tuple i)))

omit [∀ i, Fintype (V i)] in
theorem exists_arithmeticTensorBlock_fieldProducts :
    ∃ (J : ((i : ι) → V i) → Type (max u v)) (_ : ∀ tuple, Fintype (J tuple))
      (E : (tuple : (i : ι) → V i) → J tuple → Type (max u v))
      (_ : ∀ tuple j, NontriviallyNormedField (E tuple j))
      (_ : ∀ tuple j, NormedAlgebra ℚ_[p] (E tuple j))
      (e : ∀ tuple, ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J tuple) → E tuple j)),
      ∀ tuple, (∀ j, FiniteDimensional ℚ_[p] (E tuple j) ∧ CompleteSpace (E tuple j) ∧
        IsUltrametricDist (E tuple j)) ∧ Continuous (e tuple) ∧ Continuous (e tuple).symm := by
  choose J hJ E hfield halgebra e hprops using
    (fun tuple => exists_arithmeticTensorTuple_fieldProduct places tuple)
  exact ⟨J, hJ, E, hfield, halgebra, e, hprops⟩

variable {J : ((i : ι) → V i) → Type*}
variable {E : (tuple : (i : ι) → V i) → J tuple → Type*}
variable [∀ tuple j, NormedField (E tuple j)] [∀ tuple j, NormedAlgebra ℚ_[p] (E tuple j)]

def arithmeticBlockFieldAlgEquiv
    (e : ∀ tuple, ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J tuple) → E tuple j)) :
    ArithmeticPacketTensor places ≃ₐ[ℚ_[p]] ((w : Sigma J) → E w.1 w.2) :=
  ((arithmeticTensorBlocksAlgEquiv places).trans (AlgEquiv.piCongrRight e)).trans
    (blockCoordinatesAlgEquiv (K := fun w : Sigma J => E w.1 w.2) ℚ_[p]).symm

theorem arithmeticBlockFieldAlgEquiv_blockProjection
    (e : ∀ tuple, ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J tuple) → E tuple j))
    (x : ArithmeticPacketTensor places) (tuple : (i : ι) → V i) :
    blockProjection tuple (arithmeticBlockFieldAlgEquiv places e x) =
      e tuple (arithmeticTensorTupleProjection places tuple x) := rfl

theorem continuous_arithmeticBlockFieldAlgEquiv
    (e : ∀ tuple, ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J tuple) → E tuple j)) :
    Continuous (arithmeticBlockFieldAlgEquiv places e) :=
  (arithmeticBlockFieldAlgEquiv places e).toLinearMap.continuous_of_finiteDimensional

theorem continuous_arithmeticBlockFieldAlgEquiv_symm
    (e : ∀ tuple, ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J tuple) → E tuple j)) :
    Continuous (arithmeticBlockFieldAlgEquiv places e).symm := by
  letI : FiniteDimensional ℚ_[p] ((w : Sigma J) → E w.1 w.2) :=
    Module.Finite.of_surjective (arithmeticBlockFieldAlgEquiv places e).toLinearMap
      (arithmeticBlockFieldAlgEquiv places e).surjective
  exact (arithmeticBlockFieldAlgEquiv places e).symm.toLinearMap.continuous_of_finiteDimensional

end

end LeanFormal.IUT.NumberFieldFinitePlace
