import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorFieldDecomposition

/-!
# Finite local-field decomposition for tensors of finite etale packets

The factors may be finite products of actual completions. Their finite
etale tensor is classified into finite extension fields, with actual
extension norms and a continuous algebra equivalence in both directions.
-/

namespace LeanFormal.IUT.LocalFieldPadicTensor

noncomputable section

universe u v

variable {p : ℕ} [Fact p.Prime] {ι : Type u} [Fintype ι]
variable (A : ι → Type v) [∀ i, NormedCommRing (A i)] [∀ i, NormedAlgebra ℚ_[p] (A i)]
variable [∀ i, FiniteDimensional ℚ_[p] (A i)] [∀ i, Algebra.Etale ℚ_[p] (A i)]

omit [Fintype ι] in
instance finitePadicEtaleTensorEtale [Finite ι] :
    Algebra.Etale ℚ_[p] (FinitePadicTensor (p := p) A) := by
  letI := Fintype.ofFinite ι
  letI : Algebra.FormallyEtale ℚ_[p] (FinitePadicTensor (p := p) A) :=
    LocalFieldTensorDecomposition.finiteTensor_formallyEtale
  exact ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

theorem exists_finiteNormedFieldProduct_etaleTensor :
    ∃ (J : Type (max u v)) (_ : Fintype J) (E : J → Type (max u v))
      (_ : ∀ j, NontriviallyNormedField (E j)) (_ : ∀ j, NormedAlgebra ℚ_[p] (E j))
      (e : FinitePadicTensor (p := p) A ≃ₐ[ℚ_[p]] ((j : J) → E j)),
      (∀ j, FiniteDimensional ℚ_[p] (E j) ∧ CompleteSpace (E j) ∧ IsUltrametricDist (E j)) ∧
        Continuous e ∧ Continuous e.symm := by
  obtain ⟨J, hJ, E, hfield, halgebra, e, hE⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod ℚ_[p] (FinitePadicTensor (p := p) A)).mp inferInstance
  letI := hJ
  letI : Fintype J := Fintype.ofFinite J
  letI := hfield
  letI := halgebra
  letI : ∀ j, Module.Finite ℚ_[p] (E j) := fun j => (hE j).1
  letI : ∀ j, NontriviallyNormedField (E j) := fun j =>
    spectralNorm.nontriviallyNormedField ℚ_[p] (E j)
  letI : ∀ j, NormedAlgebra ℚ_[p] (E j) := fun j =>
    spectralNorm.normedAlgebra ℚ_[p] (E j)
  let e' : FinitePadicTensor (p := p) A ≃ₐ[ℚ_[p]] ((j : J) → E j) := e
  refine ⟨J, inferInstance, E, inferInstance, inferInstance, e', ?_, ?_, ?_⟩
  · intro j
    refine ⟨inferInstance, spectralNorm.completeSpace ℚ_[p] (E j), ?_⟩
    apply IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
    exact isNonarchimedean_spectralNorm
  · exact e'.toLinearEquiv.toContinuousLinearEquiv.continuous
  · exact e'.symm.toLinearEquiv.toContinuousLinearEquiv.continuous

end

end LeanFormal.IUT.LocalFieldPadicTensor
