import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldTensorDecomposition
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

/-!
# Topological field-product decomposition of the genuine finite tensor

Apply the proved finite etale classification to the actual tensor, give
its output fields their Qp extension norms, and use finite-dimensional
continuity in both directions. The algebraic decomposition is thus a
topological decomposition at this actual finite tensor level.
-/

namespace LeanFormal.IUT.LocalFieldPadicTensor

noncomputable section

open scoped TensorProduct

section RingStructure

variable {p : ℕ} [Fact p.Prime] {ι : Type*}
variable (A : ι → Type*) [∀ i, NormedCommRing (A i)] [∀ i, NormedAlgebra ℚ_[p] (A i)]

instance finitePadicTensorCommRing : CommRing (FinitePadicTensor (p := p) A) :=
  inferInstanceAs (CommRing (⨂[ℚ_[p]] i, A i))

instance finitePadicTensorAlgebra : Algebra ℚ_[p] (FinitePadicTensor (p := p) A) :=
  inferInstanceAs (Algebra ℚ_[p] (⨂[ℚ_[p]] i, A i))

end RingStructure

variable {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι]
variable (A : ι → Type) [∀ i, NormedField (A i)] [∀ i, NormedAlgebra ℚ_[p] (A i)]
variable [∀ i, FiniteDimensional ℚ_[p] (A i)]

theorem exists_finiteNormedFieldProduct_piTensor :
    ∃ (J : Type) (_ : Fintype J) (E : J → Type)
      (_ : ∀ j, NontriviallyNormedField (E j)) (_ : ∀ j, NormedAlgebra ℚ_[p] (E j))
      (e : FinitePadicTensor (p := p) A ≃ₐ[ℚ_[p]] ((j : J) → E j)),
      (∀ j, FiniteDimensional ℚ_[p] (E j) ∧ CompleteSpace (E j) ∧ IsUltrametricDist (E j)) ∧
        Continuous e ∧ Continuous e.symm := by
  obtain ⟨J, hJ, E, hfield, halgebra, e, hE⟩ :=
    LocalFieldTensorDecomposition.exists_finiteFieldProduct_piTensor ℚ_[p] A
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

theorem continuous_finitePadicTensor_mul :
    Continuous (fun z : FinitePadicTensor (p := p) A × FinitePadicTensor (p := p) A =>
      z.1 * z.2) := by
  obtain ⟨J, hJ, E, hfield, halgebra, e, _, he, hinverse⟩ :=
    exists_finiteNormedFieldProduct_piTensor (p := p) A
  letI := hJ
  letI := hfield
  letI := halgebra
  have hproduct := (he.comp continuous_fst).mul (he.comp continuous_snd)
  have h := hinverse.comp hproduct
  change Continuous (fun z : FinitePadicTensor (p := p) A × FinitePadicTensor (p := p) A =>
    e.symm (e z.1 * e z.2)) at h
  simpa only [← map_mul, AlgEquiv.symm_apply_apply] using h

instance finitePadicTensorContinuousMul : ContinuousMul (FinitePadicTensor (p := p) A) :=
  ⟨continuous_finitePadicTensor_mul A⟩

end

end LeanFormal.IUT.LocalFieldPadicTensor
