import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorLogShellHull
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldProductHullTransport

/-!
# Compatibility of the actual logarithmic hull with decomposition choices

The change from one field-product decomposition to another is the
actual composite algebra equivalence. Finite-dimensional continuity
and the proved hull transport identify the two resulting hulls.
-/

namespace LeanFormal.IUT.LocalFieldPadicTensor

open LeanFormal.IUT.LocalFieldProductHull

noncomputable section

variable {p : ℕ} [Fact p.Prime] {ι : Type}
variable (A : ι → Type) [∀ i, NormedField (A i)] [∀ i, NormedAlgebra ℚ_[p] (A i)]
variable [∀ i, CharZero (A i)] [∀ i, IsUltrametricDist (A i)]
variable [∀ i, CompleteSpace (A i)] [∀ i, ProperSpace (A i)]
variable {J L : Type} {E : J → Type} {F : L → Type}
variable [∀ j, NormedField (E j)] [∀ l, NormedField (F l)]
variable [∀ j, NormedAlgebra ℚ_[p] (E j)] [∀ l, NormedAlgebra ℚ_[p] (F l)]

theorem tensorLogShellProductImage_decomposition_change
    (first : FinitePadicTensor (p := p) A ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (second : FinitePadicTensor (p := p) A ≃ₐ[ℚ_[p]] ((l : L) → F l)) :
    (first.symm.trans second) '' tensorLogShellProductImage A first =
      tensorLogShellProductImage A second := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    change second x = second (first.symm (first x))
    rw [AlgEquiv.symm_apply_apply]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨first x, ⟨x, hx, rfl⟩, ?_⟩
    change second (first.symm (first x)) = second x
    rw [AlgEquiv.symm_apply_apply]

variable [Finite J] [Finite L] [∀ j, FiniteDimensional ℚ_[p] (E j)]
variable [∀ l, FiniteDimensional ℚ_[p] (F l)]
variable [∀ j, ProperSpace (E j)] [∀ l, ProperSpace (F l)]

theorem tensorLogShellHull_decomposition_change
    (first : FinitePadicTensor (p := p) A ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (second : FinitePadicTensor (p := p) A ≃ₐ[ℚ_[p]] ((l : L) → F l)) :
    (first.symm.trans second) '' hull (tensorLogShellProductImage A first) =
      hull (tensorLogShellProductImage A second) := by
  letI := Fintype.ofFinite J
  letI := Fintype.ofFinite L
  let changeOfDecomposition := first.symm.trans second
  have hforward : Continuous changeOfDecomposition :=
    changeOfDecomposition.toLinearMap.continuous_of_finiteDimensional
  have hbackward : Continuous changeOfDecomposition.symm :=
    changeOfDecomposition.symm.toLinearMap.continuous_of_finiteDimensional
  have htransport := continuous_ringEquiv_image_hull changeOfDecomposition.toRingEquiv
    hforward hbackward (tensorLogShellProductImage A first)
  change changeOfDecomposition.toRingEquiv '' hull (tensorLogShellProductImage A first) = _
  rw [htransport]
  change hull ((first.symm.trans second) '' tensorLogShellProductImage A first) = _
  rw [tensorLogShellProductImage_decomposition_change]

end

end LeanFormal.IUT.LocalFieldPadicTensor
