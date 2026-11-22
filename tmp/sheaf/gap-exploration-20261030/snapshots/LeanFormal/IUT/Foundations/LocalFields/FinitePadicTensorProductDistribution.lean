import LeanFormal.IUT.Foundations.Algebra.FiniteTensorProductDistribution
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorFieldDecomposition

/-!
# The tuple-preserving decomposition of a finite p-adic tensor packet

The actual distribution equivalence is continuous in both directions for
the proved finite-dimensional tensor topology. Tensor block dimensions
are computed from finite bases, retaining the tuple indexing.
-/

namespace LeanFormal.IUT.LocalFieldPadicTensor

open scoped TensorProduct

noncomputable section

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
variable {κ : ι → Type*} [∀ i, Fintype (κ i)] (M : (i : ι) → κ i → Type*)

section Modules

variable [∀ i j, NormedAddCommGroup (M i j)] [∀ i j, NormedSpace ℚ_[p] (M i j)]
variable [∀ i j, FiniteDimensional ℚ_[p] (M i j)]

open Classical in
def finitePadicTensorProductLinearEquiv :
    FinitePadicTensor (p := p) (fun i => (j : κ i) → M i j) ≃L[ℚ_[p]]
      ((tuple : (i : ι) → κ i) → FinitePadicTensor (p := p) (fun i => M i (tuple i))) := by
  let e : FinitePadicTensor (p := p) (fun i => (j : κ i) → M i j) ≃ₗ[ℚ_[p]]
      ((tuple : (i : ι) → κ i) → FinitePadicTensor (p := p) (fun i => M i (tuple i))) :=
    FiniteTensorProductDistribution.tensorProductLinearEquiv ℚ_[p] M
  exact e.toContinuousLinearEquiv

open Classical in
theorem finitePadicTensorProductLinearEquiv_tprod (x : (i : ι) → (j : κ i) → M i j)
    (tuple : (i : ι) → κ i) :
    finitePadicTensorProductLinearEquiv (p := p) M (finitePadicTensorTprod _ x) tuple =
      finitePadicTensorTprod (p := p) _ (fun i => x i (tuple i)) :=
  FiniteTensorProductDistribution.tensorProductLinearEquiv_tprod ℚ_[p] M x tuple

theorem finrank_finitePadicTensor (A : ι → Type*) [∀ i, NormedAddCommGroup (A i)]
    [∀ i, NormedSpace ℚ_[p] (A i)] [∀ i, FiniteDimensional ℚ_[p] (A i)] :
    Module.finrank ℚ_[p] (FinitePadicTensor (p := p) A) =
      ∏ i, Module.finrank ℚ_[p] (A i) := by
  classical
  change Module.finrank ℚ_[p] (⨂[ℚ_[p]] i, A i) = _
  rw [Module.finrank_eq_card_basis (Basis.piTensorProduct (fun i => Module.finBasis ℚ_[p] (A i))),
    Fintype.card_pi]
  simp only [Fintype.card_fin]

open Classical in
theorem finrank_finitePadicTensorProduct :
    Module.finrank ℚ_[p] (FinitePadicTensor (p := p) (fun i => (j : κ i) → M i j)) =
      ∑ tuple : (i : ι) → κ i, ∏ i, Module.finrank ℚ_[p] (M i (tuple i)) := by
  rw [(finitePadicTensorProductLinearEquiv (p := p) M).toLinearEquiv.finrank_eq,
    Module.finrank_pi_fintype]
  apply Finset.sum_congr rfl
  intro tuple _
  exact finrank_finitePadicTensor _

end Modules

section Algebras

variable [∀ i j, NormedCommRing (M i j)] [∀ i j, NormedAlgebra ℚ_[p] (M i j)]
variable [∀ i j, FiniteDimensional ℚ_[p] (M i j)]

def finitePadicTensorProductAlgEquiv :
    FinitePadicTensor (p := p) (fun i => (j : κ i) → M i j) ≃ₐ[ℚ_[p]]
      ((tuple : (i : ι) → κ i) → FinitePadicTensor (p := p) (fun i => M i (tuple i))) :=
  FiniteTensorProductDistribution.tensorProductAlgEquiv ℚ_[p] M

omit [∀ i j, FiniteDimensional ℚ_[p] (M i j)] in
theorem finitePadicTensorProductAlgEquiv_tprod (x : (i : ι) → (j : κ i) → M i j)
    (tuple : (i : ι) → κ i) :
    finitePadicTensorProductAlgEquiv (p := p) M (finitePadicTensorTprod _ x) tuple =
      finitePadicTensorTprod (p := p) _ (fun i => x i (tuple i)) :=
  FiniteTensorProductDistribution.tensorProductAlgEquiv_tprod ℚ_[p] M x tuple

open Classical in
theorem continuous_finitePadicTensorProductAlgEquiv :
    Continuous (finitePadicTensorProductAlgEquiv (p := p) M) :=
  (finitePadicTensorProductAlgEquiv (p := p) M).toLinearEquiv.toContinuousLinearEquiv.continuous

open Classical in
theorem continuous_finitePadicTensorProductAlgEquiv_symm :
    Continuous (finitePadicTensorProductAlgEquiv (p := p) M).symm :=
  (finitePadicTensorProductAlgEquiv (p := p) M).symm.toLinearEquiv.toContinuousLinearEquiv
    |>.continuous

end Algebras

end

end LeanFormal.IUT.LocalFieldPadicTensor
