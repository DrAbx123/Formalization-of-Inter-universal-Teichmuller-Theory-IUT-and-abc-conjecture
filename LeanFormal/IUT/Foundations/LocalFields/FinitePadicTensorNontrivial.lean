import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology

/-!
# Positive dimension of the genuine finite tensor of nonzero local modules

Each finite source basis has a nonempty index. The actual tensor basis
therefore has a nonempty product index, including for an empty factor
family. Its coordinate equivalence proves that the tensor is nontrivial.
-/

namespace LeanFormal.IUT.LocalFieldPadicTensor

noncomputable section

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Finite ι]
variable (M : ι → Type*) [∀ i, NormedAddCommGroup (M i)]
variable [∀ i, NormedSpace ℚ_[p] (M i)] [∀ i, FiniteDimensional ℚ_[p] (M i)]
variable [∀ i, Nontrivial (M i)]

instance finitePadicTensorNontrivial : Nontrivial (FinitePadicTensor (p := p) M) := by
  classical
  letI := Fintype.ofFinite ι
  let coordinate : FinitePadicTensorIndex (p := p) M :=
    fun _ => ⟨0, Module.finrank_pos⟩
  let e := finitePadicTensorCoordinates (p := p) M
  refine ⟨⟨e.symm 0, e.symm 1, ?_⟩⟩
  intro heq
  have hzeroone : (0 : FinitePadicTensorIndex (p := p) M → ℚ_[p]) = 1 := e.symm.injective heq
  exact zero_ne_one (congrArg (fun x => x coordinate) hzeroone)

theorem finrank_finitePadicTensor_pos :
    0 < Module.finrank ℚ_[p] (FinitePadicTensor (p := p) M) := Module.finrank_pos

end

end LeanFormal.IUT.LocalFieldPadicTensor
