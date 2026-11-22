import tmp.sheaf.xif.paper.S2736hTensorCharPKFinalActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.S2736iTensorFinrankActual

open LeanFormal.IUT.PadicIntegerProductLattice
open LeanFormal.IUT.LocalFieldPadicTensor

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
variable (M : ι → Type*) [∀ i, NormedAddCommGroup (M i)]
variable [∀ i, NormedSpace ℚ_[p] (M i)]
variable [∀ i, FiniteDimensional ℚ_[p] (M i)]

theorem finrank_tensor :
    Module.finrank ℚ_[p] (FinitePadicTensor (p := p) M) =
      Fintype.card (FinitePadicTensorIndex (p := p) M) := by
  rw [(finitePadicTensorCoordinates (p := p) M).finrank_eq]
  exact Module.finrank_fintype_fun_eq_card ℚ_[p]

#check finrank_tensor
end LeanFormal.IUT.XiFPaper.S2736iTensorFinrankActual
end
