import tmp.sheaf.xif.paper.Mzk1SNFToolActual

/-! GAP-step: extract diag data from Mathlib Smith normal form. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1SNFDiagActual
open Module
open LeanFormal.IUT.XiFPaper.Mzk1SNFToolActual
variable {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
variable {ι : Type*} [Fintype ι]
/-- SNF diagonal data: bases and diagonal entries. -/
theorem snf_diag_data (b : Module.Basis ι R M) (N : Submodule R M) :
    ∃ (n : ℕ) (bM : Module.Basis ι R M) (bN : Module.Basis (Fin n) R N)
      (f : Fin n ↪ ι) (a : Fin n → R),
      ∀ i, (bN i : M) = a i • bM (f i) :=
  exists_smith_normal_form b N
end LeanFormal.IUT.XiFPaper.Mzk1SNFDiagActual
end