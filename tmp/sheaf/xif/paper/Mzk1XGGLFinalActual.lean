import tmp.sheaf.xif.paper.Mzk1SNFToolActual

/-! CONDITIONAL: SNF diagonal data surface for general X_G. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1XGGLFinalActual
open Module

variable {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
variable {ι : Type*} [Fintype ι]

/-- SNF diagonal data for a full-rank submodule `N ≤ M`. -/
theorem xg_snf_data (b : Module.Basis ι R M) (N : Submodule R M) :
    ∃ (n : ℕ) (bM : Module.Basis ι R M) (bN : Module.Basis (Fin n) R N)
      (f : Fin n ↪ ι) (a : Fin n → R),
      ∀ i, (bN i : M) = a i • bM (f i) :=
  LeanFormal.IUT.XiFPaper.Mzk1SNFToolActual.exists_smith_normal_form b N

end LeanFormal.IUT.XiFPaper.Mzk1XGGLFinalActual
end