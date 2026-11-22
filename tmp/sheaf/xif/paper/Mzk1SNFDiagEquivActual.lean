import tmp.sheaf.xif.paper.Mzk1SNFToolActual

/-! GAP-step: SNF as span of diagonal generators. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1SNFDiagEquivActual
open Module
variable {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
variable {ι : Type*} [Fintype ι]
theorem snf_eq_span_diag (b : Module.Basis ι R M) (N : Submodule R M) :
    ∃ (n : ℕ) (bM : Module.Basis ι R M) (f : Fin n ↪ ι) (a : Fin n → R),
      N = Submodule.span R (Set.range fun i => a i • bM (f i)) := by
  obtain ⟨n, bM, bN, f, a, hsnf⟩ :=
    LeanFormal.IUT.XiFPaper.Mzk1SNFToolActual.exists_smith_normal_form b N
  refine ⟨n, bM, f, a, ?_⟩
  calc
    N = Submodule.map N.subtype ⊤ := (Submodule.map_subtype_top N).symm
    _ = Submodule.map N.subtype (Submodule.span R (Set.range bN)) := by rw [bN.span_eq]
    _ = Submodule.span R (N.subtype '' Set.range bN) := by rw [Submodule.map_span]
    _ = Submodule.span R (Set.range (fun i => (bN i : M))) := by
          congr 1; rw [Set.range_comp]; rfl
    _ = Submodule.span R (Set.range fun i => a i • bM (f i)) := by
          congr 1; ext x; constructor
          · rintro ⟨i, rfl⟩; exact ⟨i, hsnf i⟩
          · rintro ⟨i, rfl⟩; exact ⟨i, (hsnf i).symm⟩
end LeanFormal.IUT.XiFPaper.Mzk1SNFDiagEquivActual
end