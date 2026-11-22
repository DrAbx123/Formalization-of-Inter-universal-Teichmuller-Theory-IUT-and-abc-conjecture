import tmp.sheaf.xif.paper.Mzk1ChangeMatrixRingActual
import tmp.sheaf.xif.paper.Mzk1SNFToolActual

/-! GAP-step: SNF matrix of the inclusion is diagonal; U*M*W=diag. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1SNFMatrixDiagActual
open Module
open LeanFormal.IUT.XiFPaper.Mzk1ChangeMatrixActual
open LeanFormal.IUT.XiFPaper.Mzk1ChangeMatrixRingActual
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {N : Submodule R M} (bM : Module.Basis ι R M) (bN : Module.Basis ι R N)
variable (a : ι → R)
/-- With full-rank SNF data `bN i = a i • bM i`, the matrix of `N ↪ M`
in the bases `bN`, `bM` is diagonal. -/
theorem toMatrix_subtype_eq_diagonal
    (hSNF : ∀ i, (bN i : M) = a i • bM i) :
    LinearMap.toMatrix bN bM (Submodule.subtype N) = Matrix.diagonal a := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  by_cases h : i = j
  · subst h
    simp [hSNF, Matrix.diagonal]
  · simp [hSNF, Matrix.diagonal, h]
/-- Explicit `U*M*W = diag a` with `U = W = 1` (the change matrices from
`bM`,`bN` to themselves); real U/W from another basis pair compose via
`changeMatrix_mul`/`flip`. -/
theorem u_mul_diag_mul_w
    (hSNF : ∀ i, (bN i : M) = a i • bM i) :
    changeMatrix bM bM * LinearMap.toMatrix bN bM (Submodule.subtype N) *
      changeMatrix bN bN = Matrix.diagonal a := by
  rw [changeMatrix_one, toMatrix_subtype_eq_diagonal bM bN a hSNF, changeMatrix_one]
  simp
end LeanFormal.IUT.XiFPaper.Mzk1SNFMatrixDiagActual
end