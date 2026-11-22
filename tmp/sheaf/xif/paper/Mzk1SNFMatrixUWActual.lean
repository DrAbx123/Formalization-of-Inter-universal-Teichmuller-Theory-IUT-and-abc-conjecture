import tmp.sheaf.xif.paper.Mzk1SNFMatrixDiagActual
import tmp.sheaf.xif.paper.Mzk1ChangeMatrixActual
import Mathlib.LinearAlgebra.Matrix.Basis

/-! GAP-step: explicit U/W change-of-basis matrices with `U * diag a * W`. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1SNFMatrixUWActual
open Module
open LeanFormal.IUT.XiFPaper.Mzk1SNFMatrixDiagActual
open LeanFormal.IUT.XiFPaper.Mzk1ChangeMatrixActual

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Standard-basis change: `U = b.toMatrix bM` (M side), `W = bN.toMatrix bN0`
(N side), so `U * diag a * W` is the matrix of `N ↪ M` in the standard bases. -/
theorem u_mul_diag_mul_w_standard
    {N : Submodule R M} (bM b : Module.Basis ι R M) (bN bN0 : Module.Basis ι R N)
    (a : ι → R) (hSNF : ∀ i, (bN i : M) = a i • bM i) :
    b.toMatrix bM * Matrix.diagonal a * bN.toMatrix bN0 =
      LinearMap.toMatrix bN0 b N.subtype := by
  rw [← toMatrix_subtype_eq_diagonal bM bN a hSNF]
  exact basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
    (b := bN0) (b' := bN) (c := b) (c' := bM) (f := N.subtype)

/-- The M-side change matrix `U = b.toMatrix bM` has unit determinant. -/
theorem u_det_isUnit {N : Submodule R M} (bM b : Module.Basis ι R M) :
    IsUnit (b.toMatrix bM).det :=
  changeMatrix_det_isUnit b bM

/-- The N-side change matrix `W = bN.toMatrix bN0` has unit determinant. -/
theorem w_det_isUnit {N : Submodule R M} (bN bN0 : Module.Basis ι R N) :
    IsUnit (bN.toMatrix bN0).det :=
  changeMatrix_det_isUnit bN bN0

end LeanFormal.IUT.XiFPaper.Mzk1SNFMatrixUWActual
end 