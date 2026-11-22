import tmp.sheaf.xif.paper.Mzk1GapDetHaarSNFSplitActual
import tmp.sheaf.xif.paper.Mzk1SNFMatrixUWActual
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Tactic
/-! GAP-DET-HAAR matrix-level SNF split facts -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1GapDetHaarMatrixSplitActual
open LeanFormal.IUT.XiFPaper.Mzk1GapDetHaarSNFSplitActual
open LeanFormal.IUT.XiFPaper.Mzk1SNFMatrixUWActual
section Matrix
variable {R : Type*} [CommRing R] {d : Type*} [Fintype d] [DecidableEq d]
/-- Determinant of a U-diag-W split. -/
theorem det_eq_mul_prod_mul_of_split
    (A U W : Matrix d d R) (a : d -> R)
    (h : A = U * Matrix.diagonal a * W) :
    A.det = U.det * (∏ i, a i) * W.det := by
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
/-- Unit determinant from a split with unit U,W determinants. -/
theorem isUnit_det_of_split (A U W : Matrix d d R) (a : d -> R)
    (h : A = U * Matrix.diagonal a * W)
    (ha : ∀ i, IsUnit (a i))
    (hU : IsUnit U.det) (hW : IsUnit W.det) :
    IsUnit A.det := by
  rw [det_eq_mul_prod_mul_of_split A U W a h]
  exact hU.mul (IsUnit.prod_univ_iff.mpr ha) |>.mul hW
/-- Norm of the determinant under a split, in a normed field. -/
theorem norm_det_eq_mul_prod_mul_of_split
    {K : Type*} [NormedField K]
    (A U W : Matrix d d K) (a : d -> K)
    (h : A = U * Matrix.diagonal a * W) :
    ‖A.det‖ = ‖U.det‖ * (∏ i, ‖a i‖) * ‖W.det‖ := by
  rw [det_eq_mul_prod_mul_of_split A U W a h]
  rw [norm_mul, norm_mul, norm_prod]
end Matrix
/-- Actual determinant formula for the SNFMatrixSplit structure. -/
theorem snfMatrixSplit_det {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : Submodule R M} {bM b : Module.Basis ι R M}
    {bN bN0 : Module.Basis ι R N} {a : ι -> R}
    (S : SNFMatrixSplit N bM b bN bN0 a) :
    (LinearMap.toMatrix bN0 b N.subtype).det =
      S.U.det * (∏ i, a i) * S.W.det := by
  rw [← S.equation]
  exact det_eq_mul_prod_mul_of_split (S.U * Matrix.diagonal a * S.W) S.U S.W a rfl
/-- Missing: construct matrix-level SNF data for arbitrary B in GL_d(Q_p). -/
def matrixSNFSplitMissing : List String :=
  [ "build N = image lattice and bases bM,bN from arbitrary B",
    "prove full-rank index equiv for square invertible B" ]
theorem matrixSNFSplitMissing_length : matrixSNFSplitMissing.length = 2 := rfl
#check det_eq_mul_prod_mul_of_split
#check isUnit_det_of_split
#check norm_det_eq_mul_prod_mul_of_split
#check snfMatrixSplit_det
end LeanFormal.IUT.XiFPaper.Mzk1GapDetHaarMatrixSplitActual
end
