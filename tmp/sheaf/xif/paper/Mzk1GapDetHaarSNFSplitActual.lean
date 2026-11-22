import tmp.sheaf.xif.paper.Mzk1SNFToolActual
import tmp.sheaf.xif.paper.Mzk1SNFMatrixUWActual
import tmp.sheaf.xif.paper.Mzk1SNFMatrixDiagActual
/-! GAP-DET-HAAR SNF split: actual U * diag(a) * W construction from SNF basis data -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1GapDetHaarSNFSplitActual
open Module
open LeanFormal.IUT.XiFPaper.Mzk1SNFToolActual
open LeanFormal.IUT.XiFPaper.Mzk1SNFMatrixUWActual
open LeanFormal.IUT.XiFPaper.Mzk1SNFMatrixDiagActual
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Actual SNF matrix split data. -/
structure SNFMatrixSplit (N : Submodule R M) (bM b : Module.Basis ι R M)
    (bN bN0 : Module.Basis ι R N) (a : ι -> R) where
  U : Matrix ι ι R
  W : Matrix ι ι R
  U_eq : U = b.toMatrix bM
  W_eq : W = bN.toMatrix bN0
  equation : U * Matrix.diagonal a * W = LinearMap.toMatrix bN0 b N.subtype
  detU_unit : IsUnit U.det
  detW_unit : IsUnit W.det
/-- Actual split from SNF basis data. -/
noncomputable def snfMatrixSplit (N : Submodule R M) (bM b : Module.Basis ι R M)
    (bN bN0 : Module.Basis ι R N) (a : ι -> R)
    (hSNF : forall i, (bN i : M) = a i • bM i) :
    SNFMatrixSplit N bM b bN bN0 a where
  U := b.toMatrix bM
  W := bN.toMatrix bN0
  U_eq := rfl
  W_eq := rfl
  equation := u_mul_diag_mul_w_standard bM b bN bN0 a hSNF
  detU_unit := u_det_isUnit (N := N) bM b
  detW_unit := w_det_isUnit bN bN0
/-- Existence of the split from SNF basis data. -/
theorem exists_snfMatrixSplit (N : Submodule R M) (bM b : Module.Basis ι R M)
    (bN bN0 : Module.Basis ι R N) (a : ι -> R)
    (hSNF : forall i, (bN i : M) = a i • bM i) :
    Nonempty (SNFMatrixSplit N bM b bN bN0 a) :=
  ⟨snfMatrixSplit N bM b bN bN0 a hSNF⟩
/-- Missing: produce the SNF basis data from an arbitrary GL_d(Q_p) element. -/
def snfSplitMissing : List String :=
  [ "construct N, bM, b, bN, bN0, a from B in GL_d(Q_p)",
    "full-rank index equiv (n = d) for square B" ]
theorem snfSplitMissing_length : snfSplitMissing.length = 2 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1GapDetHaarSNFSplitActual
end
