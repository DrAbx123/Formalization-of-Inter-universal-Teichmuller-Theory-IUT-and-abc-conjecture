import tmp.sheaf.xif.paper.Mzk1SNFToolActual
import tmp.sheaf.xif.paper.Mzk1SNFMatrixUWActual
import tmp.sheaf.xif.paper.Mzk1SNFMatrixDiagActual
/-! GAP-DET-HAAR step 1: SNF decomposition interface -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1GapDetHaarSNFActual
open LeanFormal.IUT.XiFPaper.Mzk1SNFToolActual
open LeanFormal.IUT.XiFPaper.Mzk1SNFMatrixUWActual
open LeanFormal.IUT.XiFPaper.Mzk1SNFMatrixDiagActual
/-- Existing SNF donors for the det-Haar step. -/
def snfDonors : List String :=
  [ "exists_smith_normal_form", "u_mul_diag_mul_w_standard",
    "u_det_isUnit", "w_det_isUnit" ]
theorem snfDonors_length : snfDonors.length = 4 := rfl
/-- Exact remaining step for GL_d(Q_p): integral SNF of an arbitrary invertible matrix. -/
def snfMissing : List String :=
  [ "clear denominators: p^m B integral",
    "SNF U (p^m B) W = diag(a_i)",
    "unit parts a_i = p^{k_i} u_i" ]
theorem snfMissing_length : snfMissing.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1GapDetHaarSNFActual
end
