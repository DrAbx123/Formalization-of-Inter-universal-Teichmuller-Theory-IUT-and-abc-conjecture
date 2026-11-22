/- U-R fallback J2 (route §5.3): determinant/covolume algebra for lattice
transport.  This file records the actual matrix determinant identities used to
compare covolumes after a basis change; the source/packet matrix instantiation
is a separate deliverable. -/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1URJ2Actual

variable {n : Nat} {K : Type*} [Field K]

/-- Covolume factor of an actual basis matrix. -/
def detCovolume (A : Matrix (Fin n) (Fin n) K) : K := A.det

theorem detCovolume_basis_change (A P : Matrix (Fin n) (Fin n) K) :
    detCovolume (P * A) = P.det * detCovolume A := by
  simp [detCovolume, Matrix.det_mul]

theorem detCovolume_smul (c : K) (A : Matrix (Fin n) (Fin n) K) :
    detCovolume (c • A) = c ^ n * detCovolume A := by
  simp [detCovolume, Matrix.det_smul]

theorem detCovolume_one :
    detCovolume (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  simp [detCovolume]

#print axioms detCovolume_basis_change
#print axioms detCovolume_smul
end LeanFormal.IUT.XiFPaper.Mzk1URJ2Actual
end
