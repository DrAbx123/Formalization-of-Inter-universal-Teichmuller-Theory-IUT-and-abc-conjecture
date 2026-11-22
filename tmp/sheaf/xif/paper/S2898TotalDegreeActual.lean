import tmp.sheaf.xif.paper.S2801D6FaithfulActual
import tmp.sheaf.xif.paper.S2847A6ArithmeticActual
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open MvPolynomial
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2898TotalDegreeActual

universe u
variable (K : Type u) [Field K]

theorem S2898_polynomial_eq :
    S2801E37Polynomial K =
      (MvPolynomial.X 1 ^ 2 + MvPolynomial.X 1 -
        MvPolynomial.X 0 ^ 3 + MvPolynomial.X 0 : MvPolynomial (Fin 2) K) := by
  rw [S2801E37Polynomial, S2801E37Curve]
  simp [LeanFormal.IUT.IUTII.Frobenioid.Example36.weierstrassAffinePolynomial]
  ring
theorem S2898_totalDegree_le :
    (S2801E37Polynomial K).totalDegree ≤ 3 := by
  rw [S2898_polynomial_eq]
  have hY2 : (MvPolynomial.X 1 ^ 2 : MvPolynomial (Fin 2) K).totalDegree = 2 := by
    rw [MvPolynomial.totalDegree_X_pow]
  have hY : (MvPolynomial.X 1 : MvPolynomial (Fin 2) K).totalDegree = 1 := by
    rw [MvPolynomial.totalDegree_X]
  have hX : (MvPolynomial.X 0 : MvPolynomial (Fin 2) K).totalDegree = 1 := by
    rw [MvPolynomial.totalDegree_X]
  have hX3 : (MvPolynomial.X 0 ^ 3 : MvPolynomial (Fin 2) K).totalDegree = 3 := by
    rw [MvPolynomial.totalDegree_X_pow]
  have hneg : (-(MvPolynomial.X 0 ^ 3) : MvPolynomial (Fin 2) K).totalDegree ≤ 3 := by
    rw [show (-(MvPolynomial.X 0 ^ 3) : MvPolynomial (Fin 2) K) =
      MvPolynomial.C (-1 : K) * MvPolynomial.X 0 ^ 3 by simp]
    calc
      (MvPolynomial.C (-1 : K) * MvPolynomial.X 0 ^ 3 : MvPolynomial (Fin 2) K).totalDegree
          ≤ (MvPolynomial.C (-1 : K) : MvPolynomial (Fin 2) K).totalDegree +
              (MvPolynomial.X 0 ^ 3 : MvPolynomial (Fin 2) K).totalDegree :=
            MvPolynomial.totalDegree_mul _ _
      _ = 3 := by rw [MvPolynomial.totalDegree_C, hX3]
  have hA : (MvPolynomial.X 1 ^ 2 + MvPolynomial.X 1 : MvPolynomial (Fin 2) K).totalDegree ≤ 2 := by
    calc
      (MvPolynomial.X 1 ^ 2 + MvPolynomial.X 1 : MvPolynomial (Fin 2) K).totalDegree
          ≤ max (MvPolynomial.X 1 ^ 2 : MvPolynomial (Fin 2) K).totalDegree
              (MvPolynomial.X 1 : MvPolynomial (Fin 2) K).totalDegree :=
            MvPolynomial.totalDegree_add _ _
      _ = 2 := by rw [hY2, hY]; norm_num
  have hB : ((MvPolynomial.X 1 ^ 2 + MvPolynomial.X 1) -
      MvPolynomial.X 0 ^ 3 : MvPolynomial (Fin 2) K).totalDegree ≤ 3 := by
    rw [sub_eq_add_neg]
    calc
      ((MvPolynomial.X 1 ^ 2 + MvPolynomial.X 1) +
          (-(MvPolynomial.X 0 ^ 3)) : MvPolynomial (Fin 2) K).totalDegree
          ≤ max (MvPolynomial.X 1 ^ 2 + MvPolynomial.X 1 : MvPolynomial (Fin 2) K).totalDegree
              (-(MvPolynomial.X 0 ^ 3) : MvPolynomial (Fin 2) K).totalDegree :=
            MvPolynomial.totalDegree_add _ _
      _ ≤ 3 := by
        exact max_le (le_trans hA (by norm_num)) hneg
  calc
    (MvPolynomial.X 1 ^ 2 + MvPolynomial.X 1 -
        MvPolynomial.X 0 ^ 3 + MvPolynomial.X 0 : MvPolynomial (Fin 2) K).totalDegree
        = (((MvPolynomial.X 1 ^ 2 + MvPolynomial.X 1) -
            MvPolynomial.X 0 ^ 3) + MvPolynomial.X 0 :
              MvPolynomial (Fin 2) K).totalDegree := by ring_nf
    _ ≤ max (((MvPolynomial.X 1 ^ 2 + MvPolynomial.X 1) -
            MvPolynomial.X 0 ^ 3 : MvPolynomial (Fin 2) K).totalDegree)
          (MvPolynomial.X 0 : MvPolynomial (Fin 2) K).totalDegree :=
        MvPolynomial.totalDegree_add _ _
    _ ≤ 3 := by
      rw [hX]
      exact max_le hB (by norm_num)

theorem S2898_coeff :
    MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 3) (S2801E37Polynomial K) = -1 := by
  rw [S2898_polynomial_eq]
  simp [MvPolynomial.coeff_add, MvPolynomial.coeff_sub,
    MvPolynomial.coeff_X_pow, MvPolynomial.coeff_X, Finsupp.single_eq_single_iff]

theorem S2898_totalDegree :
    (S2801E37Polynomial K).totalDegree = 3 := by
  apply le_antisymm (S2898_totalDegree_le K)
  have hmem : Finsupp.single (0 : Fin 2) 3 ∈ (S2801E37Polynomial K).support :=
    MvPolynomial.mem_support_iff.mpr (by rw [S2898_coeff]; norm_num)
  have hle := MvPolynomial.le_totalDegree (p := S2801E37Polynomial K) hmem
  simpa using hle

#check S2898_totalDegree
#print axioms S2898_totalDegree

end LeanFormal.IUT.XiFPaper.S2898TotalDegreeActual
end
