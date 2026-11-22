import Mathlib
import tmp.sheaf.xif.paper.S1348D6OrbicurveActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3119WeierstrassFiltrationActual

variable {l : PrimeGeFive}

abbrev P (l : PrimeGeFive) := MvPolynomial (Fin 2) (S1348K l)

noncomputable def wdeg (m : Fin 2 →₀ ℕ) : ℕ := 2 * m 0 + 3 * m 1

noncomputable def weightedDegree (p : P l) : ℕ := p.support.sup wdeg

noncomputable def filt (n : ℕ) : Set (P l) := { p | weightedDegree p ≤ n }

theorem weightedDegree_X0 :
    weightedDegree (MvPolynomial.X (0 : Fin 2) : P l) = 2 := by
  rw [weightedDegree, MvPolynomial.support_X]
  simp [wdeg]

theorem weightedDegree_X1 :
    weightedDegree (MvPolynomial.X (1 : Fin 2) : P l) = 3 := by
  rw [weightedDegree, MvPolynomial.support_X]
  simp [wdeg]

theorem filt_two_le_span :
    (filt (l := l) 2 : Set (P l)) ⊆
      (Submodule.span (S1348K l)
        ({1, MvPolynomial.X (0 : Fin 2)} : Set (P l)) : Set (P l)) := by
  intro p hp
  rw [MvPolynomial.as_sum p]
  apply Submodule.sum_mem
  intro m hm
  have hmle : wdeg m ≤ 2 := by
    have hsup : wdeg m ≤ weightedDegree p := Finset.le_sup (f := wdeg) hm
    exact le_trans hsup hp
  unfold wdeg at hmle
  have hm1 : m 1 = 0 := by
    by_contra h
    have hpos : 0 < m 1 := Nat.pos_of_ne_zero h
    omega
  have hm0 : m 0 ≤ 1 := by omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm0 with h0 | h0
  · have hmzero : m = 0 := by
      ext i; fin_cases i <;> simp [hm1, h0]
    rw [hmzero, MvPolynomial.monomial_zero', MvPolynomial.C_eq_algebraMap]
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (Submodule.smul_mem (Submodule.span (S1348K l)
          ({1, MvPolynomial.X (0 : Fin 2)} : Set (P l)))
        (MvPolynomial.coeff 0 p)
        (Submodule.subset_span (by simp)))
  · have hmsingle : m = Finsupp.single (0 : Fin 2) 1 := by
      ext i; fin_cases i <;> simp [hm1, h0]
    rw [hmsingle, ← MvPolynomial.C_mul_X_eq_monomial, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (by simp))

#check weightedDegree_X0
#check weightedDegree_X1
#check filt_two_le_span
#print axioms filt_two_le_span
end LeanFormal.IUT.XiFPaper.S3119WeierstrassFiltrationActual
end
