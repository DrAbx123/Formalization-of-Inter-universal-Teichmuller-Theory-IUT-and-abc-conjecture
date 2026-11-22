import Mathlib
import tmp.sheaf.xif.paper.S3075PhiFixesKActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open CategoryTheory AlgebraicGeometry
open scoped AlgebraMonoidAlgebra
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3077WeierstrassFiltrationActual

abbrev K := S2844D6F6BaseChangeActual.K
abbrev P := MvPolynomial (Fin 2) K

local instance : Field K := S2847A6.fieldF
local instance : NumberField K := S2847A6.numberFieldF
local instance : DecidableEq K := Classical.decEq _

noncomputable def wdeg (m : Fin 2 →₀ ℕ) : ℕ := 2 * m 0 + 3 * m 1

noncomputable def weightedDegree (p : P) : ℕ := p.support.sup wdeg

noncomputable def filt (n : ℕ) : Set P := { p | weightedDegree p ≤ n }

theorem weightedDegree_X0 : weightedDegree (MvPolynomial.X (0 : Fin 2) : P) = 2 := by
  rw [weightedDegree, MvPolynomial.support_X]
  simp [wdeg]

theorem weightedDegree_X1 : weightedDegree (MvPolynomial.X (1 : Fin 2) : P) = 3 := by
  rw [weightedDegree, MvPolynomial.support_X]
  simp [wdeg]

/-- Degree-two part of the filtration lies in span{1, X0}. -/
theorem filt_two_le_span :
    (filt 2 : Set P) ⊆
      (Submodule.span K ({1, MvPolynomial.X (0 : Fin 2)} : Set P) : Set P) := by
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
  have hm0 : m 0 ≤ 1 := by
    omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm0 with h0 | h0
  · have hmzero : m = 0 := by
      ext i
      fin_cases i <;> simp [hm1, h0]
    rw [hmzero, MvPolynomial.monomial_zero']
    rw [MvPolynomial.C_eq_algebraMap, ← Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · have hmsingle : m = Finsupp.single (0 : Fin 2) 1 := by
      ext i
      fin_cases i <;> simp [hm1, h0]
    rw [hmsingle, ← MvPolynomial.C_mul_X_eq_monomial, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

noncomputable def filtR (n : ℕ) : Set (S2801E37CoordinateRing K) :=
  Ideal.Quotient.mk (S2801E37Ideal K) '' filt n

theorem x_mem_filtR_two : S2801E37X K ∈ filtR 2 := by
  refine ⟨MvPolynomial.X (0 : Fin 2), ?_, rfl⟩
  change weightedDegree (MvPolynomial.X (0 : Fin 2) : P) ≤ 2
  rw [weightedDegree_X0]

/-- Quotient image of the degree-two filtration lies in span{1, X}. -/
theorem filtR_two_le_span :
    filtR 2 ⊆
      (Submodule.span K ({1, S2801E37X K} :
        Set (S2801E37CoordinateRing K)) : Set (S2801E37CoordinateRing K)) := by
  intro y hy
  rcases hy with ⟨p, hp, rfl⟩
  have hp' : p ∈ Submodule.span K ({1, MvPolynomial.X (0 : Fin 2)} : Set P) :=
    filt_two_le_span hp
  rcases (Submodule.mem_span_pair.mp hp') with ⟨a, c, h⟩
  let q : P →ₐ[K] S2801E37CoordinateRing K :=
    Ideal.Quotient.mkₐ K (S2801E37Ideal K)
  have hqp : q p = a • (1 : S2801E37CoordinateRing K) + c • S2801E37X K := by
    rw [← h]
    simp [q, map_add, map_smul, S2801E37X]
  change Ideal.Quotient.mk (S2801E37Ideal K) p ∈
    Submodule.span K ({1, S2801E37X K} : Set (S2801E37CoordinateRing K))
  rw [show Ideal.Quotient.mk (S2801E37Ideal K) p = q p from rfl, hqp]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

#check filt_two_le_span
#check filtR_two_le_span
#print axioms filt_two_le_span
#print axioms filtR_two_le_span
#print axioms x_mem_filtR_two

end LeanFormal.IUT.XiFPaper.S3077WeierstrassFiltrationActual
end
