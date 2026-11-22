import tmp.sheaf.n8.closure.EtaBasisChangeAssembled

/-!
# Eta basis-change final

Actual matrix/basis theorem: if bN i = a_i bM i and
f (bM i) = sum_j D_{j i} bN j, then

  toMatrix bM bM f = diagonal(a) * D.

This is proved by LinearMap.toMatrix_apply, map_sum, Finsupp.single_apply, and
Finset.sum_ite_eq.  Combining with the actual determinant unit of the change
matrix D gives det f = unit * prod a_i and ||det f|| = ||prod a_i||.

The remaining exact gap is the lattice-to-Q_p basis realization: constructing
bM, bN, a, and integral D from submodule SNF bases of L and fL : L ≃ N.  No
arbitrary matrix is introduced.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option linter.overlappingInstances false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Module Matrix
open scoped BigOperators
open LeanFormal.IUT.N8Closure.EtaBasisChangeAssembled
open LeanFormal.IUT.N8Closure.EtaBasisChangeDetIndexActual

namespace LeanFormal.IUT.N8Closure.EtaBasisChangeFinal

variable {p : Nat} [Fact p.Prime]
variable {E : Type*} [AddCommGroup E] [Module ℚ_[p] E]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Actual matrix identity: diagonal SNF relation plus D coordinate relation
gives the matrix of f as diagonal(a) * D. -/
theorem toMatrix_eq_diagonal_mul
    (f : E →ₗ[ℚ_[p]] E) (bM bN : Basis n ℚ_[p] E)
    (a : n → ℚ_[p]) (D : Matrix n n ℚ_[p])
    (hB : ∀ i, bN i = a i • bM i)
    (hD : ∀ i, f (bM i) = ∑ j, D j i • bN j) :
    LinearMap.toMatrix bM bM f = Matrix.diagonal a * D := by
  have hrepr : ∀ x, bM.repr (bN x) = Finsupp.single x (a x) := by
    intro x
    rw [hB x, map_smul, Basis.repr_self]
    simp
  ext j i
  rw [LinearMap.toMatrix_apply, hD i, map_sum]
  rw [Finsupp.finsetSum_apply]
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, hrepr,
    Matrix.mul_apply, Matrix.diagonal_apply]
  simp only [Finsupp.single_apply, mul_ite, ite_mul, mul_zero, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ j (fun x => D x i * a x),
    Finset.sum_ite_eq Finset.univ j (fun x => a j * D x i)]
  simp [mul_comm]

/-- Actual basis-change determinant/norm from the explicit matrix identity. -/
theorem det_norm_from_basis_change
    (f : E →ₗ[ℚ_[p]] E) (bM bN : Basis n ℚ_[p] E)
    (a : n → ℤ_[p]) (D : Matrix n n ℤ_[p])
    (hB : ∀ i, bN i = (a i : ℚ_[p]) • bM i)
    (hDcoord : ∀ i, f (bM i) = ∑ j, (D j i : ℚ_[p]) • bN j)
    (hD : IsUnit D.det) :
    (∃ u : ℤ_[p]ˣ,
        LinearMap.det f = (u : ℚ_[p]) * ((∏ i, a i : ℤ_[p]) : ℚ_[p])) ∧
      ‖LinearMap.det f‖ = ‖(((∏ i, a i : ℤ_[p])) : ℚ_[p])‖ := by
  have hmat : LinearMap.toMatrix bM bM f =
      Matrix.diagonal (fun i => (a i : ℚ_[p])) *
        D.map (algebraMap ℤ_[p] ℚ_[p]) := by
    simpa [Matrix.map_apply] using
      toMatrix_eq_diagonal_mul f bM bN (fun i => (a i : ℚ_[p]))
        (D.map (algebraMap ℤ_[p] ℚ_[p]))
        hB hDcoord
  refine ⟨det_eq_unit_mul_prod_of_matrix_eq f bM a D hmat hD, ?_⟩
  exact norm_det_eq_prod_norm_of_matrix_eq f bM a D hmat hD

/-- Exact final gap: lattice-to-Q_p basis realization of the assembled data. -/
def MissingLatticeToQpBasisRealization : Prop :=
  ∀ (f : E →ₗ[ℚ_[p]] E), LinearMap.det f ≠ 0 →
    Nonempty (BasisChangeAssembledData (p := p) (n := n) f)

end LeanFormal.IUT.N8Closure.EtaBasisChangeFinal
