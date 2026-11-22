import tmp.sheaf.n8.closure.EtaBasisChangeDetIndexActual

/-!
# Eta basis-change diagonalization: exact gap

The actual determinant algebra is in EtaBasisChangeDetIndexActual:
if a Q_p-basis matrix satisfies

  toMatrix bM bM f = diagonal(a) * D

with D integral and det D a unit, then det f = unit * prod_i a_i and
||det f|| = ||prod a_i||.

This file records the exact missing construction of such data from submodule
Smith normal form: bM of L, bN of N = f(L), (bN i) = a_i bM i, and D the change
matrix of f(bM) against bN with det D a unit.  Mathlib supplies the submodule
SNF bM/bN/a but not the assembled basis-change diagonalization of the matrix of
f, nor the invariance f(L)=N inside a chosen ambient lattice.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option linter.overlappingInstances false
set_option linter.unusedVariables false
set_option linter.deprecated false

open Module Matrix
open scoped BigOperators
open LeanFormal.IUT.N8Closure.EtaBasisChangeDetIndexActual

namespace LeanFormal.IUT.N8Closure.EtaBasisChangeDiagonalizationActual

variable {p : Nat} [Fact p.Prime]
variable {E : Type*} [AddCommGroup E] [Module ℚ_[p] E]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Exact basis-change diagonalization data for f. -/
structure BasisChangeDiagonalizationData (f : E →ₗ[ℚ_[p]] E) where
  bM : Basis n ℚ_[p] E
  a : n → ℤ_[p]
  D : Matrix n n ℤ_[p]
  hmat : LinearMap.toMatrix bM bM f =
    Matrix.diagonal (fun i => (a i : ℚ_[p])) *
      D.map (algebraMap ℤ_[p] ℚ_[p])
  hD : IsUnit D.det

/-- Actual determinant and norm from a supplied basis-change diagonalization. -/
theorem det_norm_of_data {f : E →ₗ[ℚ_[p]] E}
    (data : BasisChangeDiagonalizationData (p := p) (n := n) f) :
    (∃ u : ℤ_[p]ˣ,
        LinearMap.det f = (u : ℚ_[p]) * ((∏ i, data.a i : ℤ_[p]) : ℚ_[p])) ∧
      ‖LinearMap.det f‖ = ‖(((∏ i, data.a i : ℤ_[p])) : ℚ_[p])‖ := by
  refine ⟨det_eq_unit_mul_prod_of_matrix_eq f data.bM data.a data.D data.hmat data.hD, ?_⟩
  exact norm_det_eq_prod_norm_of_matrix_eq f data.bM data.a data.D data.hmat data.hD

/-- Exact missing construction: produce BasisChangeDiagonalizationData from
submodule SNF bases of L and f(L), including the unit determinant of the change
matrix D. -/
def MissingBasisChangeDiagonalizationConstruction : Prop :=
  ∀ (f : E →ₗ[ℚ_[p]] E), LinearMap.det f ≠ 0 →
    Nonempty (BasisChangeDiagonalizationData (p := p) (n := n) f)

end LeanFormal.IUT.N8Closure.EtaBasisChangeDiagonalizationActual
