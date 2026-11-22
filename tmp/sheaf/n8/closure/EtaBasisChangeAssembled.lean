import tmp.sheaf.n8.closure.EtaBasisChangeDataConstruction
import tmp.sheaf.n8.closure.EtaBasisChangeDetIndexActual

/-!
# Eta basis-change assembled: exact assembly gap

The actual change-matrix determinant-unit theorem is in
EtaBasisChangeDataConstruction: for fL : L ≃ N, the change matrix
D = toMatrix bM bN fL is integral and det D is a unit.

The actual determinant algebra is in EtaBasisChangeDetIndexActual: if
toMatrix bM bM f = diagonal(a) * D.map with det D a unit, then
det f = unit * prod a and ||det f|| = ||prod a||.

This file records the exact missing assembly: the identification of f with a
Q_p-basis matrix satisfying that diagonal-times-D relation from submodule SNF
bases of L and N=fL.  No arbitrary matrix is introduced.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option linter.overlappingInstances false
set_option linter.unusedVariables false

open Module Matrix
open scoped BigOperators
open LeanFormal.IUT.N8Closure.EtaBasisChangeDetIndexActual

namespace LeanFormal.IUT.N8Closure.EtaBasisChangeAssembled

variable {p : Nat} [Fact p.Prime]
variable {E : Type*} [AddCommGroup E] [Module ℚ_[p] E]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Exact assembled basis-change diagonalization data. -/
structure BasisChangeAssembledData (f : E →ₗ[ℚ_[p]] E) where
  bM : Basis n ℚ_[p] E
  bN : Basis n ℚ_[p] E
  a : n → ℤ_[p]
  D : Matrix n n ℤ_[p]
  hSNF : ∀ i, bN i = (a i : ℚ_[p]) • bM i
  hD : IsUnit D.det
  hmat : LinearMap.toMatrix bM bM f =
    Matrix.diagonal (fun i => (a i : ℚ_[p])) *
      D.map (algebraMap ℤ_[p] ℚ_[p])

/-- Actual determinant and norm from assembled data. -/
theorem det_norm_from_assembled {f : E →ₗ[ℚ_[p]] E}
    (data : BasisChangeAssembledData (p := p) (n := n) f) :
    (∃ u : ℤ_[p]ˣ,
        LinearMap.det f = (u : ℚ_[p]) * ((∏ i, data.a i : ℤ_[p]) : ℚ_[p])) ∧
      ‖LinearMap.det f‖ = ‖(((∏ i, data.a i : ℤ_[p])) : ℚ_[p])‖ := by
  refine ⟨det_eq_unit_mul_prod_of_matrix_eq f data.bM data.a data.D data.hmat data.hD, ?_⟩
  exact norm_det_eq_prod_norm_of_matrix_eq f data.bM data.a data.D data.hmat data.hD

/-- Exact missing assembly theorem: construct assembled data from submodule SNF
bases and fL : L ≃ N, including the diagonal-times-D matrix identity for f. -/
def MissingAssembledBasisChangeData : Prop :=
  ∀ (f : E →ₗ[ℚ_[p]] E), LinearMap.det f ≠ 0 →
    Nonempty (BasisChangeAssembledData (p := p) (n := n) f)

end LeanFormal.IUT.N8Closure.EtaBasisChangeAssembled
