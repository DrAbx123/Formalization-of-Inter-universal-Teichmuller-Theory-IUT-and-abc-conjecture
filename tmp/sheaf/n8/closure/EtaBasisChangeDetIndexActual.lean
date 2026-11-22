import Mathlib
import tmp.sheaf.n8.closure.EtaPAdicSNFDetComparison

/-!
# Eta basis-change determinant/index actual

Actual algebra: if in a Q_p-basis the matrix of f is

  toMatrix bM bM f = diagonal(a) * D

with D an integral matrix whose determinant is a unit, then

  det f = unit * prod_i a_i,

and the norm of det f equals the norm of prod_i a_i.  This is the exact
determinant step of the basis-change route.

The missing basis-change theorem is the production construction of such bM,
bN, a, D from an arbitrary Q_p-linear f and lattice f(L) (including
det D a unit).  No arbitrary unit or matrix is introduced.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.checkUnivs false
set_option linter.deprecated false

open Module Matrix
open scoped BigOperators

namespace LeanFormal.IUT.N8Closure.EtaBasisChangeDetIndexActual

variable {p : Nat} [Fact p.Prime]
variable {E : Type*} [AddCommGroup E] [Module ℚ_[p] E]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Actual determinant computation from a diagonal-times-integral matrix
relation, with integral determinant a unit. -/
theorem det_eq_unit_mul_prod_of_matrix_eq
    (f : E →ₗ[ℚ_[p]] E) (bM : Basis n ℚ_[p] E)
    (a : n → ℤ_[p]) (D : Matrix n n ℤ_[p])
    (hmat : LinearMap.toMatrix bM bM f =
      Matrix.diagonal (fun i => (a i : ℚ_[p])) *
        D.map (algebraMap ℤ_[p] ℚ_[p]))
    (hD : IsUnit D.det) :
    ∃ u : ℤ_[p]ˣ,
      LinearMap.det f = (u : ℚ_[p]) * ((∏ i, a i : ℤ_[p]) : ℚ_[p]) := by
  let uU := hD.unit
  refine ⟨uU, ?_⟩
  rw [← LinearMap.det_toMatrix bM f, hmat, Matrix.det_mul, Matrix.det_diagonal]
  have hDmap : (D.map (algebraMap ℤ_[p] ℚ_[p])).det =
      ((D.det : ℤ_[p]) : ℚ_[p]) := by
    change ((algebraMap ℤ_[p] ℚ_[p]).mapMatrix D).det = _
    rw [← RingHom.map_det (algebraMap ℤ_[p] ℚ_[p]) D]
    rfl
  rw [hDmap]
  have hDval : (uU : ℤ_[p]) = D.det := IsUnit.unit_spec hD
  rw [← hDval]
  rw [mul_comm]
  congr 1
  exact (map_prod (algebraMap ℤ_[p] ℚ_[p]) a Finset.univ).symm

/-- Actual norm comparison from the same matrix relation. -/
theorem norm_det_eq_prod_norm_of_matrix_eq
    (f : E →ₗ[ℚ_[p]] E) (bM : Basis n ℚ_[p] E)
    (a : n → ℤ_[p]) (D : Matrix n n ℤ_[p])
    (hmat : LinearMap.toMatrix bM bM f =
      Matrix.diagonal (fun i => (a i : ℚ_[p])) *
        D.map (algebraMap ℤ_[p] ℚ_[p]))
    (hD : IsUnit D.det) :
    ‖LinearMap.det f‖ = ‖(((∏ i, a i : ℤ_[p])) : ℚ_[p])‖ := by
  obtain ⟨u, hu⟩ := det_eq_unit_mul_prod_of_matrix_eq f bM a D hmat hD
  rw [hu, norm_mul, PadicInt.padic_norm_e_of_padicInt, PadicInt.norm_units, one_mul]

/-- Exact missing basis-change theorem: construct the diagonal-times-integral
matrix relation for an arbitrary f from SNF bases of L and f(L), with the
change matrix determinant a unit. -/
def MissingBasisChangeDiagonalization : Prop :=
  ∀ (f : E →ₗ[ℚ_[p]] E), LinearMap.det f ≠ 0 →
    ∃ (bM : Basis n ℚ_[p] E) (a : n → ℤ_[p]) (D : Matrix n n ℤ_[p]),
      LinearMap.toMatrix bM bM f =
        Matrix.diagonal (fun i => (a i : ℚ_[p])) *
          D.map (algebraMap ℤ_[p] ℚ_[p]) ∧
        IsUnit D.det

end LeanFormal.IUT.N8Closure.EtaBasisChangeDetIndexActual
