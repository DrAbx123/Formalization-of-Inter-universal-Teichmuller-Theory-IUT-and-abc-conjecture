import Mathlib

/-!
# Eta basis-change data construction

Actual part: for an equivalence fL : L ≃ N of free Z_p-modules and bases
bM of L, bN of N, the change matrix

  D := toMatrix bM bN fL

is integral by construction, and its determinant is a unit: the inverse change
matrix is toMatrix bN bM fL.symm, and toMatrix_comp gives
  (inverse matrix) * D = 1,
so D is a unit matrix and det D is a unit.

The missing part is constructing fL, bM, bN, and the SNF diagonal relation from
an arbitrary Q_p-linear f and an ambient lattice; Mathlib has the submodule SNF
but not the assembled lattice/basis-change data.  No arbitrary matrix or unit
is introduced.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option linter.overlappingInstances false
set_option linter.unusedVariables false

open Module Matrix
open scoped BigOperators

namespace LeanFormal.IUT.N8Closure.EtaBasisChangeDataConstruction

variable {p : Nat} [Fact p.Prime]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {L N : Type*} [AddCommGroup L] [Module ℤ_[p] L]
  [AddCommGroup N] [Module ℤ_[p] N]

/-- Actual integral change matrix between bN and fL(bM). -/
def changeMatrix (bM : Basis n ℤ_[p] L) (bN : Basis n ℤ_[p] N)
    (fL : L ≃ₗ[ℤ_[p]] N) : Matrix n n ℤ_[p] :=
  LinearMap.toMatrix bM bN fL.toLinearMap

/-- Actual inverse integral change matrix. -/
def inverseChangeMatrix (bM : Basis n ℤ_[p] L) (bN : Basis n ℤ_[p] N)
    (fL : L ≃ₗ[ℤ_[p]] N) : Matrix n n ℤ_[p] :=
  LinearMap.toMatrix bN bM fL.symm.toLinearMap

/-- Actual unit determinant of the change matrix. -/
theorem changeMatrix_det_isUnit (bM : Basis n ℤ_[p] L) (bN : Basis n ℤ_[p] N)
    (fL : L ≃ₗ[ℤ_[p]] N) :
    IsUnit (changeMatrix bM bN fL).det := by
  let D := changeMatrix bM bN fL
  let Dinv := inverseChangeMatrix bM bN fL
  have hcomp := LinearMap.toMatrix_comp bM bN bM fL.symm.toLinearMap fL.toLinearMap
  have hcomp' : Dinv * D = 1 := by
    simpa [D, Dinv, changeMatrix, inverseChangeMatrix,
      LinearEquiv.symm_comp, LinearMap.toMatrix_one] using hcomp.symm
  have hunit : IsUnit D := isUnit_iff_exists_inv'.mpr ⟨Dinv, hcomp'⟩
  exact (Matrix.isUnit_iff_isUnit_det D).mp hunit

end LeanFormal.IUT.N8Closure.EtaBasisChangeDataConstruction
