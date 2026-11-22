/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import tmp.sheaf.xif.paper.Mzk1TraceDualVolumeActual

/-!
# Restricted matrix Haar base (task-109, partial)

Status: PARTIAL.  This file records the actual coordinate lattice and the
GL_d(Z_p) matrix action, and proves the lattice-preservation direction.
The full Haar invariance, diagonal product scaling, and determinant formula
are recorded as exact GAPs in coord/P3-MINIMAL-ACCEPTANCE.md §5b.2.
-/

noncomputable section
open scoped BigOperators Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1MatrixHaarBaseActual

open Matrix MeasureTheory

universe u

variable (p : Nat) [Fact p.Prime]
variable (d : Type) [Fintype d] [DecidableEq d]

/-- The actual integral coordinate lattice in `d → Q_p`. -/
def coordLattice : Set (d → ℚ_[p]) :=
  {x | ∀ i, x i ∈ (1 : Submodule (PadicInt p) ℚ_[p])}

/-- An integral matrix, extended to Q_p. -/
noncomputable def glMatrix (V : Matrix d d (PadicInt p)) :
    Matrix d d ℚ_[p] :=
  Matrix.of fun i j => algebraMap (PadicInt p) ℚ_[p] (V i j)

/-- The matrix action on coordinate vectors. -/
noncomputable def glAct (V : Matrix d d (PadicInt p))
    (x : d → ℚ_[p]) : d → ℚ_[p] :=
  (glMatrix p d V).mulVec x

theorem coordLattice_apply {x : d → ℚ_[p]} :
    x ∈ coordLattice p d ↔ ∀ i, x i ∈ (1 : Submodule (PadicInt p) ℚ_[p]) :=
  Iff.rfl

theorem glAct_mem_coordLattice
    (V : Matrix d d (PadicInt p)) {x : d → ℚ_[p]}
    (hx : x ∈ coordLattice p d) :
    glAct p d V x ∈ coordLattice p d := by
  rw [coordLattice_apply] at hx ⊢
  intro i
  simp only [glAct, glMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply]
  apply Submodule.sum_mem
  intro j _
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (hx j)


theorem glMatrix_mul (V W : Matrix d d (PadicInt p)) :
    glMatrix p d (V * W) = glMatrix p d V * glMatrix p d W := by
  ext i j
  simp [glMatrix, Matrix.mul_apply, map_sum]

theorem glAct_mul (V W : Matrix d d (PadicInt p)) (x : d → ℚ_[p]) :
    glAct p d V (glAct p d W x) = glAct p d (V * W) x := by
  simp only [glAct, glMatrix_mul]
  rw [Matrix.mulVec_mulVec]

theorem glMatrix_one : glMatrix p d (1 : Matrix d d (PadicInt p)) = (1 : Matrix d d ℚ_[p]) := by
  ext i j
  simp [glMatrix, Matrix.of_apply, Matrix.one_apply]

theorem glAct_one (x : d → ℚ_[p]) : glAct p d (1 : Matrix d d (PadicInt p)) x = x := by
  simp [glAct, glMatrix_one, Matrix.one_mulVec]

/-- If `V` has an explicit integral inverse `W`, then `V` maps the integral
coordinate lattice onto itself. -/
theorem glAct_image_eq_of_mul_eq_one
    (V W : Matrix d d (PadicInt p)) (hVW : V * W = 1) :
    glAct p d V '' coordLattice p d = coordLattice p d := by
  apply Set.Subset.antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact glAct_mem_coordLattice p d V hy
  · intro x hx
    refine ⟨glAct p d W x, glAct_mem_coordLattice p d W hx, ?_⟩
    rw [glAct_mul, hVW, glAct_one]


/-- Coordinatewise p^e scaling of a vector. -/
def diagAct (e : d → Nat) (x : d → ℚ_[p]) : d → ℚ_[p] :=
  fun i => (p : ℚ_[p]) ^ (e i) * x i

theorem diagAct_image_coordLattice (e : d → Nat) :
    diagAct p d e '' coordLattice p d =
      {x | ∀ i, ∃ z ∈ (1 : Submodule (PadicInt p) ℚ_[p]),
        (p : ℚ_[p]) ^ (e i) * z = x i} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    intro i
    exact ⟨y i, hy i, rfl⟩
  · intro hx
    refine ⟨fun i => ((p : ℚ_[p]) ^ (e i))⁻¹ * x i, ?_, ?_⟩
    · intro i
      rcases hx i with ⟨z, hz, hz'⟩
      change ((p : ℚ_[p]) ^ (e i))⁻¹ * x i ∈ (1 : Submodule (PadicInt p) ℚ_[p])
      rw [← hz']
      change ((p : ℚ_[p]) ^ (e i))⁻¹ * ((p : ℚ_[p]) ^ (e i) * z) ∈
        (1 : Submodule (PadicInt p) ℚ_[p])
      rw [← mul_assoc, inv_mul_cancel₀, one_mul]
      · exact hz
      · exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero)
    · funext i
      change (p : ℚ_[p]) ^ (e i) * (((p : ℚ_[p]) ^ (e i))⁻¹ * x i) = x i
      rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero)), one_mul]


def glRows : List (String × String) :=
  [ ("coordLattice", "actual Z_p^d"),
    ("glAct_mem_coordLattice", "integral matrix preserves Z_p^d (subset)"),
    ("glAct_image_eq_of_mul_eq_one", "explicit inverse => equality"),
    ("Haar invariance", "GAP"),
    ("diagAct_image_coordLattice", "actual coordinatewise image"),
    ("det formula", "GAP"),
    ("diag product measure scaling", "GAP") ]

theorem glRows_length : glRows.length = 7 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1MatrixHaarBaseActual
