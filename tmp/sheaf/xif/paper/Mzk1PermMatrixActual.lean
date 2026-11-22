import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers

/-! GAP-step: permutation matrix action preserves the integral coordinate lattice. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1PermMatrixActual
variable {p : Nat} [Fact p.Prime] {d : Type*} [Fintype d] [DecidableEq d]
def permMatrix (σ : Equiv.Perm d) : Matrix d d (PadicInt p) :=
  fun i j => if σ i = j then 1 else 0
def coordSet : Set (d → ℚ_[p]) :=
  {x | ∀ i, ∃ z : PadicInt p, x i = algebraMap (PadicInt p) ℚ_[p] z}
theorem permMatrix_apply (σ : Equiv.Perm d) (i : d) :
    permMatrix (p := p) σ i = Pi.single (σ i) (1 : PadicInt p) := by
  funext j
  by_cases h : σ i = j
  · subst j; simp [permMatrix, Pi.single_eq_same]
  · simp [permMatrix, h, Pi.single_eq_of_ne]
theorem permMatrix_mulVec (σ : Equiv.Perm d) (x : d → ℚ_[p]) :
    (fun i => ∑ j, algebraMap (PadicInt p) ℚ_[p] (permMatrix (p := p) σ i j) * x j) =
      fun i => x (σ i) := by
  funext i
  rw [permMatrix_apply]
  simp [Pi.single_apply]
theorem permMatrix_coordSet_mem (σ : Equiv.Perm d) {x : d → ℚ_[p]} (hx : x ∈ coordSet (p := p)) :
    (fun i => ∑ j, algebraMap (PadicInt p) ℚ_[p] (permMatrix (p := p) σ i j) * x j) ∈
      coordSet (p := p) := by
  intro i
  rw [permMatrix_mulVec]
  exact hx (σ i)
end LeanFormal.IUT.XiFPaper.Mzk1PermMatrixActual
end