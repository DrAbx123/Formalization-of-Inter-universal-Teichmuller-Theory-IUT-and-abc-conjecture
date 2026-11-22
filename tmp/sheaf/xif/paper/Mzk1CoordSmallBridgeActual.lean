/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1DiagEmbeddingEquivActual
import tmp.sheaf.xif.paper.Mzk1MatrixHaarBaseActual

/-! # coordSmall = coordLattice (task-109, first diagonal bridge) -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1CoordSmallBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1DiagEmbeddingEquivActual
open LeanFormal.IUT.XiFPaper.Mzk1MatrixHaarBaseActual
variable {p : Nat} [Fact p.Prime] {d : Type} [Fintype d] [DecidableEq d]

theorem span_one_eq_one :
    Submodule.span (PadicInt p) ({(1 : ℚ_[p])} : Set ℚ_[p]) = 1 := by
  ext x
  constructor
  · intro hx
    rw [Submodule.mem_span_singleton] at hx
    rcases hx with ⟨a, rfl⟩
    rw [Submodule.mem_one]
    exact ⟨a, by rw [Algebra.smul_def, mul_one]⟩
  · intro hx
    rw [Submodule.mem_one] at hx
    rcases hx with ⟨a, rfl⟩
    rw [Submodule.mem_span_singleton]
    exact ⟨a, by rw [Algebra.smul_def, mul_one]⟩

theorem coordSmall_eq_coordLattice :
    (coordSmall (p := p) (d := d) : Set (d → ℚ_[p])) =
      coordLattice (p := p) (d := d) := by
  have hspan : Submodule.span (PadicInt p) ({(1 : ℚ_[p])} : Set ℚ_[p]) = 1 :=
    span_one_eq_one
  apply Set.ext
  intro x
  simp only [coordSmall, Submodule.mem_pi, Set.mem_univ, forall_true_left, hspan]
  simp [coordLattice]

def coordSmallRows : List (String × String) :=
  [ ("span_one_eq_one", "green"),
    ("coordSmall_eq_coordLattice", "green"),
    ("diag image bridge", "GAP") ]
theorem coordSmallRows_length : coordSmallRows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1CoordSmallBridgeActual
