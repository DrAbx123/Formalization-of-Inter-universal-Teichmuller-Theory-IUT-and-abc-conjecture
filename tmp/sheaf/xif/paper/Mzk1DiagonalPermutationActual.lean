/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1PermutationHaarActual
import tmp.sheaf.xif.paper.Mzk1MatrixHaarBaseActual

/-! # diagonal scaling composed with coordinate permutation (task-109) -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1DiagonalPermutationActual
open LeanFormal.IUT.XiFPaper.Mzk1PermutationHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1MatrixHaarBaseActual
variable {p : Nat} [Fact p.Prime] {d : Type} [Fintype d] [DecidableEq d]
/-- Diagonal scaling followed by coordinate permutation. -/
def diagPermAct (σ : Equiv.Perm d) (e : d → Nat) (x : d → ℚ_[p]) :
    d → ℚ_[p] :=
  permAct σ (diagAct p d e x)
theorem diagPermAct_apply (σ : Equiv.Perm d) (e : d → Nat) (x : d → ℚ_[p])
    (i : d) : diagPermAct σ e x i =
      (p : ℚ_[p]) ^ (e (σ i)) * x (σ i) := rfl
def diagPermRows : List (String × String) :=
  [ ("diagPermAct", "diag then permutation"),
    ("measure invariance", "GAP") ]
theorem diagPermRows_length : diagPermRows.length = 2 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1DiagonalPermutationActual
