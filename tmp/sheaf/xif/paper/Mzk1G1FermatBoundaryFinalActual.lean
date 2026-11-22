/- G1a boundary/degree/ramification final. -/
import tmp.sheaf.xif.paper.Mzk1G1FermatCoverDataActual
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCoverDataActual
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatBoundaryFinalActual
theorem boundary_eq_three_n (n : Nat) (hn : 3 ≤ n) :
    (fermatCoverData n hn).boundaryDegree = 3 * (n : Rat) := rfl
theorem degree_eq_n_sq (n : Nat) (hn : 3 ≤ n) :
    (fermatCoverData n hn).degree = (n : Rat) ^ 2 := rfl
theorem ramification_eq_n (n : Nat) (hn : 3 ≤ n) :
    (fermatCoverData n hn).ramification = (n : Rat) := rfl
theorem boundary_degree_sum (n : Nat) (hn : 3 ≤ n) :
    (fermatCoverData n hn).boundaryDegree = 3 * (n : Rat) ∧
    (fermatCoverData n hn).degree = (n : Rat) ^ 2 :=
  ⟨rfl, rfl⟩
#print axioms boundary_degree_sum
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatBoundaryFinalActual
