import tmp.sheaf.xif.paper.S2167DedekindFrobCycleActual
import Mathlib.Tactic.ComputeDegree
open Polynomial
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual

example : (S2132F2Z.map (Int.castRingHom (ZMod 29))).natDegree = 2 := by
  compute_degree <;> decide

example : ∀ x : ZMod 29, ¬(S2132F2Z.map (Int.castRingHom (ZMod 29))).IsRoot x := by
  intro x
  fin_cases x <;> simp [S2132F2Z, Polynomial.IsRoot] <;> decide

example : Irreducible (S2132F2Z.map (Int.castRingHom (ZMod 29))) := by
  haveI : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [show (S2132F2Z.map (Int.castRingHom (ZMod 29))).natDegree = 2 by compute_degree <;> decide]
    simp
  · intro x
    fin_cases x <;> simp [S2132F2Z, Polynomial.IsRoot] <;> decide
