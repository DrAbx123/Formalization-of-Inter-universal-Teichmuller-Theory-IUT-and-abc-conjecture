import tmp.sheaf.xif.paper.S2167DedekindFrobCycleActual
open Polynomial
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual

example : Irreducible (S2132F2Z.map (Int.castRingHom (ZMod 29))) := by
  haveI : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp [S2132F2Z]
    norm_num
  · intro x hx
    rw [Polynomial.IsRoot] at hx
    simp only [S2132F2Z, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_ofNat, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X] at hx
    revert x
    decide
