import tmp.sheaf.xif.paper.S2167DedekindFrobCycleActual
open Polynomial
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual

example : (S2132F2Z.map (Int.castRingHom (ZMod 29))) =
    (C (19 : ZMod 29) + C 24 * X + C 4 * X ^ 2) := by
  simp only [S2132F2Z, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_ofNat]
  push_cast
  ring_nf

example : Irreducible (S2132F2Z.map (Int.castRingHom (ZMod 29))) := by
  haveI : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  have hpoly : (S2132F2Z.map (Int.castRingHom (ZMod 29))) =
      (C (4 : ZMod 29) * X ^ 2 + C 24 * X + C 19) := by
    rw [show (S2132F2Z.map (Int.castRingHom (ZMod 29))) =
      (C (19 : ZMod 29) + C 24 * X + C 4 * X ^ 2) by
        simp only [S2132F2Z, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
          Polynomial.map_X, Polynomial.map_ofNat]
        push_cast
        ring_nf]
    ring
  rw [hpoly]
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have h4 : (4 : ZMod 29) ≠ 0 := by decide
    rw [Polynomial.natDegree_quadratic h4]
    simp
  · intro x hx
    rw [Polynomial.IsRoot] at hx
    revert x
    decide
