import tmp.sheaf.xif.paper.S2132D5FactorizationActual

noncomputable section
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2550Mod13IrreducibleActual

open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual

/-- The explicit reduction of the integer model of psi_5 modulo 13. -/
def F13 : (ZMod 13)[X] := C 12 + C 3 * X ^ 2 + C 12 * X ^ 3 + C 10 * X ^ 4 + C 12 * X ^ 5 + C 10 * X ^ 7 + C 1 * X ^ 8 + C 12 * X ^ 9 + C 11 * X ^ 10 + C 2 * X ^ 11 + C 5 * X ^ 12

/-- The explicit reduction is the map of the integer model. -/
theorem F13_eq_map :
    F13 = S2132Psi5Z.map (Int.castRingHom (ZMod 13)) := by
  ext n
  by_cases hn : n ≤ 12
  · interval_cases n <;>
      (simp [F13, S2132Psi5Z, Polynomial.coeff_add, Polynomial.coeff_C,
        Polynomial.coeff_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X,
        Polynomial.coeff_one] <;> decide)
  · have h1 : F13.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : F13.natDegree ≤ 12 := by unfold F13; compute_degree!
      omega
    have h2 : (S2132Psi5Z.map (Int.castRingHom (ZMod 13))).coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have hm : S2132Psi5Z.natDegree = 12 := by unfold S2132Psi5Z; compute_degree!
      have hle : (S2132Psi5Z.map (Int.castRingHom (ZMod 13))).natDegree ≤ S2132Psi5Z.natDegree := Polynomial.natDegree_map_le
      omega
    rw [h1, h2]

theorem F13_natDegree : F13.natDegree = 12 := by
  unfold F13
  compute_degree!

/-- The exact still-missing p = 13 irreducibility target. -/
def S2550Mod13IrreducibleRequired : Prop :=
  Irreducible F13

end LeanFormal.IUT.XiFPaper.S2550Mod13IrreducibleActual

end