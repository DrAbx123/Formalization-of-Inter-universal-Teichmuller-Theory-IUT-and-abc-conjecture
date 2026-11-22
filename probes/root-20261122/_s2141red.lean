import tmp.sheaf.xif.paper.S2132D5FactorizationActual
open Polynomial
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual
noncomputable def PZsmall : (ZMod 29)[X] :=
  C 16 + C 21 * X^2 + C 21 * X^3 + C 15 * X^4 + C 1 * X^5 + C 6 * X^6 + C 24 * X^7 + C 14 * X^8 + C 10 * X^9 + C 10 * X^10 + C 8 * X^11 + C 4 * X^12
example : S2132Psi5Z.map (Int.castRingHom (ZMod 29)) = PZsmall := by
  ext n
  by_cases hn : n ≤ 12
  · interval_cases n <;> (simp [S2132Psi5Z, PZsmall] <;> decide)
  · have h1 : (S2132Psi5Z.map (Int.castRingHom (ZMod 29))).coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      simp [S2132Psi5Z]
      compute_degree!
      omega
    have h2 : PZsmall.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      simp [PZsmall]
      compute_degree!
      omega
    rw [h1,h2]
