import tmp.sheaf.xif.paper.S2132D5FactorizationActual
import tmp.sheaf.xif.paper.S2481PairTransitiveHardActual

noncomputable section
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2553Mod613DegreeActual

open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual
open LeanFormal.IUT.XiFPaper.S2481PairTransitiveHardActual

/-- The explicit reduction of the integer model of psi_5 modulo 613. -/
def F613 : (ZMod 613)[X] := C 415 + C 203 * X ^ 2 + C 163 * X ^ 3 + C 443 * X ^ 4 + C 408 * X ^ 5 + C 580 * X ^ 6 + C 577 * X ^ 7 + C 401 * X ^ 8 + C 604 * X ^ 9 + C 461 * X ^ 10 + C 60 * X ^ 11 + C 478 * X ^ 12

theorem F613_eq_map :
    F613 = S2132Psi5Z.map (Int.castRingHom (ZMod 613)) := by
  ext n
  by_cases hn : n ≤ 12
  · interval_cases n <;>
      (simp [F613, S2132Psi5Z, Polynomial.coeff_add, Polynomial.coeff_C,
        Polynomial.coeff_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X,
        Polynomial.coeff_one] <;> decide)
  · have h1 : F613.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : F613.natDegree ≤ 12 := by unfold F613; compute_degree!
      omega
    have h2 : (S2132Psi5Z.map (Int.castRingHom (ZMod 613))).coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have hm : S2132Psi5Z.natDegree = 12 := by unfold S2132Psi5Z; compute_degree!
      have hle : (S2132Psi5Z.map (Int.castRingHom (ZMod 613))).natDegree ≤ S2132Psi5Z.natDegree := Polynomial.natDegree_map_le
      omega
    rw [h1, h2]

theorem F613_natDegree : F613.natDegree = 12 := by
  unfold F613
  compute_degree!

/-- The actual S2481 split H modulo 613. -/
theorem H613_splits :
    (S2481HZ.map (Int.castRingHom (ZMod 613))).Splits :=
  S2481HMod613_splits

/-- The still-missing irreducibility of F613. -/
def S2553Mod613IrreducibleRequired : Prop := Irreducible F613

end LeanFormal.IUT.XiFPaper.S2553Mod613DegreeActual

end