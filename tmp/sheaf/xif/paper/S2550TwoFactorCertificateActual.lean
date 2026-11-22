import tmp.sheaf.xif.paper.S2132D5FactorizationActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

namespace LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual

open Polynomial
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual

local instance : Fact (Nat.Prime 1249) := ⟨by norm_num⟩

/-- Explicit reduction of the actual psi5 integer model modulo 1249. -/
def S2550Psi5Mod1249 : (ZMod 1249)[X] :=
  C 548 + C 40 * X ^ 2 + C 375 * X ^ 3 + C 382 * X ^ 4 +
    C 245 * X ^ 5 + C 251 * X ^ 6 + C 337 * X ^ 7 + C 69 * X ^ 8 +
    C 1022 * X ^ 9 + C 1133 * X ^ 10 + C 99 * X ^ 11 + C 415 * X ^ 12

/-- The quadratic factor modulo 1249. -/
def S2550F2 : (ZMod 1249)[X] := X ^ 2 + C 917 * X + C 1160

/-- The degree-ten factor modulo 1249. -/
def S2550F10 : (ZMod 1249)[X] :=
  X ^ 10 + C 570 * X ^ 9 + C 817 * X ^ 8 + C 839 * X ^ 7 +
    C 1177 * X ^ 6 + C 242 * X ^ 5 + C 369 * X ^ 4 + C 1164 * X ^ 3 +
    C 1212 * X ^ 2 + C 166 * X + C 580

/-- The corrected two-factor product certificate at 1249. -/
theorem S2550Product :
    S2550Psi5Mod1249 = C 415 * (S2550F2 * S2550F10) := by
  ext n
  by_cases hn : n ≤ 12
  · interval_cases n <;>
      (simp [S2550Psi5Mod1249, S2550F2, S2550F10, Polynomial.coeff_add,
        Polynomial.coeff_mul, Polynomial.coeff_C, Polynomial.coeff_X_pow,
        Polynomial.coeff_X, Polynomial.coeff_one, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> decide)
  · have h1 : S2550Psi5Mod1249.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : S2550Psi5Mod1249.natDegree = 12 := by
        unfold S2550Psi5Mod1249
        compute_degree!
      omega
    have h2 : (C 415 * (S2550F2 * S2550F10)).coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have hf2 : S2550F2.natDegree = 2 := by
        unfold S2550F2; compute_degree!
      have hf10 : S2550F10.natDegree = 10 := by
        unfold S2550F10; compute_degree!
      have hC : (C (415 : ZMod 1249)).natDegree = 0 := by simp
      have hmul : (S2550F2 * S2550F10).natDegree ≤ S2550F2.natDegree + S2550F10.natDegree :=
        Polynomial.natDegree_mul_le
      have hdeg : (C 415 * (S2550F2 * S2550F10)).natDegree ≤ 12 := by
        calc
          (C 415 * (S2550F2 * S2550F10)).natDegree
              ≤ (C (415 : ZMod 1249)).natDegree + (S2550F2 * S2550F10).natDegree :=
                Polynomial.natDegree_mul_le
          _ ≤ 0 + (S2550F2.natDegree + S2550F10.natDegree) := by omega
          _ = 12 := by omega
      exact lt_of_le_of_lt hdeg (by omega)
    rw [h1, h2]

theorem S2550Psi5Mod1249_eq :
    S2550Psi5Mod1249 = S2132Psi5Z.map (Int.castRingHom (ZMod 1249)) := by
  ext n
  by_cases hn : n ≤ 12
  · interval_cases n <;>
      (simp [S2550Psi5Mod1249, S2132Psi5Z, Polynomial.coeff_add, Polynomial.coeff_C,
        Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · have h1 : S2550Psi5Mod1249.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : S2550Psi5Mod1249.natDegree = 12 := by
        unfold S2550Psi5Mod1249; compute_degree!
      omega
    have h2 : (S2132Psi5Z.map (Int.castRingHom (ZMod 1249))).coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have hle : (S2132Psi5Z.map (Int.castRingHom (ZMod 1249))).natDegree ≤ S2132Psi5Z.natDegree := Polynomial.natDegree_map_le
      have h12 : S2132Psi5Z.natDegree = 12 := by unfold S2132Psi5Z; compute_degree!
      omega
    rw [h1, h2]


/-- The quadratic factor is irreducible (finite root check over ZMod 1249). -/
theorem S2550F2_irreducible : Irreducible S2550F2 := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · have hdeg : S2550F2.natDegree = 2 := by
      unfold S2550F2
      compute_degree!
    rw [hdeg]
    norm_num
  · intro x hx
    have hnot : ∀ y : ZMod 1249, y ^ 2 + 917 * y + 1160 ≠ 0 := by
      decide +revert
    exact hnot x (by simpa [S2550F2, Polynomial.IsRoot] using hx)

def S2550QuadraticIrreducibleRequired : Prop := Irreducible S2550F2

def S2550DegreeTenIrreducibleRequired : Prop := Irreducible S2550F10

end LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual

end
