import tmp.sheaf.xif.paper.S2550Mod13IrreducibleActual
import tmp.sheaf.xif.paper.S2583FactorDegreeActual

noncomputable section
set_option maxHeartbeats 8000000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2552Mod13RabinActual

open LeanFormal.IUT.XiFPaper.S2550Mod13IrreducibleActual

/-- The monic normalization of F13. -/
def G : (ZMod 13)[X] := C 5 + C 11 * X ^ 2 + C 5 * X ^ 3 + C 2 * X ^ 4 + C 5 * X ^ 5 + C 2 * X ^ 7 + C 8 * X ^ 8 + C 5 * X ^ 9 + C 10 * X ^ 10 + C 3 * X ^ 11 + C 1 * X ^ 12

def T4 : (ZMod 13)[X] := C 2 + C 4 * X + C 2 * X ^ 2 + C 9 * X ^ 3 + C 5 * X ^ 4 + C 3 * X ^ 5 + C 12 * X ^ 6 + C 9 * X ^ 7 + C 9 * X ^ 8 + C 4 * X ^ 9 + C 8 * X ^ 10 + C 3 * X ^ 11

def T6 : (ZMod 13)[X] := C 2 + C 5 * X + C 12 * X ^ 2 + C 7 * X ^ 3 + C 6 * X ^ 4 + C 11 * X ^ 5 + C 11 * X ^ 6 + C 6 * X ^ 7 + C 11 * X ^ 8 + C 1 * X ^ 9 + C 5 * X ^ 10 + C 6 * X ^ 11

def U4 : (ZMod 13)[X] := C 4 + C 3 * X + C 5 * X ^ 2 + C 3 * X ^ 3 + C 10 * X ^ 4 + C 11 * X ^ 5 + C 9 * X ^ 6 + C 5 * X ^ 7 + C 2 * X ^ 8 + C 5 * X ^ 9 + C 8 * X ^ 10

def V4 : (ZMod 13)[X] := C 10 + C 10 * X + C 12 * X ^ 2 + C 10 * X ^ 3 + C 8 * X ^ 4 + C 3 * X ^ 5 + C 1 * X ^ 7 + C 1 * X ^ 8 + C 5 * X ^ 9 + C 9 * X ^ 10 + C 6 * X ^ 11

def U6 : (ZMod 13)[X] := C 12 + C 7 * X + C 11 * X ^ 2 + C 4 * X ^ 3 + C 4 * X ^ 4 + C 4 * X ^ 5 + C 7 * X ^ 6 + C 12 * X ^ 7 + C 5 * X ^ 8 + C 1 * X ^ 9 + C 11 * X ^ 10

def V6 : (ZMod 13)[X] := C 3 + C 9 * X + C 7 * X ^ 2 + C 12 * X ^ 3 + C 8 * X ^ 4 + C 1 * X ^ 5 + C 3 * X ^ 6 + C 1 * X ^ 7 + C 6 * X ^ 8 + C 1 * X ^ 9 + C 2 * X ^ 10 + C 9 * X ^ 11

lemma G_eq_scaled_F13 : G = C (8 : ZMod 13) * F13 := by
  ext n
  by_cases hn : n ≤ 12
  · interval_cases n <;> (simp [G, F13] <;> decide)
  · have h1 : G.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : G.natDegree ≤ 12 := by unfold G; compute_degree!
      omega
    have h2 : (C (8 : ZMod 13) * F13).coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : (C (8 : ZMod 13) * F13).natDegree ≤ 12 := by unfold F13; compute_degree!
      omega
    rw [h1, h2]

lemma bezoutT4 : U4 * G + V4 * (T4 - X) = 1 := by
  ext n
  by_cases hn : n ≤ 24
  · interval_cases n <;>
      (simp [U4, V4, T4, G, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X,
        Polynomial.coeff_one, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> decide)
  · have h1 : (U4 * G + V4 * (T4 - X)).coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : (U4 * G + V4 * (T4 - X)).natDegree ≤ 24 := by unfold U4 V4 T4 G; compute_degree!
      omega
    have h2 : (1 : (ZMod 13)[X]).coeff n = 0 := by rw [Polynomial.coeff_one, if_neg (by omega)]
    rw [h1, h2]

lemma bezoutT6 : U6 * G + V6 * (T6 - X) = 1 := by
  ext n
  by_cases hn : n ≤ 24
  · interval_cases n <;>
      (simp [U6, V6, T6, G, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X,
        Polynomial.coeff_one, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> decide)
  · have h1 : (U6 * G + V6 * (T6 - X)).coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : (U6 * G + V6 * (T6 - X)).natDegree ≤ 24 := by unfold U6 V6 T6 G; compute_degree!
      omega
    have h2 : (1 : (ZMod 13)[X]).coeff n = 0 := by rw [Polynomial.coeff_one, if_neg (by omega)]
    rw [h1, h2]

theorem coprime_T4 : IsCoprime G (T4 - X) := ⟨U4, V4, bezoutT4⟩
theorem coprime_T6 : IsCoprime G (T6 - X) := ⟨U6, V6, bezoutT6⟩

end LeanFormal.IUT.XiFPaper.S2552Mod13RabinActual

end