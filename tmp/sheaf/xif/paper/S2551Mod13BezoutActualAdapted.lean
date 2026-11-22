import tmp.sheaf.xif.paper.S2550Mod13IrreducibleActual

noncomputable section
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2551Mod13BezoutActualAdapted

open LeanFormal.IUT.XiFPaper.S2550Mod13IrreducibleActual

def T4 : (ZMod 13)[X] := C 2 + C 4 * X + C 2 * X ^ 2 + C 9 * X ^ 3 + C 5 * X ^ 4 + C 3 * X ^ 5 + C 12 * X ^ 6 + C 9 * X ^ 7 + C 9 * X ^ 8 + C 4 * X ^ 9 + C 8 * X ^ 10 + C 3 * X ^ 11
def P4 : (ZMod 13)[X] := C 6 + C 11 * X + C 1 * X ^ 2 + C 11 * X ^ 3 + C 2 * X ^ 4 + C 10 * X ^ 5 + C 7 * X ^ 6 + C 1 * X ^ 7 + C 3 * X ^ 8 + C 1 * X ^ 9 + C 12 * X ^ 10
def Q4 : (ZMod 13)[X] := C 10 + C 10 * X + C 12 * X ^ 2 + C 10 * X ^ 3 + C 8 * X ^ 4 + C 3 * X ^ 5 + C 1 * X ^ 7 + C 1 * X ^ 8 + C 5 * X ^ 9 + C 9 * X ^ 10 + C 6 * X ^ 11
def T6 : (ZMod 13)[X] := C 2 + C 5 * X + C 12 * X ^ 2 + C 7 * X ^ 3 + C 6 * X ^ 4 + C 11 * X ^ 5 + C 11 * X ^ 6 + C 6 * X ^ 7 + C 11 * X ^ 8 + C 1 * X ^ 9 + C 5 * X ^ 10 + C 6 * X ^ 11
def P6 : (ZMod 13)[X] := C 5 + C 4 * X + C 10 * X ^ 2 + C 6 * X ^ 3 + C 6 * X ^ 4 + C 6 * X ^ 5 + C 4 * X ^ 6 + C 5 * X ^ 7 + C 1 * X ^ 8 + C 8 * X ^ 9 + C 10 * X ^ 10
def Q6 : (ZMod 13)[X] := C 3 + C 9 * X + C 7 * X ^ 2 + C 12 * X ^ 3 + C 8 * X ^ 4 + C 1 * X ^ 5 + C 3 * X ^ 6 + C 1 * X ^ 7 + C 6 * X ^ 8 + C 1 * X ^ 9 + C 2 * X ^ 10 + C 9 * X ^ 11

lemma bezoutT4 : P4 * F13 + Q4 * (T4 - X) = 1 := by
  ext n
  by_cases hn : n ≤ 24
  · interval_cases n <;>
      (simp [P4, Q4, T4, F13, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X,
        Polynomial.coeff_one, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> decide)
  · have h1 : (P4 * F13 + Q4 * (T4 - X)).coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : (P4 * F13 + Q4 * (T4 - X)).natDegree ≤ 24 := by
        unfold P4 Q4 T4 F13; compute_degree!
      omega
    have h2 : (1 : (ZMod 13)[X]).coeff n = 0 := by rw [Polynomial.coeff_one, if_neg (by omega)]
    rw [h1, h2]

lemma bezoutT6 : P6 * F13 + Q6 * (T6 - X) = 1 := by
  ext n
  by_cases hn : n ≤ 24
  · interval_cases n <;>
      (simp [P6, Q6, T6, F13, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X,
        Polynomial.coeff_one, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> decide)
  · have h1 : (P6 * F13 + Q6 * (T6 - X)).coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : (P6 * F13 + Q6 * (T6 - X)).natDegree ≤ 24 := by
        unfold P6 Q6 T6 F13; compute_degree!
      omega
    have h2 : (1 : (ZMod 13)[X]).coeff n = 0 := by rw [Polynomial.coeff_one, if_neg (by omega)]
    rw [h1, h2]

theorem coprime_T4 : IsCoprime F13 (T4 - X) := ⟨P4, Q4, bezoutT4⟩
theorem coprime_T6 : IsCoprime F13 (T6 - X) := ⟨P6, Q6, bezoutT6⟩

end LeanFormal.IUT.XiFPaper.S2551Mod13BezoutActualAdapted

end