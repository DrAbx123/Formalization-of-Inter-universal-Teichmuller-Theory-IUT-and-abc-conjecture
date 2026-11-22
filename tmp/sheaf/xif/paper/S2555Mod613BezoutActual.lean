import tmp.sheaf.xif.paper.S2554Mod613ChainDataActual

noncomputable section
set_option maxHeartbeats 8000000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2555Mod613BezoutActual

open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual

def U4 : (ZMod 613)[X] := C 233 + C 486 * X + C 572 * X ^ 2 + C 19 * X ^ 3 + C 446 * X ^ 4 + C 378 * X ^ 5 + C 325 * X ^ 6 + C 204 * X ^ 7 + C 426 * X ^ 8 + C 609 * X ^ 9 + C 215 * X ^ 10
def V4 : (ZMod 613)[X] := C 594 + C 315 * X + C 228 * X ^ 2 + C 152 * X ^ 3 + C 129 * X ^ 4 + C 272 * X ^ 5 + C 169 * X ^ 6 + C 346 * X ^ 7 + C 108 * X ^ 8 + C 47 * X ^ 9 + C 366 * X ^ 10 + C 190 * X ^ 11
def U6 : (ZMod 613)[X] := C 62 + C 77 * X + C 81 * X ^ 2 + C 490 * X ^ 3 + C 561 * X ^ 4 + C 142 * X ^ 5 + C 76 * X ^ 6 + C 324 * X ^ 7 + C 188 * X ^ 8 + C 604 * X ^ 9 + C 133 * X ^ 10
def V6 : (ZMod 613)[X] := C 92 + C 556 * X + C 445 * X ^ 2 + C 235 * X ^ 3 + C 564 * X ^ 4 + C 280 * X ^ 5 + C 419 * X ^ 6 + C 203 * X ^ 7 + C 226 * X ^ 8 + C 477 * X ^ 9 + C 460 * X ^ 10 + C 487 * X ^ 11

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
    have h2 : (1 : (ZMod 613)[X]).coeff n = 0 := by rw [Polynomial.coeff_one, if_neg (by omega)]
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
    have h2 : (1 : (ZMod 613)[X]).coeff n = 0 := by rw [Polynomial.coeff_one, if_neg (by omega)]
    rw [h1, h2]

theorem coprime_T4 : IsCoprime G (T4 - X) := ⟨U4, V4, bezoutT4⟩
theorem coprime_T6 : IsCoprime G (T6 - X) := ⟨U6, V6, bezoutT6⟩

end LeanFormal.IUT.XiFPaper.S2555Mod613BezoutActual

end