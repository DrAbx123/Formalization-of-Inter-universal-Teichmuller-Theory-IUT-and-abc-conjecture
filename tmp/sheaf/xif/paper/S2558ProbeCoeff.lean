import Mathlib

open Polynomial

namespace ProbeCoeff

def L : (ZMod 1249)[X] :=
  (1 + 2 * X + 3 * X ^ 2 + 4 * X ^ 3 + 5 * X ^ 4 + 6 * X ^ 5 +
    7 * X ^ 6 + 8 * X ^ 7 + 9 * X ^ 8 + 10 * X ^ 9) ^ 2

def R : (ZMod 1249)[X] :=
  (580 + 166 * X + 1212 * X ^ 2 + 1164 * X ^ 3 + 369 * X ^ 4 + 242 * X ^ 5 +
    1177 * X ^ 6 + 839 * X ^ 7 + 817 * X ^ 8 + 570 * X ^ 9 + X ^ 10) *
  (284 + 428 * X + 405 * X ^ 2 + 423 * X ^ 3 + 206 * X ^ 4 +
    750 * X ^ 5 + 556 * X ^ 6 + 634 * X ^ 7 + 100 * X ^ 8) +
  (149 + 633 * X + 583 * X ^ 2 + 957 * X ^ 3 + 461 * X ^ 4 + 9 * X ^ 5 +
    1098 * X ^ 6 + 605 * X ^ 7 + 247 * X ^ 8 + 965 * X ^ 9)

theorem probe : L = R := by
  have hL : L.natDegree ≤ 18 := by unfold L; compute_degree!
  have hR : R.natDegree ≤ 18 := by unfold R; compute_degree!
  apply Polynomial.ext
  intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (dsimp [L, R]; simp [Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_one,
        Polynomial.coeff_X] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

end ProbeCoeff
