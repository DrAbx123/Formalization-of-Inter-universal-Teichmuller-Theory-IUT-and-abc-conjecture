import Mathlib

set_option maxRecDepth 100000

open Polynomial

namespace ProbeCoeff2

noncomputable def L : (ZMod 1249)[X] :=
  1 + X * 4 + X ^ 2 * 10 + X ^ 3 * 20 + X ^ 4 * 35 + X ^ 5 * 56 +
    X ^ 6 * 84 + X ^ 7 * 120 + X ^ 8 * 165 + X ^ 9 * 220 + X ^ 10 * 264 +
    X ^ 11 * 296 + X ^ 12 * 315 + X ^ 13 * 320 + X ^ 14 * 310 +
    X ^ 15 * 284 + X ^ 16 * 241 + X ^ 17 * 180 + X ^ 18 * 100

noncomputable def R : (ZMod 1249)[X] :=
  164869 + X * 296017 + X ^ 2 * 650739 + X ^ 3 * 1162839 +
    X ^ 4 * 1284007 + X ^ 5 * 1679961 + X ^ 6 * 1777411 +
    X ^ 7 * 2605534 + X ^ 8 * 2956548 + X ^ 9 * 3108981 +
    X ^ 10 * 2418328 + X ^ 11 * 2117351 + X ^ 12 * 1883807 +
    X ^ 13 * 1967495 + X ^ 14 * 1531584 + X ^ 15 * 919548 +
    X ^ 16 * 443636 + X ^ 17 * 57634 + X ^ 18 * 100

theorem probe : L = R := by
  have hL : L.natDegree ≤ 18 := by unfold L; compute_degree!
  have hR : R.natDegree ≤ 18 := by unfold R; compute_degree!
  apply Polynomial.ext
  intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [L, R, Polynomial.coeff_add, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

end ProbeCoeff2
