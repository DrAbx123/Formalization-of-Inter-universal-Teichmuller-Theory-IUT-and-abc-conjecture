/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport

/-! # A703: concrete triple Theta-data model (no hfull / no N-scaling) -/

/- ① q-pilot of a triple: q = (abc)^2, hence log q = 2 log(abc) and (1/6) log q = (1/3) log(abc).
② Bounded-region estimate (the user's restriction "a,b comparable with c"):
   from `c <= K * (a*b)` one gets `2 log c <= log(abc) + log K`,
   i.e. `log c <= (1/2) log(abc) + (1/2) log K` (coefficient 1/2, not 1/3).
   The 1/3 form `3 log c <= log K + log(abc)` additionally needs `c^2 <= K * a*b`;
   both correct statements are recorded below — no false inequality is asserted.
③ f = natRadical(abc), log f = sum_{p | abc} log p.
④ Scope: general triples with small a,b (ab << c^2) need N5 (GenEll/Belyi);
   NOT claimed here. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1TripleThetaModelActual

/-- ① The concrete q-pilot of the triple: `(a*b*c)^2`. -/
def qPilotOfTriple (a b c : Nat) : Nat := (a * b * c) ^ 2

/-- ① `log q = 2 log(abc)` (positivity of `a*b*c` is the one hypothesis). -/
theorem qPilot_log {a b c : Nat} (habc : 0 < a * b * c) :
    Real.log ((qPilotOfTriple a b c : Nat) : ℝ) =
      2 * Real.log (((a * b * c : Nat)) : ℝ) := by
  unfold qPilotOfTriple
  rw [Nat.cast_pow, Real.log_pow]
  push_cast
  ring

/-- ① `(1/6) log q = (1/3) log(abc)`. -/
theorem one_sixth_qPilot_log {a b c : Nat} (habc : 0 < a * b * c) :
    (1/6 : ℝ) * Real.log ((qPilotOfTriple a b c : Nat) : ℝ) =
      (1/3 : ℝ) * Real.log (((a * b * c : Nat)) : ℝ) := by
  rw [qPilot_log habc]
  ring

/-- ② Bounded-region estimate (correct `1/2` form): if `c <= K*(a*b)` with `K > 0`, then
`2 log c <= log(abc) + log K`. -/
theorem bounded_log_c_le_half {a b c : Nat} {K : ℝ} (hc : 0 < c) (habc : 0 < a * b * c)
    (hK : 0 < K) (hbdd : (c : ℝ) ≤ K * ((a * b : Nat) : ℝ)) :
    2 * Real.log (c : ℝ) ≤ Real.log (((a * b * c : Nat)) : ℝ) + Real.log K := by
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hab_pos : (0 : ℝ) < ((a * b : Nat) : ℝ) := by
    by_contra h
    push_neg at h
    have : (c : ℝ) ≤ 0 := by
      calc (c : ℝ) ≤ K * ((a * b : Nat) : ℝ) := hbdd
        _ ≤ 0 := by nlinarith
    linarith
  have hprod : (0 : ℝ) < K * ((a * b : Nat) : ℝ) := mul_pos hK hab_pos
  have hsq : (c : ℝ) ^ 2 ≤ K * (((a * b * c : Nat)) : ℝ) := by
    have hmul : (c : ℝ) * (c : ℝ) ≤ (c : ℝ) * (K * ((a * b : Nat) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hbdd (le_of_lt hcR)
    calc (c : ℝ) ^ 2 = (c : ℝ) * (c : ℝ) := by ring
      _ ≤ (c : ℝ) * (K * ((a * b : Nat) : ℝ)) := hmul
      _ = K * (((a * b * c : Nat)) : ℝ) := by push_cast; ring
  have hlog : 2 * Real.log (c : ℝ) = Real.log ((c : ℝ) ^ 2) := by
    rw [Real.log_pow]; norm_num
  rw [hlog]
  have hmono : Real.log ((c : ℝ) ^ 2) ≤ Real.log (K * (((a * b * c : Nat)) : ℝ)) :=
    Real.log_le_log (by positivity) hsq
  have hsplit : Real.log (K * (((a * b * c : Nat)) : ℝ)) = Real.log K + Real.log (((a * b * c : Nat)) : ℝ) :=
    Real.log_mul hK.ne' (by exact_mod_cast (ne_of_gt habc)) 
  linarith

/-- ② The `1/3` form, with the stronger hypothesis `c^2 <= K*(a*b)` (then `c^3 <= K*abc`). -/
theorem bounded_log_c_le_third {a b c : Nat} {K : ℝ} (hc : 0 < c) (habc : 0 < a * b * c)
    (hK : 0 < K) (hbdd : ((c : ℝ) ^ 2) ≤ K * ((a * b : Nat) : ℝ)) :
    3 * Real.log (c : ℝ) ≤ Real.log (((a * b * c : Nat)) : ℝ) + Real.log K := by
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hcube : ((c : ℝ)) ^ 3 ≤ K * (((a * b * c : Nat)) : ℝ) := by
    calc (c : ℝ) ^ 3 = (c : ℝ) * ((c : ℝ) ^ 2) := by ring
      _ ≤ (c : ℝ) * (K * ((a * b : Nat) : ℝ)) := mul_le_mul_of_nonneg_left hbdd (le_of_lt hcR)
      _ = K * (((a * b * c : Nat)) : ℝ) := by push_cast; ring
  have hlog : 3 * Real.log (c : ℝ) = Real.log ((c : ℝ) ^ 3) := by
    rw [Real.log_pow]; norm_num
  rw [hlog]
  have hmono : Real.log ((c : ℝ) ^ 3) ≤ Real.log (K * (((a * b * c : Nat)) : ℝ)) :=
    Real.log_le_log (by positivity) hcube
  have hsplit : Real.log (K * (((a * b * c : Nat)) : ℝ)) = Real.log K + Real.log (((a * b * c : Nat)) : ℝ) :=
    Real.log_mul hK.ne' (by exact_mod_cast (ne_of_gt habc))
  linarith

/-- ③ The radical of the triple. -/
def radOfTriple (a b c : Nat) : Nat := natRadical (a * b * c)

/-- ③ `log rad(abc) = sum_{p | abc} log p`. -/
theorem log_rad_eq_sum (a b c : Nat) :
    Real.log ((radOfTriple a b c : Nat) : ℝ) =
      ∑ p ∈ (a * b * c).primeFactors, Real.log (p : ℝ) := by
  unfold radOfTriple
  exact natRadical_cast_log_eq_sum_primeFactors (a * b * c)

end LeanFormal.IUT.XiFPaper.Mzk1TripleThetaModelActual
