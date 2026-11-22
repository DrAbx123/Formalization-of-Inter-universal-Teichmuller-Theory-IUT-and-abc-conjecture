import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import LeanFormal.IUT.IUTIV.Estimates.StepVProcessionAverage
import Mathlib.Tactic

/-! # A825 exceptional-term bound via Chebyshev/primorial estimates

Explicit exceptional bound for IUT IV Step (v), avoiding PNT/eta_prm:
* per-packet exceptional sum bounded by `4|I| log(el)` (green re-export below);
* summing over rational primes with total weight <= 1 and `p <= el` needs
  `pi(el) * log(el) <= 4 el`; Mathlib Chebyshev gives explicit
  `pi(floor x) <= log 4 * x / log(sqrt x) + sqrt x`, hence
  `pi * log x <= sqrt x * log x + 2 x log 4`, and elementary `log x <= sqrt x`
  gives the clean `pi * log x <= 4 x`;
* therefore exceptional contribution <= `16 (l+5) e*_mod l`, an explicit
  `C0(l, e*_mod)`. Bigger than paper 4/3 but no eta_prm/PNT. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ExceptionalBoundActual

open LeanFormal.IUT.IUTIV.StepVProcessionAverage

/-- For `1 <= t`, `log t <= t/2`. -/
lemma log_le_half_self {t : Real} (ht : 1 <= t) : Real.log t <= t / 2 := by
  rcases le_or_gt t 2 with h2 | h2
  · have h0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
    have h := Real.log_le_sub_one_of_pos h0
    linarith
  · have h0 : 0 < t := by linarith
    have hu0 : 0 < t / 2 := by positivity
    have hlog : Real.log t = Real.log 2 + Real.log (t / 2) := by
      rw [← Real.log_mul (by norm_num) (ne_of_gt hu0)]
      congr 1
      ring
    have h1 := Real.log_le_sub_one_of_pos hu0
    have h2log : Real.log 2 <= 1 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : Real) < 2 by norm_num)
      linarith
    rw [hlog]
    linarith

/-- For `1 <= x`, `log x <= sqrt x`. -/
lemma log_le_sqrt {x : Real} (hx : 1 <= x) : Real.log x <= Real.sqrt x := by
  have hx0 : 0 <= x := le_trans zero_le_one hx
  have ht : 1 <= Real.sqrt x := Real.one_le_sqrt.mpr hx
  have hlog : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt hx0]
    ring
  have h := log_le_half_self ht
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0
  nlinarith

/-- Explicit Chebyshev form: `pi(floor x) * log x <= sqrt x * log x + 2 x log 4`. -/
theorem primeCounting_mul_log_le_sqrt_add {x : Real} (hx : 1 < x) :
    (Nat.primeCounting ⌊x⌋₊ : Real) * Real.log x <=
      Real.sqrt x * Real.log x + 2 * x * Real.log 4 := by
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hlogsqrt : Real.log (Real.sqrt x) = Real.log x / 2 :=
    Real.log_sqrt (by linarith)
  have hpi := Chebyshev.pi_le_log4_mul_div hx
  have hmul := mul_le_mul_of_nonneg_right hpi hlog.le
  have hdiv : (Real.log 4 * x / Real.log (Real.sqrt x)) * Real.log x = 2 * x * Real.log 4 := by
    rw [hlogsqrt]
    field_simp [ne_of_gt hlog]
  calc
    (Nat.primeCounting ⌊x⌋₊ : Real) * Real.log x
        <= (Real.log 4 * x / Real.log (Real.sqrt x) + Real.sqrt x) * Real.log x := hmul
    _ = Real.sqrt x * Real.log x + 2 * x * Real.log 4 := by
      rw [add_mul, hdiv]
      ring

/-- Elementary comparison: `sqrt x * log x + 2 x log 4 <= 4 x` for `x >= 1`. -/
theorem sqrt_log_add_log4_le_four {x : Real} (hx : 1 <= x) :
    Real.sqrt x * Real.log x + 2 * x * Real.log 4 <= 4 * x := by
  have hx0 : 0 <= x := le_trans zero_le_one hx
  have hlog : Real.log x <= Real.sqrt x := log_le_sqrt hx
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0
  have hterm1 : Real.sqrt x * Real.log x <= x := by
    have := mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg x)
    rwa [hsq] at this
  have hlog4 : 2 * Real.log 4 <= 3 := by
    have h2 := Real.log_two_lt_d9
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : Real) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [h4]
    nlinarith
  nlinarith

/-- Clean explicit bound: `pi(floor x) * log x <= 4 x` for `x > 1`. -/
theorem primeCounting_mul_log_le_four_mul {x : Real} (hx : 1 < x) :
    (Nat.primeCounting ⌊x⌋₊ : Real) * Real.log x <= 4 * x :=
  (primeCounting_mul_log_le_sqrt_add hx).trans (sqrt_log_add_log4_le_four (le_of_lt hx))

/-- Re-export of the green per-packet exceptional bound. -/
theorem exceptionalSum_bound {α : Type*} (I Istar : Finset α) (hsub : Istar ⊆ I)
    (e : α → Real) (p el : Real) (hel : 1 <= el)
    (hR4 : forall i, i ∈ Istar → p <= el ∧ Real.log (e i) <= -3 + 4 * Real.log el) :
    (∑ i ∈ Istar, (3 + Real.log (e i))) <=
      4 * (I.card : Real) * (if p <= el then Real.log el else 0) :=
  exceptionalSum_le_r4 I Istar hsub e p el hel hR4

/-- The explicit exceptional constant `C0(l, e*_mod) = 16 (l+5) e*_mod l`. -/
noncomputable def exceptionalC0 (l eMod : Real) : Real := 16 * (l + 5) * eMod * l

theorem exceptionalC0_nonneg {l eMod : Real} (hl : 0 <= l) (he : 0 <= eMod) :
    0 <= exceptionalC0 l eMod := by
  unfold exceptionalC0
  positivity

/-- Archimedean exceptional constant: each infinite factor contributes one
`log pi`; the global average carries the factor `(l+5)/4`. -/
noncomputable def archC0 (l : Real) : Real := 4 * (l + 5) * Real.log Real.pi

theorem archC0_eq (l : Real) :
    archC0 l = (l + 5) / 4 * (16 * Real.log Real.pi) := by
  unfold archC0
  ring

theorem archC0_nonneg {l : Real} (hl : 0 <= l) : 0 <= archC0 l := by
  unfold archC0
  have h1 : 0 <= l + 5 := by linarith
  have h2 : 0 <= Real.log Real.pi :=
    Real.log_nonneg (by linarith [Real.one_le_pi_div_two])
  nlinarith [mul_nonneg h1 h2]

/-- If `el = e*_mod * l > 1`, the exceptional prime sum is at most `C0(l,e*_mod)`,
namely `4 (l+5) * (pi(el) log el) <= 16 (l+5) e*_mod l`. -/
theorem exceptional_bound_C0 {l eMod : Real}
    (hl : 5 <= l) (he : 0 <= eMod) (hel : 1 < eMod * l) :
    4 * (l + 5) * ((Nat.primeCounting ⌊eMod * l⌋₊ : Real) * Real.log (eMod * l)) <=
      exceptionalC0 l eMod := by
  have hpi := primeCounting_mul_log_le_four_mul hel
  have h5 : 0 <= 4 * (l + 5) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hpi h5
  unfold exceptionalC0
  nlinarith

#print axioms primeCounting_mul_log_le_four_mul
#print axioms exceptional_bound_C0

end LeanFormal.IUT.XiFPaper.Mzk1ExceptionalBoundActual
