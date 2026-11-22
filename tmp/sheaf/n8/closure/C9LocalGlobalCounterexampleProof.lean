import tmp.sheaf.n8.closure.C9LocalGlobalCounterexample
import Mathlib

/-!
# C9 local-global counterexample: proof of the no-global-linear proposition

Proves that no nonzero rational f is integral at every finite p != 3, lies in
3 Z_3, and satisfies |f| <= 1.  The numerator/denominator argument:

* a prime divisor p != 3 of the denominator would give v_p(f) < 0;
* 3 does not divide the denominator because v_3(f) >= 1;
* hence the denominator is 1;
* then f is an integer divisible by 3, so |f| >= 3, contradicting |f| <= 1.
-/

noncomputable section

namespace ABCBridge.N8.C9LocalGlobalCounterexampleProof

open ABCBridge.N8.C9LocalGlobalCounterexample

/-- If p is prime and divides the denominator of f != 0, then v_p(f) < 0. -/
theorem padicValRat_neg_of_dvd_den {f : ℚ} (hf : f ≠ 0)
    {p : ℕ} (hp : Nat.Prime p) (hdvd : p ∣ f.den) :
    padicValRat p f < 0 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hdenne : f.den ≠ 0 := f.den_ne_zero
  have hvden : 1 ≤ padicValNat p f.den :=
    one_le_padicValNat_of_dvd hdenne hdvd
  have hnotdvd : ¬ (p : ℤ) ∣ f.num := by
    intro hnum
    have hpnum : p ∣ f.num.natAbs :=
      Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hnum)
    have hg : Nat.gcd f.num.natAbs f.den = 1 := f.reduced
    have hp1 : p ∣ 1 := by
      have h := Nat.dvd_gcd hpnum hdvd
      simpa [hg] using h
    exact hp.not_dvd_one hp1
  have hvnum : padicValInt p f.num = 0 := padicValInt.eq_zero_of_not_dvd hnotdvd
  rw [padicValRat_def, hvnum]
  have hvden' : (1 : ℤ) ≤ (padicValNat p f.den : ℤ) := by exact_mod_cast hvden
  omega

/-- A prime divisor of the denominator must be 3 under the local nonnegativity
conditions. -/
theorem den_prime_eq_three {f : ℚ} (hf : f ≠ 0)
    (hpos : ∀ p : ℕ, Nat.Prime p → p ≠ 3 → 0 ≤ padicValRat p f)
    {p : ℕ} (hp : Nat.Prime p) (hdvd : p ∣ f.den) : p = 3 := by
  by_contra hp3
  have hneg := padicValRat_neg_of_dvd_den hf hp hdvd
  have hnonneg := hpos p hp hp3
  linarith

/-- The denominator is not divisible by 3 when v_3(f) >= 1. -/
theorem three_not_dvd_den {f : ℚ} (hf : f ≠ 0)
    (hv3 : 1 ≤ padicValRat 3 f) : ¬ 3 ∣ f.den := by
  intro hdvd
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hneg := padicValRat_neg_of_dvd_den hf (by norm_num : Nat.Prime 3) hdvd
  linarith

/-- Under the hypotheses, the denominator of f is 1. -/
theorem den_eq_one {f : ℚ} (hf : f ≠ 0)
    (hpos : ∀ p : ℕ, Nat.Prime p → p ≠ 3 → 0 ≤ padicValRat p f)
    (hv3 : 1 ≤ padicValRat 3 f) : f.den = 1 := by
  rw [Nat.eq_one_iff_not_exists_prime_dvd]
  intro p hp hdvd
  have hp3 : p = 3 := den_prime_eq_three hf hpos hp hdvd
  subst hp3
  exact three_not_dvd_den hf hv3 hdvd

/-- Under the hypotheses, the numerator is divisible by 3. -/
theorem three_dvd_num {f : ℚ} (hv3 : 1 ≤ padicValRat 3 f)
    (hden : f.den = 1) : (3 : ℤ) ∣ f.num := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hvint : 1 ≤ padicValInt 3 f.num := by
    rw [padicValRat_def, hden] at hv3
    simpa using hv3
  have h := (padicValInt_dvd_iff (p := 3) (n := 1) f.num).mpr (Or.inr hvint)
  simpa using h

/-- The actual no-global-linear proposition. -/
theorem no_global_linear_f_actual :
    ¬ ∃ f : ℚ, GlobalLinearCondition f := by
  rintro ⟨f, hf, hpos, hv3, habs⟩
  have hden : f.den = 1 := den_eq_one hf hpos hv3
  have hnumdvd : (3 : ℤ) ∣ f.num := three_dvd_num hv3 hden
  have hnum_ne : f.num ≠ 0 := Rat.num_ne_zero.mpr hf
  obtain ⟨k, hk⟩ := hnumdvd
  have hk_ne : k ≠ 0 := by
    intro hk0
    apply hnum_ne
    rw [hk, hk0]
    norm_num
  have hf_eq_num : f = (f.num : ℚ) := by
    have h := Rat.num_div_den f
    rw [hden] at h
    norm_num at h
    exact h.symm
  have hf_eq : f = ((3 * k : ℤ) : ℚ) := by
    rw [hf_eq_num, hk]
  have habs_ge : (3 : ℝ) ≤ |(f : ℝ)| := by
    rw [hf_eq]
    push_cast
    rw [abs_mul]
    norm_num
    have hkabs : (1 : ℝ) ≤ |(k : ℝ)| := by
      exact_mod_cast Int.one_le_abs hk_ne
    nlinarith [hkabs]
  have habsR : |(f : ℝ)| ≤ 1 := by
    exact_mod_cast habs
  linarith

end ABCBridge.N8.C9LocalGlobalCounterexampleProof
