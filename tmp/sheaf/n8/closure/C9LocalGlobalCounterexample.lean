import Mathlib

/-!
# C9 local-global counterexample, stage 1

Standard arithmetic model, F = Q, p = 3:

  L_3 = 3 Z_3,   H_3 = 9 Z_3,
  L_p = H_p = Z_p  (p != 3),   L_inf = H_inf = [-1,1].

Relative log-volumes of the standard unit lattices are normalized to 0, so
Q = nu(L) = -log 3 and h = nu(H) = -2 log 3 < Q.

There are local linear isomorphisms L_v -> H_v (multiplication by 3 at 3,
identity elsewhere), but no global linear effective morphism L -> H.  A global
linear morphism would come from f in Q^*, integral at all finite p != 3,
lying in 3 Z_3, and with |f| <= 1 at the infinite place; no nonzero such f
exists.

This is the stage-1 statement package.  The exact non-existence proposition is
the named sorry; easy numeric/local lemmas are proved.
-/

noncomputable section

namespace ABCBridge.N8.C9LocalGlobalCounterexample

open scoped Real

/-- The local lattice L_3 = 3 Z_3, represented at the finite level by 3 Z. -/
def L3 : Ideal ℤ := Ideal.span ({3} : Set ℤ)

/-- The local lattice H_3 = 9 Z_3, represented at the finite level by 9 Z. -/
def H3 : Ideal ℤ := Ideal.span ({9} : Set ℤ)

/-- Multiplication by 3 at p = 3 maps L_3 to H_3; this is the local linear
isomorphism at the only nontrivial finite place. -/
theorem localIso_at_three : L3 * L3 = H3 := by
  unfold L3 H3
  rw [Ideal.span_singleton_mul_span_singleton]
  norm_num

/-- Elsewhere (all finite p != 3 and the infinite place) the local lattices are
equal; this records the exact data shape, not a global morphism. -/
def elsewhereEqual : Prop := True

/-- Normalized relative log-volume of L: Q = -log 3. -/
def Q0 : ℝ := -Real.log 3

/-- Normalized relative log-volume of H: h = -2 log 3. -/
def h0 : ℝ := -2 * Real.log 3

/-- The counterexample has h < Q. -/
theorem h0_lt_Q0 : h0 < Q0 := by
  have hlog : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  unfold h0 Q0
  linarith

/-- The local comparison data of the counterexample: L3, H3, and the local
multiplier 3 at p = 3. -/
structure LocalLinearComparisonData where
  L : Ideal ℤ := L3
  H : Ideal ℤ := H3
  /-- Local multiplier at p = 3. -/
  multiplier3 : ℚ := 3
  multiplier3_ne_zero : multiplier3 ≠ 0 := by norm_num

/-- The actual local comparison data. -/
def localLinearComparisonData : LocalLinearComparisonData where
  L := L3
  H := H3
  multiplier3 := 3
  multiplier3_ne_zero := by norm_num

/-- Global linear condition for f in Q^*: integral at every finite p != 3,
lying in 3 Z_3, and bounded by 1 at the infinite place. -/
def GlobalLinearCondition (f : ℚ) : Prop :=
  f ≠ 0 ∧
    (∀ p : ℕ, Nat.Prime p → p ≠ 3 → 0 ≤ padicValRat p f) ∧
    1 ≤ padicValRat 3 f ∧
    |f| ≤ 1

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
theorem no_global_linear_f :
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

/-- A Frobenius-degree-two global morphism L -> H does exist (L^(tensor 2) =
H); this only shows 2 Q0 <= h0 and does not give the linear inequality. -/
theorem frobenius_two_local : L3 * L3 = H3 := localIso_at_three

end ABCBridge.N8.C9LocalGlobalCounterexample
