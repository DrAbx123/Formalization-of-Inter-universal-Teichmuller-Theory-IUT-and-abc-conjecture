/- H-T §8.2: 绝对 δ-sum 全局化（rootDiscr = (1/finrank)·Σ δ_P log|N(P)|）与
绝对 inertiaDeg 恒等 log|N(P)| = f_P·log p（base ℤ）。

donors:
* IUT.ABCBridge.Arithmetic.RationalDifferent.log_absNorm_differentIdeal_div_finrank_eq_log_rootDiscr;
* Mathlib Ideal.absNorm (MonoidWithZeroHom) + prod_normalizedFactors_eq_self;
* Mathlib Ideal.natAbs_pow_inertiaDeg (base ℤ 的 absNorm = p^f)。 -/
import Mathlib.Tactic
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalDifferent

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1HT82AbsDifferentSumActual

open NumberField UniqueFactorizationMonoid
open scoped BigOperators

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- differentIdeal ℤ (𝓞 K) 的 normalizedFactors 支撑。 -/
noncomputable def differentPlaces : Finset (Ideal (𝓞 K)) :=
  (normalizedFactors (differentIdeal ℤ (𝓞 K))).toFinset

/-- absNorm(differentIdeal ℤ 𝓞_K) = ∏_{P∈s} absNorm P ^ count P
（absNorm 乘性 + normalizedFactors 归一分解）。 -/
theorem absNorm_differentIdeal_eq_prod (hI : differentIdeal ℤ (𝓞 K) ≠ ⊥) :
    Ideal.absNorm (differentIdeal ℤ (𝓞 K)) =
      ∏ P ∈ differentPlaces K,
        (Ideal.absNorm P) ^ (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P := by
  classical
  have hprod : (normalizedFactors (differentIdeal ℤ (𝓞 K))).prod = differentIdeal ℤ (𝓞 K) :=
    prod_normalizedFactors_eq_self hI
  calc Ideal.absNorm (differentIdeal ℤ (𝓞 K))
      = Ideal.absNorm ((normalizedFactors (differentIdeal ℤ (𝓞 K))).prod) := by rw [hprod]
    _ = ((normalizedFactors (differentIdeal ℤ (𝓞 K))).map Ideal.absNorm).prod := by
          rw [map_multiset_prod]
    _ = ∏ P ∈ differentPlaces K,
          (Ideal.absNorm P) ^ (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P := by
          rw [differentPlaces, Finset.prod_multiset_map_count]

/-- log|N(differentIdeal ℤ 𝓞_K)| = Σ_{P∈s} δ_P · log|N(P)|。 -/
theorem log_absNorm_differentIdeal_eq_delta_sum (hI : differentIdeal ℤ (𝓞 K) ≠ ⊥) :
    Real.log ((Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℕ) : ℝ) =
      ∑ P ∈ differentPlaces K,
        ((normalizedFactors (differentIdeal ℤ (𝓞 K))).count P : ℝ) *
          Real.log ((Ideal.absNorm P : ℕ) : ℝ) := by
  classical
  have hs : ∀ P ∈ differentPlaces K, ((Ideal.absNorm P : ℕ) : ℝ) ≠ 0 := by
    intro P hP
    have hmem : P ∈ normalizedFactors (differentIdeal ℤ (𝓞 K)) :=
      Multiset.mem_toFinset.mp hP
    have hprime : P.IsPrime := ((Ideal.mem_normalizedFactors_iff hI).mp hmem).1
    have hPne : P ≠ ⊥ := by
      intro hbot
      have hle : differentIdeal ℤ (𝓞 K) ≤ P := ((Ideal.mem_normalizedFactors_iff hI).mp hmem).2
      rw [hbot] at hle
      exact hI (le_bot_iff.mp hle)
    have hne : Ideal.absNorm P ≠ 0 := fun h0 => hPne (Ideal.absNorm_eq_zero_iff.mp h0)
    exact Nat.cast_ne_zero.mpr hne
  rw [absNorm_differentIdeal_eq_prod K hI]
  push_cast
  rw [Real.log_prod]
  · apply Finset.sum_congr rfl
    intro P hP
    rw [Real.log_pow]
  · intro P hP
    exact pow_ne_zero _ (hs P hP)

/-- **绝对 δ-sum 全局化**: log rootDiscr K = (1/finrank ℚ K)·Σ δ_P log|N(P)|。 -/
theorem log_rootDiscr_eq_delta_sum :
    Real.log (NumberField.rootDiscr K) =
      (1 / (Module.finrank ℚ K : ℝ)) *
        ∑ P ∈ differentPlaces K,
          ((normalizedFactors (differentIdeal ℤ (𝓞 K))).count P : ℝ) *
            Real.log ((Ideal.absNorm P : ℕ) : ℝ) := by
  have hD := IUT.ABCBridge.Arithmetic.RationalDifferent.log_absNorm_differentIdeal_div_finrank_eq_log_rootDiscr K
  have hI : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
  have hlog := log_absNorm_differentIdeal_eq_delta_sum K hI
  rw [← hD]
  rw [hlog]
  field_simp

/-- **绝对 inertiaDeg 恒等**（base ℤ）: log|N(P)| = f_P · log p,
其中 P 是 𝒪_K 的素理想、LiesOver span {p}（p : ℤ）。 -/
theorem log_absNorm_eq_inertiaDeg_mul_log_natAbs
    {P : Ideal (𝓞 K)} [hP : P.IsPrime] {p : ℤ} [P.LiesOver (Ideal.span {p})] :
    Real.log ((Ideal.absNorm P : ℕ) : ℝ) =
      (P.inertiaDeg ℤ : ℝ) * Real.log (p.natAbs : ℝ) := by
  have h := Ideal.natAbs_pow_inertiaDeg (R := 𝓞 K) p P
  rw [← h]
  push_cast
  rw [Real.log_pow]

#print axioms absNorm_differentIdeal_eq_prod
#print axioms log_absNorm_differentIdeal_eq_delta_sum
#print axioms log_rootDiscr_eq_delta_sum
#print axioms log_absNorm_eq_inertiaDeg_mul_log_natAbs

end LeanFormal.IUT.XiFPaper.Mzk1HT82AbsDifferentSumActual