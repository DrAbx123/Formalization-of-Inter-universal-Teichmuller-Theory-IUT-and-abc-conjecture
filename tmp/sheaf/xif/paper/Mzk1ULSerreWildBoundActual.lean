/- Serre wild different bound 消费（ported LANA SerreBound DONE 23:34:50）:
  Iut.Serre.not_pow_dvd_differentIdeal: e=e(𝔓/𝔭), e ∉ 𝔭^(κ+1) ⇒ 𝔓^(e(κ+1)) ∤ differentIdeal A B。
  本文件给出 count 形式: (normalizedFactors (differentIdeal A B)).count 𝔓 < e(κ+1)，
  供 hlogK 的 Prop1.3(ii) wild 部分（log N(diff) ≤ log f_F + 2log l 的 wild 常数吸收）使用。
  donor: tmp/sheaf/xif/paper/lana/iut/Iut/Tower/SerreBound.lean:251; 改法: 原文件为序列化 port，
  这里只加 count 桥（Mathlib Dedekind normalizedFactors）与不同指数命名。 -/
import tmp.sheaf.xif.paper.lana.iut.Iut.Tower.SerreBound
import tmp.sheaf.xif.paper.Mzk1G1F7DifferentExponentBoundsActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
namespace LeanFormal.IUT.XiFPaper.Mzk1ULSerreWildBoundActual

open UniqueFactorizationMonoid

universe u

/-- count-pow 桥: ¬ P^N ∣ I ⇒ count ≤ N−1（I≠⊥, P 素非零）。 -/
theorem count_lt_of_not_pow_dvd
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {I : Ideal R} (hI : I ≠ ⊥) (P : Ideal R) [P.IsPrime] (hP0 : P ≠ ⊥) {N : ℕ}
    (h : ¬ P ^ N ∣ I) :
    (normalizedFactors I).count P < N := by
  by_contra hc
  push_neg at hc
  have hdiv : P ^ N ∣ I := by
    rw [UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero _ hP0) hI]
    rw [normalizedFactors_pow, normalizedFactors_irreducible
      ((Ideal.prime_of_isPrime hP0 inferInstance).irreducible), normalize_eq,
      Multiset.nsmul_singleton, ← Multiset.le_count_iff_replicate_le]
    exact hc
  exact h hdiv

/-- 由「𝔓^(e(κ+1)) 不整除 relative different」直接得 count 上界（Serre 定理的 count 形式，
    不依赖 FractionRing 的可分性实例；那一步由调用方给 hnot）。 -/
theorem differentExponent_lt_of_not_pow_dvd
    {A B : Type u} [CommRing A] [CommRing B]
    [IsDedekindDomain A] [IsDedekindDomain B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    (𝔭 : Ideal A) [𝔭.IsMaximal] (𝔓 : Ideal B) [𝔓.IsMaximal] [𝔓.LiesOver 𝔭]
    (h𝔭 : 𝔭 ≠ ⊥) (κ : ℕ) (hI : differentIdeal A B ≠ ⊥)
    (hnot : ¬ 𝔓 ^ (𝔭.ramificationIdx' 𝔓 * (κ + 1)) ∣ differentIdeal A B) :
    (normalizedFactors (differentIdeal A B)).count 𝔓 <
      𝔭.ramificationIdx' 𝔓 * (κ + 1) := by
  have hP0 : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭 𝔓
  exact count_lt_of_not_pow_dvd hI 𝔓 hP0 hnot

#print axioms count_lt_of_not_pow_dvd
#print axioms differentExponent_lt_of_not_pow_dvd

end LeanFormal.IUT.XiFPaper.Mzk1ULSerreWildBoundActual