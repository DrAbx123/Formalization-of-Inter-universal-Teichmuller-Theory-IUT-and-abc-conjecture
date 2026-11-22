/- Route 8.5 F7 (part 1; recompiled after watchdog restart): the different exponent of an unramified prime is zero, and the
Mathlib lower bound P^(e-1) | differentIdeal is recorded for the tame case. -/
import tmp.sheaf.xif.paper.Mzk1G1RelativeDifferentLogActual
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F7DifferentExponentBoundsActual

open NumberField
open UniqueFactorizationMonoid
open LeanFormal.IUT.XiFPaper.Mzk1G1RelativeDifferentLogActual

universe u

section

variable {K : Type u} [Field K] [NumberField K]
variable {L : Type u} [Field L] [NumberField L] [Algebra K L]
variable [Module.Finite (𝓞 K) (𝓞 L)]

/-- At an unramified prime P, the different exponent delta(P) is zero (Mathlib:
P divides differentIdeal iff P is ramified). -/
theorem differentExponent_eq_zero_of_unramified (P : Ideal (𝓞 L)) [P.IsPrime]
    (hunr : Algebra.IsUnramifiedAt (𝓞 K) P) :
    differentExponent (K := K) (L := L) P = 0 := by
  have hI : differentIdeal (𝓞 K) (𝓞 L) ≠ ⊥ := differentIdeal_ne_bot
  have hnotdvd : ¬ P ∣ differentIdeal (𝓞 K) (𝓞 L) := by
    intro hdvd
    exact (dvd_differentIdeal_iff.mp hdvd) hunr
  rw [differentExponent, Multiset.count_eq_zero]
  intro hmem
  have hle : differentIdeal (𝓞 K) (𝓞 L) ≤ P := ((Ideal.mem_normalizedFactors_iff hI).mp hmem).2
  exact hnotdvd (Ideal.dvd_iff_le.mpr hle)

/-- Mathlib lower bound in the tame/ramified direction: if P^e divides the extended prime
p = P.under, then P^(e-1) divides the relative different, hence delta(P) >= e-1. -/
theorem pow_sub_one_dvd_differentIdeal_under (P : Ideal (𝓞 L)) [P.IsPrime] {e : Nat}
    (he : e ≠ 0) (hp : P.under (𝓞 K) ≠ ⊥)
    (hP : P ^ e ∣ (P.under (𝓞 K)).map (algebraMap (𝓞 K) (𝓞 L))) :
    P ^ (e - 1) ∣ differentIdeal (𝓞 K) (𝓞 L) := by
  have hpmax : (P.under (𝓞 K)).IsMaximal :=
    Ideal.isMaximal_of_isPrime_of_ne_bot _ hp
  haveI : (P.under (𝓞 K)).IsMaximal := hpmax
  exact pow_sub_one_dvd_differentIdeal (A := 𝓞 K) (B := 𝓞 L) P e hp hP

/-- Count form (kurt recipe): if P^(e-1) divides the relative different, then the different
exponent is at least e-1. -/
theorem count_differentIdeal_ge_ramification_sub_one (P : Ideal (𝓞 L)) [P.IsPrime]
    (hP : P ≠ ⊥) {e : Nat} (h : P ^ (e - 1) ∣ differentIdeal (𝓞 K) (𝓞 L)) :
    e - 1 ≤ differentExponent (K := K) (L := L) P := by
  have hI : differentIdeal (𝓞 K) (𝓞 L) ≠ ⊥ := differentIdeal_ne_bot
  have hle : differentIdeal (𝓞 K) (𝓞 L) ≤ P ^ (e - 1) := Ideal.dvd_iff_le.mp h
  have hcount := Ideal.count_le_of_ideal_ge hle hI P
  have hprime : Prime P := Ideal.prime_of_isPrime hP ‹P.IsPrime›
  have hnf : normalizedFactors (P ^ (e - 1)) =
      Multiset.replicate (e - 1) (normalize P) :=
    hprime.irreducible.normalizedFactors_pow (e - 1)
  have hnorm : normalize P = P := normalize_eq P
  rw [hnf, hnorm, Multiset.count_replicate_self] at hcount
  exact hcount

/-- Tame lower bound in the form used by route 8.5: if P^e divides the extended base prime,
then delta(P) >= e - 1. -/
theorem differentExponent_ge_ramification_sub_one (P : Ideal (𝓞 L)) [P.IsPrime]
    (hP : P ≠ ⊥) {e : Nat} (he : e ≠ 0) (hp : P.under (𝓞 K) ≠ ⊥)
    (hPmap : P ^ e ∣ (P.under (𝓞 K)).map (algebraMap (𝓞 K) (𝓞 L))) :
    e - 1 ≤ differentExponent (K := K) (L := L) P :=
  count_differentIdeal_ge_ramification_sub_one P hP
    (pow_sub_one_dvd_differentIdeal_under P he hp hPmap)

end

section CountEquality

variable {R : Type u} [CommRing R] [IsDedekindDomain R]

/-- If P^m divides I but P^(m+1) does not, then the multiplicity of P in the normalized
factorization of I is exactly m. -/
theorem count_eq_of_pow_dvd_not_pow_succ_dvd {I : Ideal R} (hI : I ≠ ⊥)
    (P : Ideal R) [P.IsPrime] (hP : P ≠ ⊥) {m : Nat}
    (hdvd : P ^ m ∣ I) (hnot : ¬ P ^ (m + 1) ∣ I) :
    (normalizedFactors I).count P = m := by
  classical
  apply le_antisymm ?_ ?_
  · by_contra hle
    have hlt : m < (normalizedFactors I).count P := lt_of_not_ge hle
    have hcount : m + 1 ≤ (normalizedFactors I).count P := Nat.succ_le_of_lt hlt
    have hprime : Prime P := Ideal.prime_of_isPrime hP ‹P.IsPrime›
    have hnf : normalizedFactors (P ^ (m + 1)) =
        Multiset.replicate (m + 1) (normalize P) :=
      hprime.irreducible.normalizedFactors_pow (m + 1)
    have hnorm : normalize P = P := normalize_eq P
    have hle2 : normalizedFactors (P ^ (m + 1)) ≤ normalizedFactors I := by
      rw [hnf, hnorm, Multiset.le_iff_count]
      intro a
      by_cases ha : a = P
      · subst ha
        rw [Multiset.count_replicate_self]
        exact hcount
      · rw [Multiset.count_replicate, if_neg (Ne.symm ha)]
        exact Nat.zero_le _
    have hpow_ne : P ^ (m + 1) ≠ ⊥ := pow_ne_zero _ hP
    exact hnot ((dvd_iff_normalizedFactors_le_normalizedFactors hpow_ne hI).mpr hle2)
  · have hle : I ≤ P ^ m := Ideal.dvd_iff_le.mp hdvd
    have hcount := Ideal.count_le_of_ideal_ge hle hI P
    have hprime : Prime P := Ideal.prime_of_isPrime hP ‹P.IsPrime›
    have hnf : normalizedFactors (P ^ m) = Multiset.replicate m (normalize P) :=
      hprime.irreducible.normalizedFactors_pow m
    have hnorm : normalize P = P := normalize_eq P
    rw [hnf, hnorm, Multiset.count_replicate_self] at hcount
    exact hcount

end CountEquality

#print axioms differentExponent_eq_zero_of_unramified
#print axioms pow_sub_one_dvd_differentIdeal_under
#print axioms count_differentIdeal_ge_ramification_sub_one
#print axioms differentExponent_ge_ramification_sub_one
#print axioms count_eq_of_pow_dvd_not_pow_succ_dvd
end LeanFormal.IUT.XiFPaper.Mzk1G1F7DifferentExponentBoundsActual
