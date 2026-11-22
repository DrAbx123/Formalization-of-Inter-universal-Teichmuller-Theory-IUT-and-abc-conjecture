import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianIntegralBasis
import Mathlib.RingTheory.DedekindDomain.Basic
import LeanFormal.IUT.Foundations.NumberField.PlaceCompletionCarrier
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction

noncomputable section
set_option maxRecDepth 100000
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace

namespace LeanFormal.IUT.XiFPaper.S2704GaussianPrimeActual

def piPlus : GaussianInt := ⟨44, 15⟩

def piMinus : GaussianInt := ⟨44, -15⟩

theorem S2704_norm_piPlus : Zsqrtd.norm piPlus = 2161 := by
  rw [Zsqrtd.norm_def]
  norm_num [piPlus]

theorem S2704_norm_piMinus : Zsqrtd.norm piMinus = 2161 := by
  rw [Zsqrtd.norm_def]
  norm_num [piMinus]

theorem S2704_natPrime2161 : Nat.Prime 2161 := by
  decide

theorem S2704_irreducible_of_norm
    (x : GaussianInt) (hx : Zsqrtd.norm x = 2161) : Irreducible x := by
  rw [irreducible_iff]
  constructor
  · intro hunit
    have h : (Zsqrtd.norm x).natAbs = 1 :=
      (Zsqrtd.norm_eq_one_iff (d := -1)).mpr hunit
    rw [hx] at h
    norm_num at h
  · intro a b hab
    have hnorm : (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs = 2161 := by
      rw [← Int.natAbs_mul, ← Zsqrtd.norm_mul, ← hab, hx]
      norm_num
    have hdiv : (Zsqrtd.norm a).natAbs ∣ 2161 :=
      ⟨(Zsqrtd.norm b).natAbs, hnorm.symm⟩
    rcases S2704_natPrime2161.eq_one_or_self_of_dvd _ hdiv with h1 | h1
    · left
      exact (Zsqrtd.norm_eq_one_iff (d := -1)).mp h1
    · right
      have hb : (Zsqrtd.norm b).natAbs = 1 := by
        rw [h1] at hnorm
        omega
      exact (Zsqrtd.norm_eq_one_iff (d := -1)).mp hb

theorem S2704_ne_zero_piPlus : piPlus ≠ 0 := by
  intro h
  have := S2704_norm_piPlus
  rw [h, Zsqrtd.norm_zero] at this
  norm_num at this

theorem S2704_ne_zero_piMinus : piMinus ≠ 0 := by
  intro h
  have := S2704_norm_piMinus
  rw [h, Zsqrtd.norm_zero] at this
  norm_num at this

theorem S2704_irreducible_piPlus : Irreducible piPlus :=
  S2704_irreducible_of_norm piPlus S2704_norm_piPlus

theorem S2704_irreducible_piMinus : Irreducible piMinus :=
  S2704_irreducible_of_norm piMinus S2704_norm_piMinus

theorem S2704_prime_piPlus : Prime piPlus :=
  (irreducible_iff_prime).mp S2704_irreducible_piPlus

theorem S2704_prime_piMinus : Prime piMinus :=
  (irreducible_iff_prime).mp S2704_irreducible_piMinus

theorem S2704_span_piPlus_isPrime : (Ideal.span {piPlus}).IsPrime :=
  (Ideal.span_singleton_prime S2704_ne_zero_piPlus).mpr S2704_prime_piPlus

theorem S2704_span_piMinus_isPrime : (Ideal.span {piMinus}).IsPrime :=
  (Ideal.span_singleton_prime S2704_ne_zero_piMinus).mpr S2704_prime_piMinus

theorem S2704_span_piPlus_isMaximal : (Ideal.span {piPlus}).IsMaximal :=
  Ideal.IsPrime.isMaximal S2704_span_piPlus_isPrime (by
    simpa [Ideal.span_singleton_eq_bot] using S2704_ne_zero_piPlus)

theorem S2704_span_piMinus_isMaximal : (Ideal.span {piMinus}).IsMaximal :=
  Ideal.IsPrime.isMaximal S2704_span_piMinus_isPrime (by
    simpa [Ideal.span_singleton_eq_bot] using S2704_ne_zero_piMinus)

theorem S2704_val_lt_one_of_mem_maximalIdeal
    {K : Type*} [Field K] [NumberField K]
    (p : NumberField.FinitePlace K)
    (π : NumberField.RingOfIntegers K) (h : π ∈ p.maximalIdeal.asIdeal) :
    Valued.v ((algebraMap (NumberField.RingOfIntegers K)
      (NumberFieldFinitePlace.CompletionIntegers p) π :
        NumberFieldFinitePlace.CompletionIntegers p) :
          NumberFieldFinitePlace.Completion p) < 1 := by
  rw [NumberFieldFinitePlace.valued_algebraMap_completionIntegers]
  exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := K)
    (v := p.maximalIdeal) π).mpr h

theorem S2704_residueCharacteristic_of_comap
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (p : NumberField.FinitePlace K)
    (q : NumberField.FinitePlace ℚ)
    (hp : comap (k := ℚ) p = q) :
    residueCharacteristic p = residueCharacteristic q := by
  rw [← NumberFieldFinitePlace.residueCharacteristic_comap (k := ℚ) (place := p), hp]

#check S2704_norm_piPlus
#check S2704_norm_piMinus
#check S2704_natPrime2161
#check S2704_span_piPlus_isPrime
#check S2704_span_piMinus_isPrime
#check S2704_span_piPlus_isMaximal
#check S2704_span_piMinus_isMaximal
#check S2704_val_lt_one_of_mem_maximalIdeal
#check S2704_residueCharacteristic_of_comap
#print axioms S2704_span_piPlus_isMaximal
#print axioms S2704_span_piMinus_isMaximal
#print axioms S2704_val_lt_one_of_mem_maximalIdeal

end LeanFormal.IUT.XiFPaper.S2704GaussianPrimeActual
end
