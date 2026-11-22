/- Route 7.2: Serre's wild different bound gives the local different order bound without the
base paperOrder case.  Donor: ported LANA SerreBound (DONE 23:34:50) via david lane's
Mzk1ULSerreWildBoundActual.serre_differentExponent_lt (read-only import). -/
import tmp.sheaf.xif.paper.lana.iut.Iut.Tower.SerreBound
import tmp.sheaf.xif.paper.Mzk1G1F7DifferentExponentBoundsActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralTraceDualTensorInclusion
import LeanFormal.IUT.Foundations.LocalFields.LocalDifferentUpperBound
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellRamificationInertia
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.Tactic
noncomputable section
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
namespace LeanFormal.IUT.XiFPaper.Mzk1G1UniversalSerreDeltaBoundActual

open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.IntegralTraceDualTensorInclusion
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalDifferentUpperBound
open UniqueFactorizationMonoid

/-- count-pow bridge (ported from david lane, donor: lana SerreBound): if P^N does not divide
I then the different exponent at P is smaller than N. -/
theorem count_lt_of_not_pow_dvd'
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {I : Ideal R} (hI : I ≠ ⊥) (P : Ideal R) [P.IsPrime] (hP0 : P ≠ ⊥) {N : Nat}
    (h : ¬ P ^ N ∣ I) : (normalizedFactors I).count P < N := by
  by_contra hc
  push_neg at hc
  have hdiv : P ^ N ∣ I := by
    rw [UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero _ hP0) hI]
    rw [normalizedFactors_pow, normalizedFactors_irreducible
      ((Ideal.prime_of_isPrime hP0 inferInstance).irreducible), normalize_eq,
      Multiset.nsmul_singleton, ← Multiset.le_count_iff_replicate_le]
    exact hc
  exact h hdiv

/-- Serre wild bound in count form (ported from david lane). -/
theorem serre_differentExponent_lt'
    {A B : Type*} [CommRing A] [CommRing B]
    [IsDedekindDomain A] [IsDedekindDomain B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra (FractionRing A) (FractionRing B)]
    (hsep : Algebra.IsSeparable (FractionRing A) (FractionRing B))
    (𝔭 : Ideal A) [𝔭.IsMaximal] [Finite (A ⧸ 𝔭)] (𝔓 : Ideal B) [𝔓.IsMaximal] [𝔓.LiesOver 𝔭]
    (h𝔭 : 𝔭 ≠ ⊥) (κ : Nat)
    (hκ : ((𝔭.ramificationIdx' 𝔓 : Nat) : A) ∉ 𝔭 ^ (κ + 1)) :
    (normalizedFactors (differentIdeal A B)).count 𝔓 <
      𝔭.ramificationIdx' 𝔓 * (κ + 1) := by
  letI : Algebra (FractionRing A) (FractionRing B) := FractionRing.liftAlgebra A B
  letI : IsScalarTower A (FractionRing A) (FractionRing B) :=
    FractionRing.isScalarTower_liftAlgebra
  haveI hsepI : Algebra.IsSeparable (FractionRing A) (FractionRing B) := hsep
  have hI : differentIdeal A B ≠ ⊥ := differentIdeal_ne_bot (A := A) (B := B)
  have hP0 : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭 𝔓
  exact count_lt_of_not_pow_dvd' hI 𝔓 hP0
    (Iut.Serre.not_pow_dvd_differentIdeal (A := A) (B := B) 𝔭 𝔓 h𝔭 κ hκ)

variable {p : Nat} [Fact p.Prime]
variable {L : Type*} [NormedField L] [CharZero L] [CompleteSpace L] [IsUltrametricDist L]
  [ProperSpace L] [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
local instance : IsScalarTower ℤ_[p] ℚ_[p] L :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)
local instance : Algebra (FractionRing ℤ_[p]) (FractionRing (Integers L)) :=
  FractionRing.liftAlgebra ℤ_[p] (FractionRing (Integers L))

/-- The cast of the ramification exponent is not in the (kappa+1)-st power of (p). -/
theorem ramificationIdx_cast_not_mem_pow (e : ℕ) (κ : ℕ) (hκ : κ = padicValNat p e + 1)
    (he : e ≠ 0) :
    ((e : ℕ) : ℤ_[p]) ∉ (Ideal.span {(p : ℤ_[p])} : Ideal ℤ_[p]) ^ (κ + 1) := by
  subst hκ
  intro hmem
  have hspan : (Ideal.span {(p : ℤ_[p])} : Ideal ℤ_[p]) ^ (padicValNat p e + 2) =
      Ideal.span {((p : ℤ_[p]) ^ (padicValNat p e + 2))} := by
    rw [Ideal.span_singleton_pow]
  rw [hspan, PadicInt.mem_span_pow_iff_le_valuation _ (Nat.cast_ne_zero.mpr he)] at hmem
  have hval : PadicInt.valuation ((e : ℕ) : ℤ_[p]) = padicValNat p e := by
    change (((e : ℕ) : ℚ_[p]).valuation).toNat = padicValNat p e
    rw [Padic.valuation_natCast]
    exact Int.toNat_natCast (padicValNat p e)
  rw [hval] at hmem
  omega

/-- Serre bound in localDifferentOrder form. -/
theorem localDifferentOrder_lt_logShell_mul :
    localDifferentOrder (p := p) (L := L) <
      logShellRamificationExponent (K := L) (p := p) *
        (padicValNat p (logShellRamificationExponent (K := L) (p := p)) + 2) := by
  letI : IsIntegrallyClosed ℤ_[p] := padicInt_isIntegrallyClosed (p := p)
  letI : IsDedekindDomain ℤ_[p] := by infer_instance
  letI : IsDedekindDomain (Integers L) := integersIsDedekindDomain (p := p) (L := L)
  letI : IsDiscreteValuationRing (Integers L) := integersIsDiscreteValuationRing (p := p) (L := L)
  letI : Module.IsTorsionFree ℤ_[p] (Integers L) := integersIsTorsionFree (p := p) (L := L)
  letI : Module.Finite ℤ_[p] (Integers L) := integersModuleFinite (p := p) (L := L)
  letI : Finite (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) := inferInstance
  letI : (IsLocalRing.maximalIdeal (Integers L)).LiesOver (IsLocalRing.maximalIdeal ℤ_[p]) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap ℤ_[p] (Integers L))).symm⟩
  let e := (IsLocalRing.maximalIdeal ℤ_[p]).ramificationIdx' (IsLocalRing.maximalIdeal (Integers L))
  let κ := padicValNat p e + 1
  have h𝔭 : IsLocalRing.maximalIdeal ℤ_[p] ≠ ⊥ := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.span_singleton_eq_bot.not.mpr (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have he : e ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver
      (S := Integers L) (R := ℤ_[p]) (P := IsLocalRing.maximalIdeal (Integers L))
      (p := IsLocalRing.maximalIdeal ℤ_[p]) h𝔭
  have hκ : ((e : ℕ) : ℤ_[p]) ∉ (IsLocalRing.maximalIdeal ℤ_[p]) ^ (κ + 1) := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact ramificationIdx_cast_not_mem_pow (p := p) e κ rfl he
  haveI hsepL : Algebra.IsSeparable ℚ_[p] L := inferInstance
  haveI hsepFrac : Algebra.IsSeparable (FractionRing ℤ_[p]) (FractionRing (Integers L)) := by
    refine Algebra.IsSeparable.of_equiv_equiv
      (FractionRing.algEquiv ℤ_[p] ℚ_[p]).symm.toRingEquiv
      (FractionRing.algEquiv (Integers L) L).symm.toRingEquiv ?_
    ext x
    exact IsFractionRing.algEquiv_commutes
      (FractionRing.algEquiv ℤ_[p] ℚ_[p]).symm
      (FractionRing.algEquiv (Integers L) L).symm x
  have hserre := serre_differentExponent_lt' (A := ℤ_[p]) (B := Integers L) hsepFrac
    (IsLocalRing.maximalIdeal ℤ_[p]) (IsLocalRing.maximalIdeal (Integers L))
    h𝔭 κ hκ
  have hcount : (normalizedFactors (differentIdeal ℤ_[p] (Integers L))).count
      (IsLocalRing.maximalIdeal (Integers L)) =
      localDifferentOrder (p := p) (L := L) := by
    symm
    exact localDifferentOrder_eq_factorCount (p := p) (K := L)
  have hlog : logShellRamificationExponent (K := L) (p := p) = e := by
    rw [logShellRamificationExponent_eq_ramificationIdx (K := L) (p := p)]
  rw [hcount] at hserre
  simpa [hlog, κ] using hserre

#print axioms localDifferentOrder_lt_logShell_mul
end LeanFormal.IUT.XiFPaper.Mzk1G1UniversalSerreDeltaBoundActual
