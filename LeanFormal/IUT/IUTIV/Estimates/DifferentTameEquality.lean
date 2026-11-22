/-
# Tame ramification: the exact different exponent `e - 1`

Equality case of IUT IV Prop 1.3 (i) (L579–583: "with equality if `k_i/k_0` is tamely
ramified").  For a Dedekind extension `B / A`, a nonzero maximal `p` of `A` and a nonzero prime
`P` of `B` over `p` with ramification index `e`, if `e` is invertible in `A ⧸ p` and
`B ⧸ P` is separable over `A ⧸ p` (tame ramification at `P`), then `P ^ e ∤ 𝔇_{B/A}`; with
Dedekind's bound this gives `ord_P 𝔇_{B/A} = e - 1`.

Route: the separable residue field `B ⧸ P` is formally étale over `A ⧸ p`, so it lifts into
the Artinian ring `B ⧸ P^e` (nilpotent kernel); trace transitivity gives
`Tr_{(B/P^e)/(A/p)} (φ z) = e · Tr_{(B/P)/(A/p)} z`, which is nonzero for a suitable `z`.
Mathlib's `not_dvd_differentIdeal_of_intTrace_not_mem`, applied to the ideal `P ^ e` and its
coprime cofactor in `p B`, concludes.
-/

import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Trace.Quotient
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Basic
import LeanFormal.IUT.IUTIV.Estimates.DifferentTowerEstimate

open Module Ideal UniqueFactorizationMonoid

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace LeanFormal.IUT.IUTIV.Estimates

/-- **Trace through a nilpotent thickening of a separable field.**  Let `R` be a finite
`k`-algebra with a surjection `g : R → C` onto a separable field extension `C / k` whose
kernel is nilpotent.  If `[R : k] = e · [C : k]` with `e ≠ 0` in `k`, some element of `R`
has nonzero trace. -/
theorem exists_trace_ne_zero_of_nilpotent_ker {k R C : Type*} [Field k] [CommRing R] [Field C]
    [Algebra k R] [Algebra k C] [Module.Finite k R] [Algebra.IsSeparable k C]
    (g : R →ₐ[k] C) (hg : Function.Surjective g)
    (hker : IsNilpotent (RingHom.ker (g : R →+* C)))
    (e : ℕ) (he : finrank k R = e * finrank k C) (he0 : (e : k) ≠ 0) :
    ∃ x : R, Algebra.trace k R x ≠ 0 := by
  haveI : Module.Finite k C := Module.Finite.of_surjective g.toLinearMap hg
  haveI : Algebra.FormallyEtale k C := Algebra.FormallyEtale.of_isSeparable k C
  let φ : C →ₐ[k] R :=
    Algebra.FormallySmooth.liftOfSurjective (AlgHom.id k C) g hg hker
  letI : Algebra C R := φ.toRingHom.toAlgebra
  haveI : IsScalarTower k C R := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  haveI : Module.Finite C R := Module.Finite.of_restrictScalars_finite k C R
  have hfC : 0 < finrank k C := Module.finrank_pos
  have hrank : finrank C R = e := by
    have := Module.finrank_mul_finrank k C R
    rw [he] at this
    have h2 : finrank k C * finrank C R = finrank k C * e := by rw [this]; ring
    exact Nat.eq_of_mul_eq_mul_left hfC h2
  obtain ⟨z, hz⟩ : ∃ z : C, Algebra.trace k C z ≠ 0 := by
    simpa [LinearMap.ext_iff] using Algebra.trace_ne_zero k C
  refine ⟨algebraMap C R z, ?_⟩
  rw [← Algebra.trace_trace (S := C), Algebra.trace_algebraMap, hrank, map_nsmul,
    nsmul_eq_mul]
  exact mul_ne_zero he0 hz


section Dedekind

variable {A B : Type*} [CommRing A] [CommRing B] [IsDedekindDomain A] [IsDedekindDomain B]
  [Algebra A B] [Module.Finite A B] [IsTorsionFree A B]
  [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

/-- **Tame ramification bounds the different exponent from above.**  If `P` lies over `p`
with ramification index `e`, `e ≠ 0` in `A ⧸ p` and `B ⧸ P` separable over `A ⧸ p`, then
`P ^ e ∤ 𝔇_{B/A}`. -/
theorem not_pow_ramificationIdx'_dvd_differentIdeal_of_tame
    {p : Ideal A} [p.IsMaximal] (hp : p ≠ ⊥) (P : Ideal B) [P.IsMaximal] [P.LiesOver p]
    (hP : P ≠ ⊥) [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    (he : ((ramificationIdx' p P : ℕ) : A ⧸ p) ≠ 0) :
    ¬ P ^ ramificationIdx' p P ∣ differentIdeal A B := by
  classical
  set e := ramificationIdx' p P with he_def
  have hmap0 : p.map (algebraMap A B) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hp
  have hPirr : Irreducible P := (Ideal.prime_of_isPrime hP inferInstance).irreducible
  have he0 : e ≠ 0 := fun h => he (by rw [h, Nat.cast_zero])
  obtain ⟨Q, hQ⟩ : P ^ e ∣ p.map (algebraMap A B) :=
    Ideal.dvd_iff_le.mpr Ideal.le_pow_ramificationIdx'
  have hQP : ¬ Q ≤ P := by
    intro h
    have hdvd : P ^ (e + 1) ∣ p.map (algebraMap A B) := by
      rw [hQ, pow_succ]
      exact mul_dvd_mul_left _ (Ideal.dvd_iff_le.mpr h)
    have hle := (pow_dvd_iff_le_emultiplicity).mp hdvd
    rw [emultiplicity_eq_count_normalizedFactors hPirr hmap0, normalize_eq,
      ← Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmap0 inferInstance hP]
      at hle
    have : e + 1 ≤ e := by exact_mod_cast hle
    omega
  have hcopP : IsCoprime P Q := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    exact hQP ((‹P.IsMaximal›.eq_of_le hne le_sup_left).symm ▸ le_sup_right)
  have hcop : IsCoprime (P ^ e) Q := hcopP.pow_left
  -- the residue trace through the nilpotent thickening `B ⧸ P ^ e → B ⧸ P`
  have hPeP : P ^ e ≤ P := Ideal.pow_le_self he0
  letI : Algebra (A ⧸ p) (B ⧸ P ^ e) := Ideal.Quotient.algebraQuotientPowRamificationIdx p P
  let g : (B ⧸ P ^ e) →ₐ[A ⧸ p] (B ⧸ P) :=
    { Ideal.Quotient.factor hPeP with
      commutes' := fun r => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
        rfl }
  have hg : Function.Surjective g := fun z => Ideal.Quotient.factor_surjective hPeP z
  have hker : IsNilpotent (RingHom.ker (g : (B ⧸ P ^ e) →+* (B ⧸ P))) := by
    refine ⟨e, ?_⟩
    have hk : RingHom.ker (g : (B ⧸ P ^ e) →+* (B ⧸ P)) =
        P.map (Ideal.Quotient.mk (P ^ e)) := by
      ext x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      simp [g, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_quotient_iff_mem hPeP]
    rw [hk, ← Ideal.map_pow, Ideal.map_quotient_self]
    rfl
  have hrank : finrank (A ⧸ p) (B ⧸ P ^ e) = e * finrank (A ⧸ p) (B ⧸ P) :=
    Ideal.finrank_prime_pow_ramificationIdx p P hP he0
  letI : Field (A ⧸ p) := Ideal.Quotient.field p
  letI : Field (B ⧸ P) := Ideal.Quotient.field P
  haveI : IsScalarTower A (A ⧸ p) (B ⧸ P ^ e) := .of_algebraMap_eq' rfl
  haveI : Module.Finite (A ⧸ p) (B ⧸ P ^ e) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ P ^ e)
  obtain ⟨x, hx⟩ := exists_trace_ne_zero_of_nilpotent_ker (k := A ⧸ p) (R := B ⧸ P ^ e)
    (C := B ⧸ P) g hg hker e hrank he
  -- the Chinese remainder decomposition of `B ⧸ p B`
  letI : Algebra (A ⧸ p) (B ⧸ Q) := Ideal.Quotient.algebraQuotientOfLEComap (by
      rw [← Ideal.map_le_iff_le_comap, hQ]
      exact Ideal.mul_le_left)
  have : IsScalarTower A (A ⧸ p) (B ⧸ Q) := .of_algebraMap_eq' rfl
  have : Module.Finite (A ⧸ p) (B ⧸ Q) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ Q)
  letI eqv : (B ⧸ p.map (algebraMap A B)) ≃ₐ[A ⧸ p] ((B ⧸ P ^ e) × B ⧸ Q) :=
    { __ := (Ideal.quotEquivOfEq hQ).trans (Ideal.quotientMulEquivQuotientProd (P ^ e) Q hcop),
      commutes' := Quotient.ind fun _ ↦ rfl }
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (eqv.symm (x, 0))
  refine not_dvd_differentIdeal_of_intTrace_not_mem A (P ^ e) Q hQ.symm y ?_ ?_
  · have := congr((eqv $hy).2)
    simp at this
    simpa [eqv, Ideal.Quotient.eq_zero_iff_mem] using this
  · rw [← Ideal.Quotient.eq_zero_iff_mem, ← Algebra.trace_quotient_eq_of_isDedekindDomain,
      hy, Algebra.trace_eq_of_algEquiv, Algebra.trace_prod_apply]
    simpa

/-- **The tame different exponent.**  Under tame ramification at `P`,
`ord_P 𝔇_{B/A} = e(P|p) - 1`. -/
theorem count_differentIdeal_eq_of_tame [DecidableEq (Ideal B)]
    {p : Ideal A} [p.IsMaximal] (hp : p ≠ ⊥) (P : Ideal B) [P.IsMaximal] [P.LiesOver p]
    (hP : P ≠ ⊥) [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    (he : ((ramificationIdx' p P : ℕ) : A ⧸ p) ≠ 0) :
    (normalizedFactors (differentIdeal A B)).count P = ramificationIdx' p P - 1 := by
  have hPirr : Irreducible P := (Ideal.prime_of_isPrime hP inferInstance).irreducible
  have hD : differentIdeal A B ≠ ⊥ := differentIdeal_ne_bot
  have hcount : ∀ n : ℕ, P ^ n ∣ differentIdeal A B ↔
      n ≤ (normalizedFactors (differentIdeal A B)).count P := by
    intro n
    rw [pow_dvd_iff_le_emultiplicity, emultiplicity_eq_count_normalizedFactors hPirr hD,
      normalize_eq]
    exact_mod_cast Iff.rfl
  have hlow := (hcount _).mp (pow_sub_one_dvd_differentIdeal A P (ramificationIdx' p P) hp
    (Ideal.dvd_iff_le.mpr Ideal.le_pow_ramificationIdx'))
  have hup : ¬ ramificationIdx' p P ≤ (normalizedFactors (differentIdeal A B)).count P :=
    fun h => not_pow_ramificationIdx'_dvd_differentIdeal_of_tame hp P hP he ((hcount _).mpr h)
  omega

end Dedekind

/-- **IUT IV Prop 1.3 (i), equality in the tame case, for a Dedekind tower.**  If `P` is
tamely ramified over `Q` (`e(P|Q) ≠ 0` in `B ⧸ Q`, `C ⧸ P` separable over `B ⧸ Q`), then
`d_C = d_B + (e(P|Q) - 1) / e(P|p)`. -/
theorem iutIVProp13i_normalizedDifferent_eq_of_tame (A B C : Type*) [CommRing A] [CommRing B]
    [CommRing C] [IsDedekindDomain A] [IsDedekindDomain B] [IsDedekindDomain C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Module.Finite A B] [Module.Finite A C] [Module.Finite B C]
    [IsTorsionFree A B] [IsTorsionFree A C] [IsTorsionFree B C]
    [Algebra.IsSeparable (FractionRing A) (FractionRing C)]
    [DecidableEq (Ideal B)] [DecidableEq (Ideal C)]
    (p : Ideal A) (Q : Ideal B) (P : Ideal C) [p.IsPrime] [Q.IsMaximal] [P.IsMaximal]
    (hp : p ≠ ⊥) (hQ : Q ≠ ⊥) (hP : P ≠ ⊥) [Q.LiesOver p] [P.LiesOver Q] [P.LiesOver p]
    [Algebra.IsSeparable (B ⧸ Q) (C ⧸ P)]
    (htame : ((ramificationIdx' Q P : ℕ) : B ⧸ Q) ≠ 0) :
    ((normalizedFactors (differentIdeal A C)).count P : ℝ) / ramificationIdx' p P =
      ((normalizedFactors (differentIdeal A B)).count Q : ℝ) / ramificationIdx' p Q +
        ((ramificationIdx' Q P : ℝ) - 1) / ramificationIdx' p P := by
  have : Algebra.IsSeparable (FractionRing B) (FractionRing C) :=
    Algebra.isSeparable_tower_top_of_isSeparable (FractionRing A) _ _
  have htower : ramificationIdx' p P = ramificationIdx' p Q * ramificationIdx' Q P := by
    apply Ideal.ramificationIdx'_algebra_tower
    · exact Ideal.map_ne_bot_of_ne_bot hQ
    · exact Ideal.map_ne_bot_of_ne_bot hp
    · exact Ideal.map_le_iff_le_comap.mpr (le_of_eq (Ideal.over_def P Q))
  have heQ : ramificationIdx' p Q ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver Q hp
  have hePQ : ramificationIdx' Q P ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver P hQ
  have hcount := count_differentIdeal_tower A B C Q P hQ hP
  have hexact := count_differentIdeal_eq_of_tame (A := B) (B := C) hQ P hP htame
  set eQ := ramificationIdx' p Q
  set ePQ := ramificationIdx' Q P
  have heQr : (0 : ℝ) < eQ := by exact_mod_cast Nat.pos_of_ne_zero heQ
  have hePQr : (0 : ℝ) < ePQ := by exact_mod_cast Nat.pos_of_ne_zero hePQ
  have hsub : ((ePQ - 1 : ℕ) : ℝ) = (ePQ : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hePQ), Nat.cast_one]
  rw [htower, hcount, hexact]
  push_cast
  rw [hsub]
  field_simp
  ring

end LeanFormal.IUT.IUTIV.Estimates
