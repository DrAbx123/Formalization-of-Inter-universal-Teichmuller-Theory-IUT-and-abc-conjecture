import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionQuotientPow
import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# The `v`-adic completion of a Dedekind domain is the valuation completion

For a Dedekind domain `R` with fraction field `K` and a height-one prime `v`, let
`Ô_v = v.adicCompletionIntegers K` be the integers of the valuation completion
`v.adicCompletion K`.  This file proves:

* `Ô_v` is `m̂`-adically complete (`IsAdicComplete m̂ Ô_v`), from completeness of
  `v.adicCompletion K` and `m̂^n = {x | v(x) ≤ exp(-n)}`;
* the ring isomorphism `AdicCompletion v.asIdeal R ≃+* Ô_v`
  (`adicCompletionRingEquivAdicCompletionIntegers`), assembled from the level-`n`
  isomorphisms `R ⧸ v^n ≃+* Ô_v ⧸ m̂^n` of `FinitePlaceCompletionQuotientPow`, and its
  compatibility with `R` (`adicCompletionRingEquivAdicCompletionIntegers_of`).

This is step (b) of Claude board A.21: identifying the ideal-adic completion of `R` at
`v` with the valuation completion.  It does not prove the CRT decomposition of the
`p`-adic completion of `𝒪_F` into the completions at the primes over `p` (step (a)).
-/

set_option autoImplicit false

open scoped Valued WithZero Topology
open Filter

namespace LeanFormal.IUT.NumberFieldFinitePlace

/-- A nonzero element of `ℤᵐ⁰` dominates `exp(-n)` for some natural `n`. -/
theorem exists_withZero_exp_neg_natCast_lt {γ : ℤᵐ⁰} (hγ : γ ≠ 0) :
    ∃ n : ℕ, WithZero.exp (-(n : ℤ)) < γ := by
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, WithZero.exp k = γ := ⟨_, WithZero.exp_log hγ⟩
  refine ⟨(1 - k).toNat, ?_⟩
  rw [WithZero.exp_lt_exp]
  have h := Int.self_le_toNat (1 - k)
  omega

section AdicCompletionRingEquiv

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  (v : IsDedekindDomain.HeightOneSpectrum R)

/-- Valuation balls of positive radius around a point of `v.adicCompletion K` are
neighbourhoods of that point. -/
theorem valued_ball_mem_nhds_adicCompletion (x : v.adicCompletion K) {γ : ℤᵐ⁰}
    (hγ : 0 < γ) :
    {z : v.adicCompletion K | Valued.v (z - x) < γ} ∈ 𝓝 x := by
  obtain ⟨t, ht⟩ := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective K v γ
  let φ : v.adicCompletion K →*₀ ℤᵐ⁰ :=
    MonoidWithZeroHom.ofClass (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
  let γ₀ : MonoidWithZeroHom.ValueGroup₀ φ := MonoidWithZeroHom.ValueGroup₀.restrict₀ φ t
  have hemb : MonoidWithZeroHom.ValueGroup₀.embedding γ₀ = γ :=
    (MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀ (f := φ) t).trans ht
  have hγ₀ : γ₀ ≠ 0 := by
    intro hzero
    have hmap : MonoidWithZeroHom.ValueGroup₀.embedding γ₀ = 0 := by
      rw [hzero, map_zero]
    rw [hemb] at hmap
    exact (ne_of_gt hγ) hmap
  rw [Valued.mem_nhds]
  refine ⟨Units.mk0 γ₀ hγ₀, fun z hz => ?_⟩
  simp only [Set.mem_setOf_eq] at hz
  rw [Units.val_mk0, Valuation.restrict_lt_iff_lt_embedding] at hz
  rw [hemb] at hz
  exact hz

/-- An element of `Ô_v` lying in every power of `m̂` is zero. -/
theorem eq_zero_of_forall_mem_maximalIdeal_pow (x : v.adicCompletionIntegers K)
    (hx : ∀ n : ℕ, x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n) : x = 0 := by
  by_contra hne
  have hne' : Valued.v (x : v.adicCompletion K) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact fun h => hne (Subtype.ext h)
  obtain ⟨n, hn⟩ := exists_withZero_exp_neg_natCast_lt hne'
  exact absurd ((mem_maximalIdeal_pow_iff_valued_le_exp_neg v n x).mp (hx n)) (not_le.mpr hn)

/-- **`Ô_v` is `m̂`-adically complete.** -/
instance isAdicComplete_maximalIdeal_adicCompletionIntegers :
    IsAdicComplete (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
      (v.adicCompletionIntegers K) := by
  rw [isAdicComplete_iff]
  constructor
  · rw [isHausdorff_iff]
    intro x hx
    refine eq_zero_of_forall_mem_maximalIdeal_pow v x fun n => ?_
    have h := hx n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, sub_zero] at h
    exact h
  · rw [isPrecomplete_iff]
    intro f hf
    have hle : ∀ m n : ℕ, m ≤ n →
        Valued.v ((f m : v.adicCompletion K) - (f n : v.adicCompletion K)) ≤
          WithZero.exp (-(m : ℤ)) := by
      intro m n hmn
      have h := hf hmn
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top,
        mem_maximalIdeal_pow_iff_valued_le_exp_neg v m] at h
      exact h
    have hcauchy : CauchySeq fun n => (f n : v.adicCompletion K) := by
      rw [CauchySeq, Valued.cauchy_iff]
      refine ⟨Filter.map_neBot, fun γ => ?_⟩
      have hγne : MonoidWithZeroHom.ValueGroup₀.embedding (γ : MonoidWithZeroHom.ValueGroup₀
          (MonoidWithZeroHom.ofClass (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰))) ≠ 0 := by
        intro h0
        apply γ.ne_zero
        exact (map_eq_zero_iff _ MonoidWithZeroHom.ValueGroup₀.embedding_injective).mp h0
      obtain ⟨n, hn⟩ := exists_withZero_exp_neg_natCast_lt hγne
      refine ⟨(fun n => (f n : v.adicCompletion K)) '' Set.Ici n,
        Filter.image_mem_map (Filter.Ici_mem_atTop n), ?_⟩
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [Valuation.restrict_lt_iff_lt_embedding]
      refine lt_of_le_of_lt ?_ hn
      have hsplit : (f b : v.adicCompletion K) - (f a : v.adicCompletion K) =
          ((f n : v.adicCompletion K) - (f a : v.adicCompletion K)) -
            ((f n : v.adicCompletion K) - (f b : v.adicCompletion K)) := by ring
      rw [hsplit]
      exact le_trans (Valuation.map_sub _ _ _) (max_le (hle n a ha) (hle n b hb))
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
    have hnear : ∀ n : ℕ, ∃ m, n ≤ m ∧
        Valued.v ((f m : v.adicCompletion K) - L) < WithZero.exp (-(n : ℤ)) := by
      intro n
      have h1 : ∀ᶠ m in atTop,
          Valued.v ((f m : v.adicCompletion K) - L) < WithZero.exp (-(n : ℤ)) :=
        hL (valued_ball_mem_nhds_adicCompletion v L WithZero.exp_pos)
      obtain ⟨m, hm1, hm2⟩ := (h1.and (Filter.eventually_ge_atTop n)).exists
      exact ⟨m, hm2, hm1⟩
    have hLint : L ∈ v.adicCompletionIntegers K := by
      obtain ⟨m, -, hm⟩ := hnear 0
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
      have hsplit : L = (f m : v.adicCompletion K) - ((f m : v.adicCompletion K) - L) := by ring
      rw [hsplit]
      refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_)
      · exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers R K v).mp (f m).2
      · simpa using le_of_lt hm
    refine ⟨⟨L, hLint⟩, fun n => ?_⟩
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_maximalIdeal_pow_iff_valued_le_exp_neg v n]
    obtain ⟨m, hnm, hm⟩ := hnear n
    change Valued.v ((f n : v.adicCompletion K) - L) ≤ _
    have hsplit : (f n : v.adicCompletion K) - L =
        ((f n : v.adicCompletion K) - (f m : v.adicCompletion K)) +
          ((f m : v.adicCompletion K) - L) := by ring
    rw [hsplit]
    exact le_trans (Valuation.map_add _ _ _) (max_le (hle n m hnm) (le_of_lt hm))

/-- The level-`n` isomorphisms commute with the transition maps. -/
theorem factorPow_adicCompletionQuotientPowEquiv {m n : ℕ} (hle : m ≤ n)
    (x : R ⧸ v.asIdeal ^ n) :
    Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) hle
        (adicCompletionQuotientPowEquiv (K := K) v n x) =
      adicCompletionQuotientPowEquiv (K := K) v m (Ideal.Quotient.factorPow v.asIdeal hle x) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.factorPow _ hle
      (adicCompletionQuotientPowHom (K := K) v n (Ideal.Quotient.mk _ r)) =
    adicCompletionQuotientPowHom (K := K) v m
      (Ideal.Quotient.factorPow _ hle (Ideal.Quotient.mk _ r))
  rw [adicCompletionQuotientPowHom_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk,
    Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, adicCompletionQuotientPowHom_mk]

/-- The projections of the adic completion commute with the transition maps. -/
theorem factorPow_adicCompletion_evalₐ {S : Type*} [CommRing S] (I : Ideal S) {m n : ℕ}
    (hle : m ≤ n) (x : AdicCompletion I S) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  obtain ⟨f, rfl⟩ := AdicCompletion.mk_surjective I S x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow,
    Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
  have h := f.property hle
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h
  rw [← neg_sub]
  exact neg_mem h

/-- The compatible family `Ô_v → Ô_v ⧸ m̂^n ≃ R ⧸ v^n`. -/
noncomputable def adicCompletionIntegersQuotientFamily (n : ℕ) :
    v.adicCompletionIntegers K →+* R ⧸ v.asIdeal ^ n :=
  (adicCompletionQuotientPowEquiv (K := K) v n).symm.toRingHom.comp
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n))

theorem adicCompletionIntegersQuotientFamily_compatible {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow v.asIdeal hle).comp
        (adicCompletionIntegersQuotientFamily (K := K) v n) =
      adicCompletionIntegersQuotientFamily (K := K) v m := by
  ext x
  simp only [adicCompletionIntegersQuotientFamily, RingHom.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  apply (adicCompletionQuotientPowEquiv (K := K) v m).injective
  rw [RingEquiv.apply_symm_apply, ← factorPow_adicCompletionQuotientPowEquiv,
    RingEquiv.apply_symm_apply, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]

/-- The compatible family `AdicCompletion v R → R ⧸ v^n ≃ Ô_v ⧸ m̂^n`. -/
noncomputable def adicCompletionQuotientFamily (n : ℕ) :
    AdicCompletion v.asIdeal R →+*
      v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n :=
  (adicCompletionQuotientPowEquiv (K := K) v n).toRingHom.comp
    (AdicCompletion.evalₐ v.asIdeal n).toRingHom

theorem adicCompletionQuotientFamily_compatible {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) hle).comp
        (adicCompletionQuotientFamily (K := K) v n) =
      adicCompletionQuotientFamily (K := K) v m := by
  ext x
  simp only [adicCompletionQuotientFamily, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [factorPow_adicCompletionQuotientPowEquiv, factorPow_adicCompletion_evalₐ]

/-- The map `Ô_v → AdicCompletion v R`. -/
noncomputable def adicCompletionIntegersToAdicCompletion :
    v.adicCompletionIntegers K →+* AdicCompletion v.asIdeal R :=
  AdicCompletion.liftRingHom v.asIdeal (adicCompletionIntegersQuotientFamily (K := K) v)
    (adicCompletionIntegersQuotientFamily_compatible (K := K) v)

/-- The map `AdicCompletion v R → Ô_v`, using `m̂`-adic completeness of `Ô_v`. -/
noncomputable def adicCompletionToAdicCompletionIntegers :
    AdicCompletion v.asIdeal R →+* v.adicCompletionIntegers K :=
  (AdicCompletion.ofAlgEquiv
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))).symm.toRingHom.comp
    (AdicCompletion.liftRingHom (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
      (adicCompletionQuotientFamily (K := K) v)
      (adicCompletionQuotientFamily_compatible (K := K) v))

theorem evalₐ_adicCompletionIntegersToAdicCompletion (n : ℕ) (y : v.adicCompletionIntegers K) :
    AdicCompletion.evalₐ v.asIdeal n (adicCompletionIntegersToAdicCompletion (K := K) v y) =
      (adicCompletionQuotientPowEquiv (K := K) v n).symm (Ideal.Quotient.mk _ y) := by
  rw [adicCompletionIntegersToAdicCompletion, AdicCompletion.evalₐ_liftRingHom]
  rfl

theorem mk_adicCompletionToAdicCompletionIntegers (n : ℕ) (x : AdicCompletion v.asIdeal R) :
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n)
        (adicCompletionToAdicCompletionIntegers (K := K) v x) =
      adicCompletionQuotientPowEquiv (K := K) v n (AdicCompletion.evalₐ v.asIdeal n x) := by
  change Ideal.Quotient.mk _ ((AdicCompletion.ofAlgEquiv _).symm
      (AdicCompletion.liftRingHom (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
        (adicCompletionQuotientFamily (K := K) v)
        (adicCompletionQuotientFamily_compatible (K := K) v) x)) = _
  rw [AdicCompletion.mk_ofAlgEquiv_symm, AdicCompletion.evalₐ_liftRingHom]
  rfl

/-- A point of `Ô_v` is determined by its images in all `Ô_v ⧸ m̂^n`. -/
theorem adicCompletionIntegers_ext {x y : v.adicCompletionIntegers K}
    (h : ∀ n : ℕ, Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n) x =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n) y) : x = y := by
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_mem_maximalIdeal_pow v (x - y) fun n => ?_
  exact Ideal.Quotient.eq.mp (h n)

/-- **`AdicCompletion v.asIdeal R ≃+* Ô_v`** (Claude board A.21 step (b)). -/
noncomputable def adicCompletionRingEquivAdicCompletionIntegers :
    AdicCompletion v.asIdeal R ≃+* v.adicCompletionIntegers K :=
  RingEquiv.ofRingHom (adicCompletionToAdicCompletionIntegers (K := K) v)
    (adicCompletionIntegersToAdicCompletion (K := K) v)
    (by
      refine RingHom.ext fun y => ?_
      refine adicCompletionIntegers_ext (K := K) v fun n => ?_
      rw [RingHom.comp_apply, RingHom.id_apply, mk_adicCompletionToAdicCompletionIntegers,
        evalₐ_adicCompletionIntegersToAdicCompletion, RingEquiv.apply_symm_apply])
    (by
      refine RingHom.ext fun x => ?_
      refine AdicCompletion.ext_evalₐ fun n => ?_
      rw [RingHom.comp_apply, RingHom.id_apply, evalₐ_adicCompletionIntegersToAdicCompletion,
        mk_adicCompletionToAdicCompletionIntegers, RingEquiv.symm_apply_apply])

/-- The isomorphism is compatible with the structure maps from `R`. -/
theorem adicCompletionRingEquivAdicCompletionIntegers_of (r : R) :
    adicCompletionRingEquivAdicCompletionIntegers (K := K) v (AdicCompletion.of v.asIdeal R r) =
      algebraMap R (v.adicCompletionIntegers K) r := by
  refine adicCompletionIntegers_ext (K := K) v fun n => ?_
  change Ideal.Quotient.mk _ (adicCompletionToAdicCompletionIntegers (K := K) v
    (AdicCompletion.of v.asIdeal R r)) = _
  rw [mk_adicCompletionToAdicCompletionIntegers, AdicCompletion.evalₐ_of]
  exact adicCompletionQuotientPowHom_mk v n r

end AdicCompletionRingEquiv

end LeanFormal.IUT.NumberFieldFinitePlace
