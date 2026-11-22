import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceAdicCompletionRingEquiv

/-!
# Chinese remainder theorem for adic completions

Let `R` be a commutative ring, `I` an ideal, and `J : ι → Ideal R` a finite family of
pairwise coprime ideals with exponents `e i ≥ 1` such that
`I ^ n = ⨅ i, J i ^ (e i * n)` for every `n`.  Then

`AdicCompletion I R ≃+* ∀ i, AdicCompletion (J i) R`
(`adicCompletionPiEquiv`), compatible with the structure maps from `R`.

Level `n` is the Chinese remainder theorem `R ⧸ I^n ≃ ∏ R ⧸ J_i^(e_i n)`; the inverse
limits are matched through the universal property `AdicCompletion.liftRingHom` and
`AdicCompletion.ext_evalₐ`, so no cofinality reindexing is needed.

This is the algebraic half of Claude board A.21 step (a): applied to `I = p𝒪_F` and the
primes `P ∣ p` it splits the `p`-adic completion of `𝒪_F` into the `P`-adic ones.
-/

set_option autoImplicit false

namespace LeanFormal.IUT.AdicCompletionChineseRemainder

open Function LeanFormal.IUT.NumberFieldFinitePlace

section General

variable {R : Type*} [CommRing R]

/-- Given a level `N`, an element of the adic completion has one representative in `R`
for all levels `k ≤ N`. -/
theorem exists_evalₐ_eq_mk_of_le (I : Ideal R) (x : AdicCompletion I R) (N : ℕ) :
    ∃ r : R, ∀ k, k ≤ N → AdicCompletion.evalₐ I k x = Ideal.Quotient.mk (I ^ k) r := by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I N x)
  refine ⟨r, fun k hk => ?_⟩
  rw [← factorPow_adicCompletion_evalₐ I hk x, ← hr, Ideal.Quotient.factorPow,
    Ideal.Quotient.factor_mk]

variable {ι : Type*} [Finite ι] (I : Ideal R) (J : ι → Ideal R) (e : ι → ℕ)

omit [Finite ι] in
theorem pairwise_isCoprime_pow (hcop : Pairwise (IsCoprime on J)) (n : ℕ) :
    Pairwise (IsCoprime on fun i => J i ^ (e i * n)) :=
  fun _ _ hij => (hcop hij).pow

/-- The level-`n` Chinese remainder isomorphism `R ⧸ I^n ≃ ∏ R ⧸ J_i^(e_i n)`. -/
noncomputable def levelChineseRemainder (hcop : Pairwise (IsCoprime on J))
    (hI : ∀ n : ℕ, I ^ n = ⨅ i, J i ^ (e i * n)) (n : ℕ) :
    R ⧸ I ^ n ≃+* ∀ i, R ⧸ J i ^ (e i * n) :=
  (Ideal.quotEquivOfEq (hI n)).trans
    (Ideal.quotientInfRingEquivPiQuotient _ (pairwise_isCoprime_pow J e hcop n))

variable {I J e}

theorem levelChineseRemainder_mk (hcop : Pairwise (IsCoprime on J))
    (hI : ∀ n : ℕ, I ^ n = ⨅ i, J i ^ (e i * n)) (n : ℕ) (r : R) :
    levelChineseRemainder I J e hcop hI n (Ideal.Quotient.mk _ r) =
      fun i => Ideal.Quotient.mk (J i ^ (e i * n)) r := by
  simp only [levelChineseRemainder, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  rfl

theorem levelChineseRemainder_symm_eq_mk (hcop : Pairwise (IsCoprime on J))
    (hI : ∀ n : ℕ, I ^ n = ⨅ i, J i ^ (e i * n)) (n : ℕ) (r : R)
    (y : ∀ i, R ⧸ J i ^ (e i * n)) (hy : ∀ i, y i = Ideal.Quotient.mk _ r) :
    (levelChineseRemainder I J e hcop hI n).symm y = Ideal.Quotient.mk _ r := by
  have : y = levelChineseRemainder I J e hcop hI n (Ideal.Quotient.mk _ r) := by
    rw [levelChineseRemainder_mk]
    exact funext hy
  rw [this, RingEquiv.symm_apply_apply]

omit [Finite ι] in
theorem le_of_pow_eq_iInf (hpos : ∀ i, 1 ≤ e i) (hI : ∀ n : ℕ, I ^ n = ⨅ i, J i ^ (e i * n))
    (i : ι) : I ≤ J i := by
  have h1 := hI 1
  rw [pow_one] at h1
  rw [h1]
  refine le_trans (iInf_le _ i) ?_
  exact Ideal.pow_le_self (by have := hpos i; omega)

/-- The level-`n` family `AdicCompletion I R → R ⧸ I^n → R ⧸ (J i)^n` (from `I ≤ J i`). -/
noncomputable def componentLevelFamily {i : ι} (hle : I ≤ J i) (n : ℕ) :
    AdicCompletion I R →+* R ⧸ J i ^ n :=
  (Ideal.Quotient.factor (Ideal.pow_right_mono hle n)).comp (AdicCompletion.evalₐ I n).toRingHom

omit [Finite ι] in
theorem componentLevelFamily_compatible {i : ι} (hle : I ≤ J i) {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow (J i) hmn).comp (componentLevelFamily hle n) =
      componentLevelFamily hle m := by
  refine RingHom.ext fun x => ?_
  obtain ⟨r, hr⟩ := exists_evalₐ_eq_mk_of_le I x n
  simp only [componentLevelFamily, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [hr n le_rfl, hr m hmn, Ideal.Quotient.factor_mk, Ideal.Quotient.factorPow,
    Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk]

/-- The component map `AdicCompletion I R → AdicCompletion (J i) R` (from `I ≤ J i`). -/
noncomputable def adicCompletionComponent {i : ι} (hle : I ≤ J i) :
    AdicCompletion I R →+* AdicCompletion (J i) R :=
  AdicCompletion.liftRingHom (J i) (componentLevelFamily hle) (componentLevelFamily_compatible hle)

omit [Finite ι] in
theorem evalₐ_adicCompletionComponent {i : ι} (hle : I ≤ J i) (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ (J i) n (adicCompletionComponent hle x) =
      Ideal.Quotient.factor (Ideal.pow_right_mono hle n) (AdicCompletion.evalₐ I n x) := by
  rw [adicCompletionComponent, AdicCompletion.evalₐ_liftRingHom]
  rfl
/-- The level-`n` family `∏ AdicCompletion (J i) R → R ⧸ I^n`. -/
noncomputable def piLevelFamily (hcop : Pairwise (IsCoprime on J))
    (hI : ∀ n : ℕ, I ^ n = ⨅ i, J i ^ (e i * n)) (n : ℕ) :
    (∀ i, AdicCompletion (J i) R) →+* R ⧸ I ^ n :=
  (levelChineseRemainder I J e hcop hI n).symm.toRingHom.comp
    (RingHom.pi fun i => (AdicCompletion.evalₐ (J i) (e i * n)).toRingHom.comp
      (Pi.evalRingHom (fun i => AdicCompletion (J i) R) i))

theorem piLevelFamily_apply (hcop : Pairwise (IsCoprime on J))
    (hI : ∀ n : ℕ, I ^ n = ⨅ i, J i ^ (e i * n)) (n : ℕ) (x : ∀ i, AdicCompletion (J i) R) :
    piLevelFamily hcop hI n x =
      (levelChineseRemainder I J e hcop hI n).symm
        (fun i => AdicCompletion.evalₐ (J i) (e i * n) (x i)) :=
  rfl

/-- If the level-`n` family value is represented by `r`, so is every component. -/
theorem evalₐ_eq_mk_of_piLevelFamily_eq (hcop : Pairwise (IsCoprime on J))
    (hI : ∀ n : ℕ, I ^ n = ⨅ i, J i ^ (e i * n)) (n : ℕ) (x : ∀ i, AdicCompletion (J i) R)
    (r : R) (hr : piLevelFamily hcop hI n x = Ideal.Quotient.mk _ r) (i : ι) :
    AdicCompletion.evalₐ (J i) (e i * n) (x i) = Ideal.Quotient.mk _ r := by
  have h := congrArg (levelChineseRemainder I J e hcop hI n) hr
  rw [piLevelFamily_apply, RingEquiv.apply_symm_apply, levelChineseRemainder_mk] at h
  exact congrFun h i

theorem piLevelFamily_compatible (hcop : Pairwise (IsCoprime on J))
    (hI : ∀ n : ℕ, I ^ n = ⨅ i, J i ^ (e i * n)) {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow I hmn).comp (piLevelFamily hcop hI n) = piLevelFamily hcop hI m := by
  refine RingHom.ext fun x => ?_
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (piLevelFamily hcop hI n x)
  have hcomp := evalₐ_eq_mk_of_piLevelFamily_eq hcop hI n x r hr.symm
  rw [RingHom.comp_apply, ← hr, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk,
    piLevelFamily_apply]
  refine (levelChineseRemainder_symm_eq_mk hcop hI m r _ fun i => ?_).symm
  rw [← factorPow_adicCompletion_evalₐ (J i) (Nat.mul_le_mul_left (e i) hmn), hcomp i,
    Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]

/-- The map `∏ AdicCompletion (J i) R → AdicCompletion I R`. -/
noncomputable def piToAdicCompletion (hcop : Pairwise (IsCoprime on J))
    (hI : ∀ n : ℕ, I ^ n = ⨅ i, J i ^ (e i * n)) :
    (∀ i, AdicCompletion (J i) R) →+* AdicCompletion I R :=
  AdicCompletion.liftRingHom I (piLevelFamily hcop hI) (piLevelFamily_compatible hcop hI)

/-- The map `AdicCompletion I R → ∏ AdicCompletion (J i) R`. -/
noncomputable def adicCompletionToPi (hpos : ∀ i, 1 ≤ e i)
    (hI : ∀ n : ℕ, I ^ n = ⨅ i, J i ^ (e i * n)) :
    AdicCompletion I R →+* ∀ i, AdicCompletion (J i) R :=
  RingHom.pi fun i => adicCompletionComponent (le_of_pow_eq_iInf hpos hI i)

/-- **Chinese remainder theorem for adic completions.** -/
noncomputable def adicCompletionPiEquiv (hcop : Pairwise (IsCoprime on J))
    (hpos : ∀ i, 1 ≤ e i) (hI : ∀ n : ℕ, I ^ n = ⨅ i, J i ^ (e i * n)) :
    AdicCompletion I R ≃+* ∀ i, AdicCompletion (J i) R :=
  RingEquiv.ofRingHom (adicCompletionToPi hpos hI) (piToAdicCompletion hcop hI)
    (by
      refine RingHom.ext fun x => funext fun i => ?_
      refine AdicCompletion.ext_evalₐ fun n => ?_
      rw [RingHom.comp_apply, RingHom.id_apply, adicCompletionToPi, RingHom.pi_apply,
        evalₐ_adicCompletionComponent, piToAdicCompletion, AdicCompletion.evalₐ_liftRingHom]
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (piLevelFamily hcop hI n x)
      have hcomp := evalₐ_eq_mk_of_piLevelFamily_eq hcop hI n x r hr.symm i
      have hn : n ≤ e i * n := Nat.le_mul_of_pos_left n (hpos i)
      rw [← hr, Ideal.Quotient.factor_mk, ← factorPow_adicCompletion_evalₐ (J i) hn, hcomp,
        Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk])
    (by
      classical
      cases nonempty_fintype ι
      refine RingHom.ext fun x => ?_
      refine AdicCompletion.ext_evalₐ fun n => ?_
      rw [RingHom.comp_apply, RingHom.id_apply, piToAdicCompletion,
        AdicCompletion.evalₐ_liftRingHom, piLevelFamily_apply]
      obtain ⟨r, hr⟩ := exists_evalₐ_eq_mk_of_le I x (n + ∑ j, e j * n)
      rw [hr n (Nat.le_add_right _ _)]
      refine levelChineseRemainder_symm_eq_mk hcop hI n r _ fun i => ?_
      have hi : e i * n ≤ n + ∑ j, e j * n :=
        le_trans (Finset.single_le_sum (fun j _ => Nat.zero_le (e j * n)) (Finset.mem_univ i))
          (Nat.le_add_left _ _)
      change AdicCompletion.evalₐ (J i) (e i * n)
        (adicCompletionComponent (le_of_pow_eq_iInf hpos hI i) x) = _
      rw [evalₐ_adicCompletionComponent, hr _ hi, Ideal.Quotient.factor_mk])

omit [Finite ι] in
theorem adicCompletionComponent_of {i : ι} (hle : I ≤ J i) (r : R) :
    adicCompletionComponent hle (AdicCompletion.of I R r) = AdicCompletion.of (J i) R r := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_adicCompletionComponent, AdicCompletion.evalₐ_of, Ideal.Quotient.factor_mk,
    AdicCompletion.evalₐ_of]

/-- The Chinese remainder isomorphism is compatible with the structure maps from `R`. -/
theorem adicCompletionPiEquiv_of (hcop : Pairwise (IsCoprime on J))
    (hpos : ∀ i, 1 ≤ e i) (hI : ∀ n : ℕ, I ^ n = ⨅ i, J i ^ (e i * n)) (r : R) :
    adicCompletionPiEquiv hcop hpos hI (AdicCompletion.of I R r) =
      fun i => AdicCompletion.of (J i) R r :=
  funext fun i => adicCompletionComponent_of (le_of_pow_eq_iInf hpos hI i) r

end General

section Dedekind

open UniqueFactorizationMonoid IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

theorem prod_factors_pow_count_eq {I : Ideal R} (hI : I ≠ ⊥) :
    ∏ P : (factors I).toFinset, (P : Ideal R) ^ (factors I).count (P : Ideal R) = I :=
  calc
    (∏ P : (factors I).toFinset, (P : Ideal R) ^ (factors I).count (P : Ideal R)) =
        ∏ P ∈ (factors I).toFinset, P ^ (factors I).count P :=
      (factors I).toFinset.prod_coe_sort fun P => P ^ (factors I).count P
    _ = ((factors I).map fun P => P).prod := (Finset.prod_multiset_map_count (factors I) id).symm
    _ = (factors I).prod := by rw [Multiset.map_id']
    _ = I := associated_iff_eq.mp (factors_prod hI)

theorem isCoprime_of_mem_factors {I P Q : Ideal R} (hP : P ∈ factors I) (hQ : Q ∈ factors I)
    (hne : P ≠ Q) : IsCoprime P Q := by
  have hPp := prime_of_factor P hP
  have hQp := prime_of_factor Q hQ
  exact Ideal.isCoprime_iff_sup_eq.mpr (Ideal.IsMaximal.coprime_of_ne
    (Ideal.IsPrime.isMaximal (Ideal.isPrime_of_prime hPp) hPp.ne_zero)
    (Ideal.IsPrime.isMaximal (Ideal.isPrime_of_prime hQp) hQp.ne_zero) hne)

theorem pairwise_isCoprime_factors (I : Ideal R) :
    Pairwise (IsCoprime on fun P : (factors I).toFinset => (P : Ideal R)) :=
  fun P Q hPQ => isCoprime_of_mem_factors (Multiset.mem_toFinset.mp P.2)
    (Multiset.mem_toFinset.mp Q.2) (Subtype.coe_injective.ne hPQ)

theorem one_le_count_factors (I : Ideal R) (P : (factors I).toFinset) :
    1 ≤ (factors I).count (P : Ideal R) :=
  Multiset.count_pos.mpr (Multiset.mem_toFinset.mp P.2)

/-- `I ^ n` is the intersection of the prime-power factors `P ^ (e_P n)`. -/
theorem pow_eq_iInf_factors_pow {I : Ideal R} (hI : I ≠ ⊥) (n : ℕ) :
    I ^ n = ⨅ P : (factors I).toFinset, (P : Ideal R) ^ ((factors I).count (P : Ideal R) * n) := by
  conv_lhs => rw [← prod_factors_pow_count_eq hI]
  rw [← Finset.prod_pow]
  simp_rw [← pow_mul]
  rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime]
  · simp only [Finset.mem_univ, iInf_pos]
  · intro P _ Q _ hPQ
    exact (pairwise_isCoprime_factors I hPQ).pow

/-- **`I`-adic completion of a Dedekind domain splits over the prime factors of `I`.** -/
noncomputable def adicCompletionFactorsEquiv {I : Ideal R} (hI : I ≠ ⊥) :
    AdicCompletion I R ≃+* ∀ P : (factors I).toFinset, AdicCompletion (P : Ideal R) R :=
  adicCompletionPiEquiv (J := fun P : (factors I).toFinset => (P : Ideal R))
    (e := fun P => (factors I).count (P : Ideal R)) (pairwise_isCoprime_factors I)
    (one_le_count_factors I) (pow_eq_iInf_factors_pow hI)

/-- A prime factor of `I` as a point of the height-one spectrum. -/
def factorHeightOneSpectrum {I : Ideal R} (P : (factors I).toFinset) : HeightOneSpectrum R :=
  ⟨P, Ideal.isPrime_of_prime (prime_of_factor _ (Multiset.mem_toFinset.mp P.2)),
    (prime_of_factor _ (Multiset.mem_toFinset.mp P.2)).ne_zero⟩

/-- **`I`-adic completion = product of the valuation completions at the primes `P ∣ I`**
(Claude board A.21 steps (a)+(b)). -/
noncomputable def adicCompletionEquivPiAdicCompletionIntegers (K : Type*) [Field K]
    [Algebra R K] [IsFractionRing R K] {I : Ideal R} (hI : I ≠ ⊥) :
    AdicCompletion I R ≃+*
      ∀ P : (factors I).toFinset, (factorHeightOneSpectrum P).adicCompletionIntegers K :=
  (adicCompletionFactorsEquiv hI).trans
    (RingEquiv.piCongrRight fun P =>
      adicCompletionRingEquivAdicCompletionIntegers (K := K) (factorHeightOneSpectrum P))

theorem adicCompletionEquivPiAdicCompletionIntegers_of (K : Type*) [Field K]
    [Algebra R K] [IsFractionRing R K] {I : Ideal R} (hI : I ≠ ⊥) (r : R) :
    adicCompletionEquivPiAdicCompletionIntegers K hI (AdicCompletion.of I R r) =
      fun P => algebraMap R ((factorHeightOneSpectrum P).adicCompletionIntegers K) r := by
  rw [adicCompletionEquivPiAdicCompletionIntegers, RingEquiv.trans_apply,
    adicCompletionFactorsEquiv, adicCompletionPiEquiv_of]
  funext P
  exact adicCompletionRingEquivAdicCompletionIntegers_of (K := K) (factorHeightOneSpectrum P) r

end Dedekind
end LeanFormal.IUT.AdicCompletionChineseRemainder
