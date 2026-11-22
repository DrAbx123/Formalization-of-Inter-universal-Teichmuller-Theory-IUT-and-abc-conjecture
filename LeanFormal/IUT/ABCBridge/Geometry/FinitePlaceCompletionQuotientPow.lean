import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionLocalInputs

/-!
# Level-`n` quotients of the adic completion of a Dedekind domain

For a Dedekind domain `R` with fraction field `K` and a height-one prime `v`, the
natural map `R → Ô_v` (the integers of the `v`-adic completion) induces, for every
`n`, a ring isomorphism

`R ⧸ v^n ≃+* Ô_v ⧸ m̂^n`.

This generalizes `adicCompletionResidueQuotientEquiv` (the case `n = 1`) and is the
levelwise input for identifying the `v`-adic (`I`-adic) completion of `R` with the
valuation completion (Claude board A.21, step (b)); it is also the integral
compatibility used for comparing global and local differents.

Kernel: `r ∈ v^n ↔ v(r) ≤ exp(-n) ↔ r ∈ m̂^n`.  Surjectivity: approximate
`x ∈ Ô_v` by `y ∈ K` to within `exp(-n)`, then `y` by `a ∈ R`.
-/

set_option autoImplicit false

open scoped Valued WithZero

namespace LeanFormal.IUT.NumberFieldFinitePlace

section AdicCompletionQuotientPow

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  (v : IsDedekindDomain.HeightOneSpectrum R)

/-- `r ∈ v^n` iff its image in the completed integers lies in `m̂^n`. -/
theorem algebraMap_mem_maximalIdeal_pow_iff (n : ℕ) (r : R) :
    algebraMap R (v.adicCompletionIntegers K) r ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n ↔
      r ∈ v.asIdeal ^ n := by
  rw [mem_maximalIdeal_pow_iff_valued_le_exp_neg v n, valued_algebraMap_adicCompletionIntegers v r,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem]

/-- Every element of the completed integers is congruent modulo `m̂^n` to an element of
`R`. -/
theorem exists_algebraMap_sub_mem_maximalIdeal_pow (n : ℕ) (x : v.adicCompletionIntegers K) :
    ∃ a : R, algebraMap R (v.adicCompletionIntegers K) a - x ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n := by
  have hpos : (0 : ℤᵐ⁰) < WithZero.exp (-(n : ℤ)) := WithZero.exp_pos
  obtain ⟨y, hy⟩ := exists_completion_sub_algebraMap_lt v (x : v.adicCompletion K) hpos
  have hlt1 : WithZero.exp (-(n : ℤ)) ≤ (1 : ℤᵐ⁰) := by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by omega)
  have hy1 : v.valuation K y ≤ 1 := by
    rw [← IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) (k := y)]
    have hsplit : (y : v.adicCompletion K) =
        ((y : v.adicCompletion K) - (x : v.adicCompletion K)) + (x : v.adicCompletion K) := by
      ring
    rw [hsplit]
    refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)
    · rw [Valuation.map_sub_swap]
      exact le_trans (le_of_lt hy) hlt1
    · exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers R K v).mp x.2
  obtain ⟨a, ha⟩ := IsDedekindDomain.HeightOneSpectrum.exists_valuation_sub_lt_of_integer v hy1
    (Units.mk0 (WithZero.exp (-(n : ℤ))) WithZero.exp_ne_zero)
  have ha' : v.valuation K (algebraMap R K a - y) < WithZero.exp (-(n : ℤ)) := by
    simpa only [Units.val_mk0] using ha
  refine ⟨a, ?_⟩
  rw [mem_maximalIdeal_pow_iff_valued_le_exp_neg v n]
  rw [show ((algebraMap R (v.adicCompletionIntegers K) a - x : v.adicCompletionIntegers K) :
      v.adicCompletion K) =
      algebraMap K (v.adicCompletion K) (algebraMap R K a) - (x : v.adicCompletion K) from by
    rw [show ((algebraMap R (v.adicCompletionIntegers K) a - x : v.adicCompletionIntegers K) :
        v.adicCompletion K) =
        ((algebraMap R (v.adicCompletionIntegers K) a : v.adicCompletionIntegers K) :
          v.adicCompletion K) - (x : v.adicCompletion K) from by push_cast; ring]
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
      IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
    rfl]
  have hsplit : algebraMap K (v.adicCompletion K) (algebraMap R K a) - (x : v.adicCompletion K) =
      (algebraMap K (v.adicCompletion K) y - (x : v.adicCompletion K)) +
        (algebraMap K (v.adicCompletion K) (algebraMap R K a) -
          algebraMap K (v.adicCompletion K) y) := by ring
  rw [hsplit]
  refine le_of_lt (lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_))
  · rw [Valuation.map_sub_swap]
    exact hy
  · rw [← map_sub]
    exact lt_of_eq_of_lt
      (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v)
        (k := algebraMap R K a - y)) ha'

/-- The ring map `R ⧸ v^n → Ô_v ⧸ m̂^n` induced by `R → Ô_v`. -/
noncomputable def adicCompletionQuotientPowHom (n : ℕ) :
    (R ⧸ v.asIdeal ^ n) →+*
      (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n) :=
  Ideal.Quotient.lift (v.asIdeal ^ n)
    ((Ideal.Quotient.mk _).comp (algebraMap R (v.adicCompletionIntegers K)))
    (by
      intro r hr
      change Ideal.Quotient.mk _ (algebraMap R (v.adicCompletionIntegers K) r) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact (algebraMap_mem_maximalIdeal_pow_iff v n r).mpr hr)

theorem adicCompletionQuotientPowHom_mk (n : ℕ) (r : R) :
    adicCompletionQuotientPowHom (K := K) v n (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ (algebraMap R (v.adicCompletionIntegers K) r) := by
  simp only [adicCompletionQuotientPowHom, Ideal.Quotient.lift_mk, RingHom.comp_apply]

theorem adicCompletionQuotientPowHom_injective (n : ℕ) :
    Function.Injective (adicCompletionQuotientPowHom (K := K) v n) := by
  intro x y h
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [adicCompletionQuotientPowHom_mk, adicCompletionQuotientPowHom_mk] at h
  refine Ideal.Quotient.eq.mpr ?_
  have hmem : algebraMap R (v.adicCompletionIntegers K) (a - b) ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n := by
    rw [map_sub]
    exact Ideal.Quotient.eq.mp h
  exact (algebraMap_mem_maximalIdeal_pow_iff v n (a - b)).mp hmem

theorem adicCompletionQuotientPowHom_surjective (n : ℕ) :
    Function.Surjective (adicCompletionQuotientPowHom (K := K) v n) := by
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, ha⟩ := exists_algebraMap_sub_mem_maximalIdeal_pow v n x
  refine ⟨Ideal.Quotient.mk _ a, ?_⟩
  rw [adicCompletionQuotientPowHom_mk]
  exact Ideal.Quotient.eq.mpr ha

/-- **Level-`n` quotient isomorphism.**  `R ⧸ v^n ≃+* Ô_v ⧸ m̂^n` for every `n`. -/
noncomputable def adicCompletionQuotientPowEquiv (n : ℕ) :
    (R ⧸ v.asIdeal ^ n) ≃+*
      (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n) :=
  RingEquiv.ofBijective (adicCompletionQuotientPowHom v n)
    ⟨adicCompletionQuotientPowHom_injective v n, adicCompletionQuotientPowHom_surjective v n⟩

end AdicCompletionQuotientPow

end LeanFormal.IUT.NumberFieldFinitePlace
