import LeanFormal.IUT.IUTIV.Estimates.DifferentTowerEstimate
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-!
# An upper bound for the different from the trace of one

Consumer: IUT IV Proposition 1.3(ii). The trace obstruction bounds the
different of a finite extension of discrete valuation rings directly.
-/

namespace LeanFormal.IUT.IUTIV.Estimates

open IsLocalRing UniqueFactorizationMonoid

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (A B : Type*) [CommRing A] [CommRing B]
  [IsDedekindDomain A] [IsDedekindDomain B] [Algebra A B]
  [Module.Finite A B] [Module.IsTorsionFree A B]
  [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

/-- A base ideal excluding the extension degree cannot map into the different. -/
theorem not_map_dvd_differentIdeal_of_degree_not_mem
    (baseIdeal : Ideal A)
    (degree_not_mem : (Module.finrank (FractionRing A) (FractionRing B) : A) ∉ baseIdeal) :
    ¬ baseIdeal.map (algebraMap A B) ∣ differentIdeal A B := by
  have trace_one : Algebra.intTrace A B 1 =
      (Module.finrank (FractionRing A) (FractionRing B) : A) := by
    apply IsFractionRing.injective A (FractionRing A)
    rw [Algebra.algebraMap_intTrace_fractionRing, map_natCast, map_one]
    simpa using Algebra.trace_algebraMap (R := FractionRing A) (S := FractionRing B) 1
  apply not_dvd_differentIdeal_of_intTrace_not_mem A
    (p := baseIdeal) (baseIdeal.map (algebraMap A B)) ⊤ (by simp) (1 : B) (by simp)
  simpa only [trace_one] using degree_not_mem

section DiscreteValuation

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem dvr_maximalIdeal_ne_bot : maximalIdeal R ≠ ⊥ := by
  obtain ⟨uniformizer, irreducible⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [irreducible.maximalIdeal_eq]
  simpa using irreducible.ne_zero

theorem dvr_ideal_eq_pow_factorCount (ideal : Ideal R) (nonzero : ideal ≠ ⊥) :
    ideal = maximalIdeal R ^ (normalizedFactors ideal).count (maximalIdeal R) := by
  obtain ⟨uniformizer, irreducible⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨exponent, ideal_eq⟩ :=
    IsDiscreteValuationRing.ideal_eq_span_pow_irreducible nonzero irreducible
  have ideal_power : ideal = maximalIdeal R ^ exponent := by
    rw [irreducible.maximalIdeal_eq, Ideal.span_singleton_pow]
    exact ideal_eq
  let prime : IsDedekindDomain.HeightOneSpectrum R :=
    ⟨maximalIdeal R, inferInstance, dvr_maximalIdeal_ne_bot R⟩
  rw [ideal_power, prime.irreducible.normalizedFactors_pow]
  simp [prime]

theorem dvr_factorCount_lt_of_not_dvd (ideal : Ideal R) (nonzero : ideal ≠ ⊥)
    (exponent : ℕ) (not_dvd : ¬ maximalIdeal R ^ exponent ∣ ideal) :
    (normalizedFactors ideal).count (maximalIdeal R) < exponent := by
  by_contra! greater
  apply not_dvd
  rw [dvr_ideal_eq_pow_factorCount R ideal nonzero]
  exact pow_dvd_pow _ greater

theorem dvr_factorCount_pow_maximalIdeal (exponent : ℕ) :
    (normalizedFactors (maximalIdeal R ^ exponent)).count (maximalIdeal R) = exponent := by
  let prime : IsDedekindDomain.HeightOneSpectrum R :=
    ⟨maximalIdeal R, inferInstance, dvr_maximalIdeal_ne_bot R⟩
  rw [prime.irreducible.normalizedFactors_pow]
  simp [prime]

theorem dvr_not_mem_pow_succ_factorCount (element : R) (nonzero : element ≠ 0) :
    element ∉ maximalIdeal R ^
      ((normalizedFactors (Ideal.span {element})).count (maximalIdeal R) + 1) := by
  intro membership
  have inclusion : Ideal.span {element} ≤ maximalIdeal R ^
      ((normalizedFactors (Ideal.span {element})).count (maximalIdeal R) + 1) := by
    apply Ideal.span_le.mpr
    simpa using membership
  have span_nonzero : Ideal.span {element} ≠ ⊥ := by simpa using nonzero
  have count_bound := Ideal.count_le_of_ideal_ge inclusion span_nonzero (maximalIdeal R)
  rw [dvr_factorCount_pow_maximalIdeal] at count_bound
  omega

theorem dvr_natCast_span_eq_prime_span_pow [CharZero R] (p : ℕ) [Fact p.Prime]
    [CharP (R ⧸ maximalIdeal R) p] (degree : ℕ) (degree_nonzero : degree ≠ 0) :
    Ideal.span {(degree : R)} = Ideal.span {(p : R)} ^ padicValNat p degree := by
  obtain ⟨primeToPart, factorization⟩ := pow_padicValNat_dvd (p := p) (n := degree)
  have prime_not_dvd : ¬ p ∣ primeToPart := by
    intro divisor
    apply pow_succ_padicValNat_not_dvd (p := p) degree_nonzero
    rw [pow_succ]
    conv_rhs => rw [factorization]
    exact Nat.mul_dvd_mul_left _ divisor
  have unit_part : IsUnit (primeToPart : R) := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    intro membership
    have residue_zero : (primeToPart : R ⧸ maximalIdeal R) = 0 := by
      simpa using (Ideal.Quotient.eq_zero_iff_mem).2 membership
    exact prime_not_dvd ((CharP.cast_eq_zero_iff (R ⧸ maximalIdeal R) p primeToPart).mp
      residue_zero)
  have cast_factorization : (degree : R) = (p : R) ^ padicValNat p degree * primeToPart := by
    exact_mod_cast factorization
  rw [cast_factorization, Ideal.span_singleton_mul_right_unit unit_part,
    ← Ideal.span_singleton_pow]

theorem dvr_natCast_factorCount [CharZero R] (p : ℕ) [Fact p.Prime]
    [CharP (R ⧸ maximalIdeal R) p] (degree : ℕ) (degree_nonzero : degree ≠ 0) :
    (normalizedFactors (Ideal.span {(degree : R)})).count (maximalIdeal R) =
      (normalizedFactors (Ideal.span {(p : R)})).count (maximalIdeal R) *
        padicValNat p degree := by
  have prime_nonzero : Ideal.span {(p : R)} ≠ ⊥ := by
    simpa using (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero : (p : R) ≠ 0)
  rw [dvr_natCast_span_eq_prime_span_pow R p degree degree_nonzero]
  conv_lhs =>
    rw [dvr_ideal_eq_pow_factorCount R (Ideal.span {(p : R)}) prime_nonzero, ← pow_mul,
      dvr_factorCount_pow_maximalIdeal]

end DiscreteValuation

variable [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]

omit [Module.Finite A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)] in
theorem dvr_map_maximalIdeal_eq_pow_ramificationIdx :
    (maximalIdeal A).map (algebraMap A B) =
      maximalIdeal B ^ (maximalIdeal A).ramificationIdx' (maximalIdeal B) := by
  have map_nonzero := Ideal.map_ne_bot_of_ne_bot (S := B) (dvr_maximalIdeal_ne_bot A)
  rw [Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count map_nonzero
    (inferInstance : (maximalIdeal B).IsPrime) (dvr_maximalIdeal_ne_bot B)]
  exact dvr_ideal_eq_pow_factorCount B _ map_nonzero

theorem dvr_different_factorCount_lt_of_degree_not_mem (exponent : ℕ)
    (degree_not_mem : (Module.finrank (FractionRing A) (FractionRing B) : A) ∉
      maximalIdeal A ^ exponent) :
    (normalizedFactors (differentIdeal A B)).count (maximalIdeal B) <
      (maximalIdeal A).ramificationIdx' (maximalIdeal B) * exponent := by
  have obstruction := not_map_dvd_differentIdeal_of_degree_not_mem A B
    (maximalIdeal A ^ exponent) degree_not_mem
  rw [Ideal.map_pow, dvr_map_maximalIdeal_eq_pow_ramificationIdx A B, ← pow_mul]
    at obstruction
  exact dvr_factorCount_lt_of_not_dvd B _ differentIdeal_ne_bot _ obstruction

theorem dvr_different_factorCount_lt_degree_padicVal [CharZero A] (p : ℕ) [Fact p.Prime]
    [CharP (A ⧸ maximalIdeal A) p] :
    (normalizedFactors (differentIdeal A B)).count (maximalIdeal B) <
      (maximalIdeal A).ramificationIdx' (maximalIdeal B) *
        ((normalizedFactors (Ideal.span {(p : A)})).count (maximalIdeal A) *
          padicValNat p (Module.finrank (FractionRing A) (FractionRing B)) + 1) := by
  letI : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  letI : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) (FractionRing B) :=
    IsIntegralClosure.isLocalization A (FractionRing A) (FractionRing B) B
  letI : FiniteDimensional (FractionRing A) (FractionRing B) :=
    .of_isLocalization A B (nonZeroDivisors A)
  have degree_nonzero : Module.finrank (FractionRing A) (FractionRing B) ≠ 0 :=
    Module.finrank_pos.ne'
  apply dvr_different_factorCount_lt_of_degree_not_mem A B
  have degree_not_mem := dvr_not_mem_pow_succ_factorCount A
    (Module.finrank (FractionRing A) (FractionRing B) : A)
    (Nat.cast_ne_zero.mpr degree_nonzero)
  rwa [dvr_natCast_factorCount A p _ degree_nonzero] at degree_not_mem

section Tower

variable (C : Type*) [CommRing C] [IsDedekindDomain C] [IsDiscreteValuationRing C]
  [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [Module.Finite A C] [Module.Finite B C]
  [Module.IsTorsionFree A C] [Module.IsTorsionFree B C]
  [Algebra.IsSeparable (FractionRing A) (FractionRing C)] [CharZero B]
  [(maximalIdeal B).LiesOver (maximalIdeal A)]
  [(maximalIdeal C).LiesOver (maximalIdeal B)]

omit [Algebra.IsSeparable (FractionRing A) (FractionRing B)] in
/-- The normalized different upper bound of IUT IV Proposition 1.3(ii).

The base DVR has uniformizer the rational prime `p` (as for `ℤ_[p]`).
The exponent is the p-adic valuation of the actual fraction-field degree.
The proof applies to all finite separable DVR towers with these hypotheses;
it does not require the paper's additional tame-intermediate/Galois hypothesis. -/
theorem iutIVProp13ii_normalizedDifferent_le (p : ℕ) [Fact p.Prime]
    (prime_generates : Ideal.span {(p : A)} = maximalIdeal A) :
    ((normalizedFactors (differentIdeal A C)).count (maximalIdeal C) : ℝ) /
        (maximalIdeal A).ramificationIdx' (maximalIdeal C) ≤
      ((normalizedFactors (differentIdeal A B)).count (maximalIdeal B) : ℝ) /
          (maximalIdeal A).ramificationIdx' (maximalIdeal B) +
        padicValNat p (Module.finrank (FractionRing B) (FractionRing C)) +
        1 / (maximalIdeal A).ramificationIdx' (maximalIdeal B) := by
  letI : Algebra.IsSeparable (FractionRing B) (FractionRing C) :=
    Algebra.isSeparable_tower_top_of_isSeparable (FractionRing A) _ _
  have prime_mem : (p : B) ∈ maximalIdeal B := by
    have base_mem : (p : A) ∈ maximalIdeal A := by
      rw [← prime_generates]
      exact Ideal.mem_span_singleton_self _
    simpa using (Ideal.mem_of_liesOver (maximalIdeal B) (maximalIdeal A) (p : A)).mp base_mem
  letI : CharP (B ⧸ maximalIdeal B) p :=
    (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
      simpa using (Ideal.Quotient.eq_zero_iff_mem).mpr prime_mem)
  have mapped_prime : (maximalIdeal A).map (algebraMap A B) = Ideal.span {(p : B)} := by
    rw [← prime_generates, Ideal.map_span]
    simp
  have base_index_eq : (maximalIdeal A).ramificationIdx' (maximalIdeal B) =
      (normalizedFactors (Ideal.span {(p : B)})).count (maximalIdeal B) := by
    rw [Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count
      (Ideal.map_ne_bot_of_ne_bot (S := B) (dvr_maximalIdeal_ne_bot A))
      (inferInstance : (maximalIdeal B).IsPrime) (dvr_maximalIdeal_ne_bot B), mapped_prime]
  have raw_bound := dvr_different_factorCount_lt_degree_padicVal B C p
  rw [← base_index_eq] at raw_bound
  let baseIndex := (maximalIdeal A).ramificationIdx' (maximalIdeal B)
  let relativeIndex := (maximalIdeal B).ramificationIdx' (maximalIdeal C)
  let baseOrder := (normalizedFactors (differentIdeal A B)).count (maximalIdeal B)
  let upperOrder := (normalizedFactors (differentIdeal A C)).count (maximalIdeal C)
  let relativeOrder := (normalizedFactors (differentIdeal B C)).count (maximalIdeal C)
  let degreePower := padicValNat p (Module.finrank (FractionRing B) (FractionRing C))
  have base_pos : (0 : ℝ) < baseIndex := by
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver (maximalIdeal B)
        (dvr_maximalIdeal_ne_bot A))
  have relative_pos : (0 : ℝ) < relativeIndex := by
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver (maximalIdeal C)
        (dvr_maximalIdeal_ne_bot B))
  have tower_orders : upperOrder = relativeOrder + relativeIndex * baseOrder :=
    count_differentIdeal_tower A B C (maximalIdeal B) (maximalIdeal C)
      (dvr_maximalIdeal_ne_bot B) (dvr_maximalIdeal_ne_bot C)
  have tower_indices : (maximalIdeal A).ramificationIdx' (maximalIdeal C) =
      baseIndex * relativeIndex :=
    Ideal.ramificationIdx'_algebra_tower' (maximalIdeal A) (maximalIdeal B) (maximalIdeal C)
  have real_bound : (relativeOrder : ℝ) < relativeIndex * (baseIndex * (degreePower : ℝ) + 1) := by
    exact_mod_cast raw_bound
  have relative_bound : (relativeOrder : ℝ) / (baseIndex * relativeIndex) <
      (degreePower : ℝ) + 1 / baseIndex := by
    apply (div_lt_iff₀ (mul_pos base_pos relative_pos)).mpr
    calc
      (relativeOrder : ℝ) < relativeIndex * (baseIndex * (degreePower : ℝ) + 1) := real_bound
      _ = ((degreePower : ℝ) + 1 / baseIndex) * (baseIndex * relativeIndex) := by
        field_simp
  change (upperOrder : ℝ) / (maximalIdeal A).ramificationIdx' (maximalIdeal C) ≤
    (baseOrder : ℝ) / baseIndex + degreePower + 1 / baseIndex
  calc
    (upperOrder : ℝ) / (maximalIdeal A).ramificationIdx' (maximalIdeal C) =
        (baseOrder : ℝ) / baseIndex + (relativeOrder : ℝ) / (baseIndex * relativeIndex) := by
      rw [tower_orders, tower_indices]
      push_cast
      field_simp
      ring
    _ ≤ (baseOrder : ℝ) / baseIndex + degreePower + 1 / baseIndex := by
      linarith

end Tower

end LeanFormal.IUT.IUTIV.Estimates
