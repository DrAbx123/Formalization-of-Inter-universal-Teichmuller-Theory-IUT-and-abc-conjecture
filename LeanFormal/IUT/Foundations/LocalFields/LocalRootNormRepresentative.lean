import LeanFormal.IUT.Foundations.LocalFields.LocalDifferentNormOrder

/-!
# Norm representatives for fractional local orders

For an actual nonzero integral element, an n-th root of its norm is realized in
the same integer ring exactly when n divides its DVR order. This constructs a
norm representative, not an algebraic root or a Tate uniformization parameter.
The final theorem gives the j-invariant order required by the numerical Step(v)
bound; divisibility is an explicit arithmetic hypothesis.
-/

namespace LeanFormal.IUT.LocalRootNormRepresentative

open LeanFormal.IUT.LocalFieldIntegralUnits LeanFormal.IUT.LocalFieldLogarithm

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
  [IsUltrametricDist K] [ProperSpace K] [NormedAlgebra ℚ_[p] K]
  [IsDiscreteValuationRing (Integers K)]

/-- The norm of any nonzero integer in terms of its actual DVR order. -/
theorem norm_integer_eq_prime_rpow_neg_order
    (element : Integers K) (nonzero : element ≠ 0) :
    ‖(element : K)‖ = (p : ℝ) ^
      (-((IsDiscreteValuationRing.addVal (Integers K) element).toNat : ℝ) /
        logShellRamificationExponent (K := K) (p := p)) := by
  obtain ⟨uniformizer, irreducible⟩ := IsDiscreteValuationRing.exists_irreducible (Integers K)
  obtain ⟨order, unit, element_eq⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible nonzero irreducible
  have unit_norm : ‖((unit : Integers K) : K)‖ = 1 := by
    have inverse_bound := (↑(unit⁻¹) : Integers K).property
    have unit_bound := (unit : Integers K).property
    change ‖((↑(unit⁻¹) : Integers K) : K)‖ ≤ 1 at inverse_bound
    change ‖((unit : Integers K) : K)‖ ≤ 1 at unit_bound
    have product_norm :
        ‖((unit : Integers K) : K)‖ * ‖((↑(unit⁻¹) : Integers K) : K)‖ = 1 := by
      rw [← norm_mul, ← Subring.coe_mul]
      simp
    nlinarith [mul_le_mul_of_nonneg_left inverse_bound
      (norm_nonneg ((unit : Integers K) : K))]
  rw [IsDiscreteValuationRing.addVal_def _ unit irreducible order element_eq, ENat.toNat_coe,
    element_eq, Subring.coe_mul, Subring.coe_pow, norm_mul, norm_pow, unit_norm, one_mul,
    norm_uniformizer_eq_prime_rpow_inv_ramificationExponent (p := p) uniformizer irreducible]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

include p in
/-- An n-th root of a nonzero integral norm is realizable exactly when its
actual integer valuation is divisible by n. This includes n=0. -/
theorem exists_integral_norm_root_iff_order_dvd
    (element : Integers K) (nonzero : element ≠ 0) (denominator : ℕ) :
    (∃ representative : Integers K, representative ≠ 0 ∧
      ‖(representative : K)‖ ^ denominator = ‖(element : K)‖) ↔
      denominator ∣ (IsDiscreteValuationRing.addVal (Integers K) element).toNat := by
  have prime_pos : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have prime_ne_one : (p : ℝ) ≠ 1 := by exact_mod_cast (Fact.out : p.Prime).ne_one
  have ramification_ne_zero :
      (logShellRamificationExponent (K := K) (p := p) : ℝ) ≠ 0 := by
    exact_mod_cast (logShellRamificationExponent_pos (K := K) (p := p)).ne'
  constructor
  · rintro ⟨representative, representative_nonzero, norm_power⟩
    rw [norm_integer_eq_prime_rpow_neg_order (p := p) representative representative_nonzero,
      norm_integer_eq_prime_rpow_neg_order (p := p) element nonzero,
      ← Real.rpow_mul_natCast prime_pos.le] at norm_power
    have exponent_eq := (Real.rpow_right_inj prime_pos prime_ne_one).mp norm_power
    field_simp at exponent_eq
    refine ⟨(IsDiscreteValuationRing.addVal (Integers K) representative).toNat, ?_⟩
    exact_mod_cast (by nlinarith [exponent_eq] :
      ((IsDiscreteValuationRing.addVal (Integers K) element).toNat : ℝ) =
        denominator * (IsDiscreteValuationRing.addVal (Integers K) representative).toNat)
  · rintro ⟨quotient, order_eq⟩
    obtain ⟨uniformizer, irreducible⟩ :=
      IsDiscreteValuationRing.exists_irreducible (Integers K)
    have representative_nonzero : uniformizer ^ quotient ≠ 0 :=
      pow_ne_zero _ irreducible.ne_zero
    refine ⟨uniformizer ^ quotient, representative_nonzero, ?_⟩
    rw [norm_integer_eq_prime_rpow_neg_order (p := p) _ representative_nonzero,
      norm_integer_eq_prime_rpow_neg_order (p := p) element nonzero,
      irreducible.addVal_pow, ENat.toNat_coe, order_eq,
      ← Real.rpow_mul_natCast prime_pos.le, Nat.cast_mul]
    congr 1
    ring

omit [Fact p.Prime] [IsUltrametricDist K]
    [CharZero K] [CompleteSpace K] [ProperSpace K] [NormedAlgebra ℚ_[p] K]
    [IsDiscreteValuationRing (Integers K)] in
private theorem localNormOrder_natPow (element : K) (exponent : ℕ) :
    localNormOrder p (element ^ exponent) = exponent * localNormOrder p element := by
  simp only [localNormOrder, norm_pow, Real.log_pow]
  ring

omit [Fact p.Prime] [IsUltrametricDist K]
    [CharZero K] [CompleteSpace K] [ProperSpace K] [NormedAlgebra ℚ_[p] K]
    [IsDiscreteValuationRing (Integers K)] in
private theorem localNormOrder_inverse (element : K) :
    localNormOrder p element⁻¹ = -localNormOrder p element := by
  simp only [localNormOrder, norm_inv, Real.log_inv]
  ring

/-- The actual inverse of a large j-value lies in the norm-integer ring. -/
def inverseJInteger (jValue : K) (large_norm : 1 < ‖jValue‖) : Integers K :=
  ⟨jValue⁻¹, by
    change ‖jValue⁻¹‖ ≤ 1
    rw [norm_inv]
    exact (inv_lt_one_of_one_lt₀ large_norm).le⟩

/-- Construct the exact paper order used for the j-th pilot slot, given the
necessary actual DVR divisibility. For Step(v), set denominator = 2*l.
This makes no assertion identifying the representative with a Tate q-root. -/
theorem exists_stepV_j_normOrder_representative
    (jValue : K) (large_norm : 1 < ‖jValue‖)
    (denominator : ℕ) (denominator_pos : 0 < denominator) (label : ℕ)
    (order_divisible : denominator ∣
      (IsDiscreteValuationRing.addVal (Integers K) (inverseJInteger jValue large_norm)).toNat) :
    ∃ representative : K, representative ≠ 0 ∧
      localNormOrder p representative =
        (label : ℝ) ^ 2 * (-localNormOrder p jValue) / denominator := by
  have j_nonzero : jValue ≠ 0 := by
    intro zero_value
    norm_num [zero_value] at large_norm
  have inverse_nonzero : inverseJInteger jValue large_norm ≠ 0 := by
    intro zero_integer
    have zero_field := congrArg (fun x : Integers K ↦ (x : K)) zero_integer
    exact (inv_ne_zero j_nonzero) zero_field
  obtain ⟨root_representative, root_nonzero, norm_power⟩ :=
    (exists_integral_norm_root_iff_order_dvd (p := p)
      (inverseJInteger jValue large_norm) inverse_nonzero denominator).mpr order_divisible
  have field_nonzero : (root_representative : K) ≠ 0 := by
    intro zero_field
    exact root_nonzero (Subtype.ext zero_field)
  have order_power :
      localNormOrder p ((root_representative : K) ^ denominator) =
        localNormOrder p jValue⁻¹ := by
    simpa only [localNormOrder, norm_pow, inverseJInteger] using
      congrArg (fun value : ℝ ↦ -Real.log value / Real.log (p : ℝ)) norm_power
  rw [localNormOrder_natPow, localNormOrder_inverse] at order_power
  have denominator_ne_zero : (denominator : ℝ) ≠ 0 := by
    exact_mod_cast denominator_pos.ne'
  have root_order : localNormOrder p (root_representative : K) =
      (-localNormOrder p jValue) / denominator := by
    apply (eq_div_iff denominator_ne_zero).mpr
    simpa only [mul_comm] using order_power
  refine ⟨(root_representative : K) ^ (label ^ 2), pow_ne_zero _ field_nonzero, ?_⟩
  rw [localNormOrder_natPow, root_order]
  push_cast
  ring

variable {L : Type*} [NormedField L] [CharZero L] [CompleteSpace L]
  [IsUltrametricDist L] [ProperSpace L] [NormedAlgebra ℚ_[p] L]
  [IsDiscreteValuationRing (Integers L)] [NormedAlgebra K L]

open LeanFormal.IUT.LocalDifferentUpperBound

/-- The integer valuation scales by the ratio of the actual absolute
ramification exponents under an isometric local-field inclusion. -/
theorem integer_order_map_mul_ramification
    (element : Integers K) (nonzero : element ≠ 0) :
    (IsDiscreteValuationRing.addVal (Integers L)
        (integersExtensionMap (L := L) element)).toNat *
        logShellRamificationExponent (K := K) (p := p) =
      (IsDiscreteValuationRing.addVal (Integers K) element).toNat *
        logShellRamificationExponent (K := L) (p := p) := by
  have mapped_nonzero : integersExtensionMap (L := L) element ≠ 0 := by
    intro zero_map
    have zero_field := congrArg (fun x : Integers L ↦ (x : L)) zero_map
    change algebraMap K L (element : K) = 0 at zero_field
    apply nonzero
    apply Subtype.ext
    apply (algebraMap K L).injective
    simpa only [Subring.coe_zero, map_zero] using zero_field
  have same_norm : ‖(integersExtensionMap (L := L) element : L)‖ = ‖(element : K)‖ := by
    change ‖algebraMap K L (element : K)‖ = ‖(element : K)‖
    simp only [norm_algebraMap']
  rw [norm_integer_eq_prime_rpow_neg_order (p := p) _ mapped_nonzero,
    norm_integer_eq_prime_rpow_neg_order (p := p) element nonzero] at same_norm
  have prime_pos : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have prime_ne_one : (p : ℝ) ≠ 1 := by exact_mod_cast (Fact.out : p.Prime).ne_one
  have ramification_K_ne_zero :
      (logShellRamificationExponent (K := K) (p := p) : ℝ) ≠ 0 := by
    exact_mod_cast (logShellRamificationExponent_pos (K := K) (p := p)).ne'
  have ramification_L_ne_zero :
      (logShellRamificationExponent (K := L) (p := p) : ℝ) ≠ 0 := by
    exact_mod_cast (logShellRamificationExponent_pos (K := L) (p := p)).ne'
  have exponents_equal := (Real.rpow_right_inj prime_pos prime_ne_one).mp same_norm
  field_simp at exponents_equal
  exact_mod_cast (by nlinarith [exponents_equal] :
    ((IsDiscreteValuationRing.addVal (Integers L)
      (integersExtensionMap (L := L) element)).toNat : ℝ) *
        logShellRamificationExponent (K := K) (p := p) =
      (IsDiscreteValuationRing.addVal (Integers K) element).toNat *
        logShellRamificationExponent (K := L) (p := p))

/-- The extension-field norm-root condition expressed entirely in the base
integer order and the two actual absolute ramification exponents. -/
theorem order_dvd_extension_iff_ramification
    (element : Integers K) (nonzero : element ≠ 0) (denominator : ℕ) :
    denominator ∣ (IsDiscreteValuationRing.addVal (Integers L)
      (integersExtensionMap (L := L) element)).toNat ↔
      denominator * logShellRamificationExponent (K := K) (p := p) ∣
        (IsDiscreteValuationRing.addVal (Integers K) element).toNat *
          logShellRamificationExponent (K := L) (p := p) := by
  rw [← integer_order_map_mul_ramification (p := p) (L := L) element nonzero]
  constructor
  · rintro ⟨quotient, order_eq⟩
    refine ⟨quotient, ?_⟩
    rw [order_eq]
    ring
  · rintro ⟨quotient, order_eq⟩
    refine ⟨quotient, ?_⟩
    apply mul_right_cancel₀ (logShellRamificationExponent_pos (K := K) (p := p)).ne'
    calc
      _ = (denominator * logShellRamificationExponent (K := K) (p := p)) * quotient := order_eq
      _ = _ := by ring

/-- The j-slot norm representative in an extension field. The exact arithmetic
condition is `n*e_K | v_K(J^-1)*e_L`; no actual algebraic root is assumed. -/
theorem exists_stepV_j_normOrder_representative_in_extension
    (jValue : K) (large_norm : 1 < ‖jValue‖)
    (denominator : ℕ) (denominator_pos : 0 < denominator) (label : ℕ)
    (order_divisible : denominator * logShellRamificationExponent (K := K) (p := p) ∣
      (IsDiscreteValuationRing.addVal (Integers K) (inverseJInteger jValue large_norm)).toNat *
        logShellRamificationExponent (K := L) (p := p)) :
    ∃ representative : L, representative ≠ 0 ∧
      localNormOrder p representative =
        (label : ℝ) ^ 2 * (-localNormOrder p jValue) / denominator := by
  have j_nonzero : jValue ≠ 0 := by
    intro zero_value
    norm_num [zero_value] at large_norm
  have inverse_nonzero : inverseJInteger jValue large_norm ≠ 0 := by
    intro zero_integer
    exact (inv_ne_zero j_nonzero)
      (congrArg (fun x : Integers K ↦ (x : K)) zero_integer)
  have large_mapped_norm : 1 < ‖algebraMap K L jValue‖ := by
    simpa only [norm_algebraMap'] using large_norm
  have mapped_inverse : integersExtensionMap (L := L) (inverseJInteger jValue large_norm) =
      inverseJInteger (algebraMap K L jValue) large_mapped_norm := by
    apply Subtype.ext
    change algebraMap K L jValue⁻¹ = (algebraMap K L jValue)⁻¹
    simp
  have mapped_divisible :=
    (order_dvd_extension_iff_ramification (p := p) (L := L)
      (inverseJInteger jValue large_norm) inverse_nonzero denominator).mpr order_divisible
  rw [mapped_inverse] at mapped_divisible
  obtain ⟨representative, representative_nonzero, order_eq⟩ :=
    exists_stepV_j_normOrder_representative (p := p) (algebraMap K L jValue)
      large_mapped_norm denominator denominator_pos label mapped_divisible
  refine ⟨representative, representative_nonzero, ?_⟩
  simpa only [localNormOrder, norm_algebraMap'] using order_eq

end LeanFormal.IUT.LocalRootNormRepresentative
