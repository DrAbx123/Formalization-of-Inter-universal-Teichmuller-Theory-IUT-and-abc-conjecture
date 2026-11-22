import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceHolomorphicIntegralClosure
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIntegerTensorComparison
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellSharpBounds

/-!
# Fractional absorption into the holomorphic integral structure

IUT IV, Proposition 1.2 (ii) (proof, `IV.txt` L540–L556) absorbs the fractional
part of `λ - d_I - a_I` inside the normalization `(R_I)~ = O_hol`:
`p^λ (R_I)~ ⊆ p^m · p^{d_I + a_I} (R_I)~` with `m = ⌊λ - d_I - a_I⌋`.

On the actual tuple tensor block this is an integrality statement about one
element.  Let `y = ⊗ y_i` be a pure tensor whose local norms satisfy
`‖y_i‖^E = ‖p‖^{n_i}` (so `ord y_i = n_i / E`), and let `k : ℤ` with
`k * E ≤ ∑ n_i`.  Then `p^{-k} • y` lies in `O_hol`.

Proof: `(p^{-k} • y)^E = p^{∑ n_i - k E} • ⊗ u_i` with `‖u_i‖ = 1`; the exponent
is a single nonnegative integer because base-field scalars move freely between
tensor slots.  The pure tensor of local integers lies in `O_tensor ⊆ O_hol`,
which is the integral closure of `Zp`; hence the `E`-th power is integral, and
so is the element itself (`IsIntegral.of_pow`).

No per-slot order of the scalar `p^{-k}` is used, no allocation of `p^m` into
pure tensors, and no sign condition on `λ`.  The element-chain corollary
`arithmeticTuple_fractionalAbsorption_elementChain` supplies the inputs `hscale`
and `hr` of the Step (v) assembly
`arithmeticTensorFractionalSingleCoordinateLogShellScalingAssembly_of_element`
whenever `m * E ≤ E λ - E ∑ (a_i + d_i)`, in particular at bad places where
`λ = ord(q^{j²}) > 0`.

`arithmeticTuple_fractionalAbsorption_of_order` states the same in the paper's
normalization `ord(p) = 1` with real orders and no `E`-bookkeeping: for every
integer `m ≤ ord ϖ - ∑ (ord α_i + ord δ_i)`, e.g. `m = ⌊λ - d_I - a_I⌋`.
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

open LeanFormal.IUT.LocalFieldIntegralUnits

section LocalValueGroup

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : ℕ} [Fact p.Prime] [NormedAlgebra ℚ_[p] K]

/-- The `e`-th power of a uniformizer has the norm of `p`. -/
theorem norm_uniformizer_pow_logShellRamificationExponent (π : Integers K)
    (hπ : Irreducible π) :
    ‖(π : K)‖ ^ logShellRamificationExponent (K := K) (p := p) = ‖(p : ℚ_[p])‖ := by
  have he : (0 : ℝ) < (logShellRamificationExponent (K := K) (p := p) : ℝ) := by
    exact_mod_cast logShellRamificationExponent_pos (K := K) (p := p)
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [norm_uniformizer_eq_prime_rpow_inv_ramificationExponent (K := K) (p := p) π hπ,
    Padic.norm_p, ← Real.rpow_natCast, ← Real.rpow_mul hp.le,
    show -(1 / (logShellRamificationExponent (K := K) (p := p) : ℝ)) *
        (logShellRamificationExponent (K := K) (p := p) : ℝ) = -1 by
      field_simp,
    Real.rpow_neg_one]

/-- **Discrete value group on the integers.**  A nonzero integer `y` has
`‖y‖^e = ‖p‖^n` for some natural `n` (`e` the ramification exponent). -/
theorem exists_norm_pow_logShellRamificationExponent_eq_of_integers (y : Integers K)
    (hy : y ≠ 0) :
    ∃ n : ℕ, ‖(y : K)‖ ^ logShellRamificationExponent (K := K) (p := p) =
      ‖(p : ℚ_[p])‖ ^ n := by
  letI : IsDiscreteValuationRing (Integers K) :=
    isDiscreteValuationRingIntegers (K := K) (p := p)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Integers K)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hπ
  refine ⟨n, ?_⟩
  have hcoe : (y : K) = ((u : Integers K) : K) * (π : K) ^ n := by
    have h := congrArg (fun z : Integers K => (z : K)) hu
    simpa [Subring.coe_mul, Subring.coe_pow] using h
  rw [hcoe, norm_mul, norm_unit_eq_one (K := K) u, one_mul, norm_pow, ← pow_mul, mul_comm,
    pow_mul, norm_uniformizer_pow_logShellRamificationExponent (K := K) (p := p) π hπ]

/-- **Discrete value group.**  Every nonzero `x` has `‖x‖^e = ‖p‖^n` for some
integer `n`; i.e. `ord x ∈ (1/e) ℤ` in the normalization `ord p = 1`. -/
theorem exists_norm_pow_logShellRamificationExponent_eq_prime_zpow (x : K) (hx : x ≠ 0) :
    ∃ n : ℤ, ‖x‖ ^ logShellRamificationExponent (K := K) (p := p) =
      ‖(p : ℚ_[p])‖ ^ n := by
  by_cases h : ‖x‖ ≤ 1
  · obtain ⟨n, hn⟩ := exists_norm_pow_logShellRamificationExponent_eq_of_integers
      (K := K) (p := p) ⟨x, (mem_integers_iff x).mpr h⟩ (by
        intro h0
        exact hx (congrArg (fun z : Integers K => (z : K)) h0))
    exact ⟨n, by rw [zpow_natCast]; exact hn⟩
  · have hinv : ‖x⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp h))
    obtain ⟨n, hn⟩ := exists_norm_pow_logShellRamificationExponent_eq_of_integers
      (K := K) (p := p) ⟨x⁻¹, (mem_integers_iff _).mpr hinv⟩ (by
        intro h0
        exact (inv_ne_zero hx) (congrArg (fun z : Integers K => (z : K)) h0))
    refine ⟨-(n : ℤ), ?_⟩
    have hn' : (‖x‖ ^ logShellRamificationExponent (K := K) (p := p))⁻¹ =
        ‖(p : ℚ_[p])‖ ^ n := by
      rw [← inv_pow, ← norm_inv]
      exact hn
    rw [zpow_neg, zpow_natCast, ← hn', inv_inv]

/-- The same for every multiple of the ramification exponent. -/
theorem exists_norm_pow_eq_prime_zpow_of_dvd (x : K) (hx : x ≠ 0) {E : ℕ}
    (hE : logShellRamificationExponent (K := K) (p := p) ∣ E) :
    ∃ n : ℤ, ‖x‖ ^ E = ‖(p : ℚ_[p])‖ ^ n := by
  obtain ⟨n, hn⟩ := exists_norm_pow_logShellRamificationExponent_eq_prime_zpow
    (K := K) (p := p) x hx
  obtain ⟨k, rfl⟩ := hE
  exact ⟨n * k, by rw [pow_mul, hn, ← zpow_natCast, ← zpow_mul]⟩

end LocalValueGroup

/-- The normalized order `ord x = -log_p ‖x‖` (so `ord p = 1`). -/
noncomputable def localNormOrder (p : ℕ) {F : Type*} [Norm F] (x : F) : ℝ :=
  -Real.log ‖x‖ / Real.log p

/-- If `‖x‖^E = ‖p‖^n`, then `E · ord x = n`. -/
theorem natCast_mul_localNormOrder_eq {p : ℕ} [Fact p.Prime] {F : Type*} [Norm F] {x : F}
    {E : ℕ} {n : ℤ} (hx : ‖x‖ ^ E = ‖(p : ℚ_[p])‖ ^ n) :
    (E : ℝ) * localNormOrder p x = n := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hlogp : Real.log p ≠ 0 := (Real.log_pos hp1).ne'
  have hlog := congrArg Real.log hx
  rw [Real.log_pow, Real.log_zpow, Padic.norm_p, Real.log_inv] at hlog
  unfold localNormOrder
  field_simp
  linarith

end LeanFormal.IUT.LocalFieldLogarithm

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldPadicTensor LeanFormal.IUT.LocalFieldProductHull
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped LeanFormal.IUT.FinitePadicIntegralLattice

noncomputable section

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)

/-- The pure tensor of a family of local elements of the tuple block. -/
abbrev arithmeticTupleTprod (x : (i : ι) → CommonPrimeCompletion (places i (tuple i))) :
    ArithmeticTensorTupleBlock places tuple :=
  finitePadicTensorTprod (p := p) (fun i => CommonPrimeCompletion (places i (tuple i))) x

/-- Pure tensors multiply coordinatewise. -/
theorem arithmeticTupleTprod_mul (x y : (i : ι) → CommonPrimeCompletion (places i (tuple i))) :
    arithmeticTupleTprod places tuple x * arithmeticTupleTprod places tuple y =
      arithmeticTupleTprod places tuple (x * y) :=
  PiTensorProduct.tprod_mul_tprod x y

/-- The unit of the tuple block is the pure tensor of units. -/
theorem arithmeticTupleTprod_one :
    arithmeticTupleTprod places tuple 1 = 1 :=
  PiTensorProduct.one_def.symm

/-- Powers of pure tensors are coordinatewise. -/
theorem arithmeticTupleTprod_pow (x : (i : ι) → CommonPrimeCompletion (places i (tuple i)))
    (n : ℕ) :
    arithmeticTupleTprod places tuple x ^ n = arithmeticTupleTprod places tuple (x ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, arithmeticTupleTprod_one]
  | succ n ih => rw [pow_succ, pow_succ, ih, arithmeticTupleTprod_mul]

/-- A pure tensor of local integers is integral over `Zp`: it lies in
`O_tensor ⊆ O_hol`, and `O_hol` is the integral closure of `Zp`. -/
theorem isIntegral_arithmeticTupleTprod_of_norm_le_one [Finite ι]
    (u : (i : ι) → CommonPrimeCompletion (places i (tuple i))) (hu : ∀ i, ‖u i‖ ≤ 1) :
    IsIntegral ℤ_[p] (arithmeticTupleTprod places tuple u) := by
  letI : Fintype ι := Fintype.ofFinite ι
  have hmem : arithmeticTupleTprod places tuple u ∈
      arithmeticTupleValuationIntegerLattice places tuple := by
    unfold arithmeticTupleValuationIntegerLattice tensorIntegerLattice submoduleTensorSpan
      tensorIntegralRegion
    exact Submodule.subset_span ⟨u, fun i _ => (mem_integers_iff _).mpr (hu i), rfl⟩
  obtain ⟨J, hJ, E, hfield, halgebra, e, hE, _, _⟩ :=
    exists_arithmeticTensorTuple_fieldProduct places tuple
  letI := hJ
  letI := hfield
  letI := halgebra
  letI : ∀ j, FiniteDimensional ℚ_[p] (E j) := fun j => (hE j).1
  letI : ∀ j, ProperSpace (E j) := fun j => FiniteDimensional.proper ℚ_[p] (E j)
  letI : ∀ j, IsUltrametricDist (E j) := fun j => (hE j).2.2
  exact arithmeticTupleCanonicalUnitReference_subset_integralClosure places tuple
    (arithmeticTupleValuationIntegerLattice_subset_canonicalUnitReference places tuple e hmem)

/-- A nonnegative integral power of `p`, as a base-field scalar on the tuple
block, is integral over `Zp`. -/
theorem isIntegral_algebraMap_prime_pow (t : ℕ) :
    IsIntegral ℤ_[p] (algebraMap ℚ_[p] (ArithmeticTensorTupleBlock places tuple)
      ((p : ℚ_[p]) ^ t)) := by
  have h : algebraMap ℚ_[p] (ArithmeticTensorTupleBlock places tuple) ((p : ℚ_[p]) ^ t) =
      algebraMap ℤ_[p] (ArithmeticTensorTupleBlock places tuple) ((p : ℤ_[p]) ^ t) := by
    rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (ArithmeticTensorTupleBlock places tuple)
      ((p : ℤ_[p]) ^ t)]
    congr 1
  rw [h]
  exact isIntegral_algebraMap

/-- A finite product of integral powers of `p` is the power with the summed
exponent. -/
theorem prod_prime_zpow (s : Finset ι) (n : ι → ℤ) :
    ∏ i ∈ s, (p : ℚ_[p]) ^ n i = (p : ℚ_[p]) ^ (∑ i ∈ s, n i) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hp0]

/-- **Fractional absorption.**  Let `y = ⊗ y_i` with `‖y_i‖^E = ‖p‖^{n_i}`
(`E > 0`, `n_i ∈ ℤ`, i.e. `ord y_i = n_i / E`).  If `k * E ≤ ∑ n_i`, then
`p^{-k} • y` is integral over `Zp`.  The condition involves only the total
order `∑ n_i / E - k`, never the order of an individual slot. -/
theorem isIntegral_prime_zpow_smul_arithmeticTupleTprod [Fintype ι]
    (y : (i : ι) → CommonPrimeCompletion (places i (tuple i)))
    (E : ℕ) (hE : 0 < E) (n : ι → ℤ) (k : ℤ)
    (hy : ∀ i, ‖y i‖ ^ E = ‖(p : ℚ_[p])‖ ^ n i)
    (hk : k * E ≤ ∑ i, n i) :
    IsIntegral ℤ_[p] (((p : ℚ_[p]) ^ (-k)) • arithmeticTupleTprod places tuple y) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpnorm0 : ‖(p : ℚ_[p])‖ ≠ 0 := norm_ne_zero_iff.mpr hp0
  -- the unit parts `u_i = p^{-n_i} • y_i^E`
  let u : (i : ι) → CommonPrimeCompletion (places i (tuple i)) :=
    fun i => ((p : ℚ_[p]) ^ n i)⁻¹ • (y i) ^ E
  have hu_norm : ∀ i, ‖u i‖ ≤ 1 := by
    intro i
    have h1 : ‖u i‖ = 1 := by
      change ‖((p : ℚ_[p]) ^ n i)⁻¹ • (y i) ^ E‖ = 1
      rw [norm_smul, norm_inv, norm_zpow, norm_pow, hy i]
      exact inv_mul_cancel₀ (zpow_ne_zero _ hpnorm0)
    exact h1.le
  have hyE : y ^ E = fun i => ((p : ℚ_[p]) ^ n i) • u i := by
    funext i
    change y i ^ E = ((p : ℚ_[p]) ^ n i) • (((p : ℚ_[p]) ^ n i)⁻¹ • (y i) ^ E)
    rw [smul_inv_smul₀ (zpow_ne_zero _ hp0)]
  -- the total exponent is a single nonnegative integer
  obtain ⟨t, ht⟩ : ∃ t : ℕ, ∑ i, n i - k * E = t :=
    Int.eq_ofNat_of_zero_le (by linarith)
  have hscalar : ((p : ℚ_[p]) ^ (-k)) ^ E * ∏ i, (p : ℚ_[p]) ^ n i = (p : ℚ_[p]) ^ t := by
    rw [show ((p : ℚ_[p]) ^ (-k)) ^ E = (p : ℚ_[p]) ^ (-k * (E : ℤ)) by
        rw [zpow_mul, zpow_natCast],
      prod_prime_zpow, ← zpow_add₀ hp0,
      show (p : ℚ_[p]) ^ t = (p : ℚ_[p]) ^ (t : ℤ) from (zpow_natCast _ _).symm]
    congr 1
    linarith
  have hpow : (((p : ℚ_[p]) ^ (-k)) • arithmeticTupleTprod places tuple y) ^ E =
      algebraMap ℚ_[p] (ArithmeticTensorTupleBlock places tuple) ((p : ℚ_[p]) ^ t) *
        arithmeticTupleTprod places tuple u := by
    rw [smul_pow, arithmeticTupleTprod_pow, hyE, ← Algebra.smul_def, ← hscalar, mul_smul]
    congr 1
    exact MultilinearMap.map_smul_univ _ _ _
  have hint : IsIntegral ℤ_[p]
      ((((p : ℚ_[p]) ^ (-k)) • arithmeticTupleTprod places tuple y) ^ E) := by
    rw [hpow]
    exact (isIntegral_algebraMap_prime_pow places tuple t).mul
      (isIntegral_arithmeticTupleTprod_of_norm_le_one places tuple u hu_norm)
  exact IsIntegral.of_pow hE hint

/-- Membership form: the absorbed element lies in the canonical holomorphic
unit reference `O_hol = (R_I)~`. -/
theorem prime_zpow_smul_arithmeticTupleTprod_mem_canonicalUnitReference [Fintype ι]
    (y : (i : ι) → CommonPrimeCompletion (places i (tuple i)))
    (E : ℕ) (hE : 0 < E) (n : ι → ℤ) (k : ℤ)
    (hy : ∀ i, ‖y i‖ ^ E = ‖(p : ℚ_[p])‖ ^ n i)
    (hk : k * E ≤ ∑ i, n i) :
    ((p : ℚ_[p]) ^ (-k)) • arithmeticTupleTprod places tuple y ∈
      arithmeticTupleCanonicalUnitReference places tuple :=
  integralClosure_subset_arithmeticTupleCanonicalUnitReference places tuple
    (isIntegral_prime_zpow_smul_arithmeticTupleTprod places tuple y E hE n k hy hk)

theorem ne_zero_of_norm_pow_eq_prime_zpow {F : Type*} [NormedField F] {x : F}
    {E : ℕ} (hE : 0 < E) {n : ℤ} (hx : ‖x‖ ^ E = ‖(p : ℚ_[p])‖ ^ n) : x ≠ 0 := by
  rintro rfl
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [norm_zero, zero_pow hE.ne'] at hx
  exact zpow_ne_zero n (norm_ne_zero_iff.mpr hp0) hx.symm

/-- **Element chain of IV Proposition 1.2 (ii).**  Let `ϖ` in the slot `i†` have
`ord ϖ = Λ / E`, and let `α_i`, `δ_i` have `ord α_i = A_i / E`,
`ord δ_i = D_i / E`.  If `m * E ≤ Λ - ∑ (A_i + D_i)` (i.e.
`m ≤ λ - a_I - d_I`, the paper's global floor bound), then the single-slot
element `ϖ` factors as `p^m • (α · δ · r)` with `α = ⊗ α_i`, `δ = ⊗ δ_i` and
`r ∈ O_hol`.  No sign condition on `λ` is needed. -/
theorem arithmeticTuple_fractionalAbsorption_elementChain [Fintype ι] [DecidableEq ι]
    (istar : ι) (varpi : CommonPrimeCompletion (places istar (tuple istar)))
    (alpha delta : (i : ι) → CommonPrimeCompletion (places i (tuple i)))
    (E : ℕ) (hE : 0 < E) (Λ : ℤ) (A D : ι → ℤ) (m : ℤ)
    (hvarpi : ‖varpi‖ ^ E = ‖(p : ℚ_[p])‖ ^ Λ)
    (halpha : ∀ i, ‖alpha i‖ ^ E = ‖(p : ℚ_[p])‖ ^ A i)
    (hdelta : ∀ i, ‖delta i‖ ^ E = ‖(p : ℚ_[p])‖ ^ D i)
    (hm : m * E ≤ Λ - ∑ i, (A i + D i)) :
    ∃ r ∈ arithmeticTupleCanonicalUnitReference places tuple,
      arithmeticTupleTprod places tuple (Function.update 1 istar varpi) =
        ((p : ℚ_[p]) ^ m) • (arithmeticTupleTprod places tuple alpha *
          arithmeticTupleTprod places tuple delta * r) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hα0 : ∀ i, alpha i ≠ 0 := fun i => ne_zero_of_norm_pow_eq_prime_zpow hE (halpha i)
  have hδ0 : ∀ i, delta i ≠ 0 := fun i => ne_zero_of_norm_pow_eq_prime_zpow hE (hdelta i)
  let w : (i : ι) → CommonPrimeCompletion (places i (tuple i)) := Function.update 1 istar varpi
  let y : (i : ι) → CommonPrimeCompletion (places i (tuple i)) :=
    fun i => w i / (alpha i * delta i)
  let n : ι → ℤ := fun i => (if i = istar then Λ else 0) - A i - D i
  have hw : ∀ i, ‖w i‖ ^ E = ‖(p : ℚ_[p])‖ ^ (if i = istar then Λ else 0) := by
    intro i
    by_cases hi : i = istar
    · subst hi
      simp only [w, Function.update_self, if_true, hvarpi]
    · simp only [w, Function.update_of_ne hi, Pi.one_apply, norm_one, one_pow, if_neg hi,
        zpow_zero]
  have hy : ∀ i, ‖y i‖ ^ E = ‖(p : ℚ_[p])‖ ^ n i := by
    intro i
    have hpn : ‖(p : ℚ_[p])‖ ≠ 0 := norm_ne_zero_iff.mpr hp0
    simp only [y, n, norm_div, norm_mul, div_pow, mul_pow, hw i, halpha i, hdelta i]
    rw [zpow_sub₀ hpn, zpow_sub₀ hpn, div_div]
  have hk : m * E ≤ ∑ i, n i := by
    have hsum : ∑ i, n i = Λ - ∑ i, (A i + D i) := by
      simp only [n, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        Finset.sum_add_distrib]
      ring
    rw [hsum]
    exact hm
  refine ⟨((p : ℚ_[p]) ^ (-m)) • arithmeticTupleTprod places tuple y,
    prime_zpow_smul_arithmeticTupleTprod_mem_canonicalUnitReference places tuple y E hE n m hy hk,
    ?_⟩
  have hprod : alpha * delta * y = w := by
    funext i
    change alpha i * delta i * (w i / (alpha i * delta i)) = w i
    rw [mul_div_cancel₀ _ (mul_ne_zero (hα0 i) (hδ0 i))]
  rw [mul_smul_comm, smul_smul, ← zpow_add₀ hp0, add_neg_cancel, zpow_zero, one_smul,
    arithmeticTupleTprod_mul, arithmeticTupleTprod_mul, hprod]

/-- **Integer scalar through a pure tensor.**  If `γ = ⊗ γ_i` has
`‖γ_i‖^E = ‖p‖^{G_i}` and the integer `c` satisfies `∑ G_i ≤ c * E` (i.e.
`c ≥ ord γ` in every field component), then `p^c = γ · r` with `r ∈ O_hol`.

With `γ = α δ` (orders `a_i + d_i`) this is the integer-scalar form of the
merged Prop 1.1 + 1.2 (i) input: `p^c • O_hol ⊆ α δ O_hol` for every integer
`c ≥ d_I + a_I`.  The factor is the total order; the per-factor statement
`p^{⌈∑ a_i⌉} R_I ⊆ α R_I` is false in general. -/
theorem exists_prime_zpow_eq_arithmeticTupleTprod_mul [Fintype ι]
    (γ : (i : ι) → CommonPrimeCompletion (places i (tuple i)))
    (E : ℕ) (hE : 0 < E) (G : ι → ℤ) (c : ℤ)
    (hγ : ∀ i, ‖γ i‖ ^ E = ‖(p : ℚ_[p])‖ ^ G i)
    (hc : ∑ i, G i ≤ c * E) :
    ∃ r ∈ arithmeticTupleCanonicalUnitReference places tuple,
      algebraMap ℚ_[p] (ArithmeticTensorTupleBlock places tuple) ((p : ℚ_[p]) ^ c) =
        arithmeticTupleTprod places tuple γ * r := by
  have hγ0 : ∀ i, γ i ≠ 0 := fun i => ne_zero_of_norm_pow_eq_prime_zpow hE (hγ i)
  have hinv : ∀ i, ‖(γ i)⁻¹‖ ^ E = ‖(p : ℚ_[p])‖ ^ (-G i) := by
    intro i
    rw [norm_inv, inv_pow, hγ i, zpow_neg]
  have hk : (-c) * E ≤ ∑ i, (-G i) := by
    rw [Finset.sum_neg_distrib]
    linarith
  refine ⟨((p : ℚ_[p]) ^ (-(-c))) • arithmeticTupleTprod places tuple (fun i => (γ i)⁻¹),
    prime_zpow_smul_arithmeticTupleTprod_mem_canonicalUnitReference places tuple
      (fun i => (γ i)⁻¹) E hE (fun i => -G i) (-c) hinv hk, ?_⟩
  have hone : γ * (fun i => (γ i)⁻¹) = 1 := by
    funext i
    exact mul_inv_cancel₀ (hγ0 i)
  rw [neg_neg, mul_smul_comm, arithmeticTupleTprod_mul, hone, arithmeticTupleTprod_one,
    Algebra.algebraMap_eq_smul_one]

/-- Submodule form: for every integer `c` with `∑ G_i ≤ c * E`, the scalar
`p^c` maps `O_hol` into `γ · O_hol`. -/
theorem prime_zpow_smul_mem_arithmeticTupleTprod_mul_canonicalUnitReference [Fintype ι]
    (γ : (i : ι) → CommonPrimeCompletion (places i (tuple i)))
    (E : ℕ) (hE : 0 < E) (G : ι → ℤ) (c : ℤ)
    (hγ : ∀ i, ‖γ i‖ ^ E = ‖(p : ℚ_[p])‖ ^ G i)
    (hc : ∑ i, G i ≤ c * E)
    {x : ArithmeticTensorTupleBlock places tuple}
    (hx : x ∈ arithmeticTupleCanonicalUnitReference places tuple) :
    ∃ z ∈ arithmeticTupleCanonicalUnitReference places tuple,
      ((p : ℚ_[p]) ^ c) • x = arithmeticTupleTprod places tuple γ * z := by
  obtain ⟨r, hr, hrγ⟩ :=
    exists_prime_zpow_eq_arithmeticTupleTprod_mul places tuple γ E hE G c hγ hc
  refine ⟨r * x, ?_, ?_⟩
  · apply integralClosure_subset_arithmeticTupleCanonicalUnitReference places tuple
    exact (arithmeticTupleCanonicalUnitReference_subset_integralClosure places tuple hr).mul
      (arithmeticTupleCanonicalUnitReference_subset_integralClosure places tuple hx)
  · rw [Algebra.smul_def, hrγ, mul_assoc]

/-- **Fractional absorption in the paper's normalization.**  For nonzero
`ϖ ∈ K_{i†}`, `α_i, δ_i ∈ K_i` and every integer
`m ≤ ord ϖ - ∑_i (ord α_i + ord δ_i)` (orders normalized by `ord p = 1`), the
single-slot element `ϖ` factors as `p^m • (⊗ α_i · ⊗ δ_i · r)` with
`r ∈ O_hol = (R_I)~`.

With `ord ϖ = λ`, `ord α_i = a_i`, `ord δ_i = d_i` this is IV Prop 1.2 (ii)'s
`p^λ (R_I)~ ⊆ p^m · p^{d_I + a_I} (R_I)~` for the paper's
`m = ⌊λ - d_I - a_I⌋`.  The common denominator is the product of the actual
ramification exponents; it does not appear in the statement. -/
theorem arithmeticTuple_fractionalAbsorption_of_order [Fintype ι] [DecidableEq ι]
    (istar : ι) (varpi : CommonPrimeCompletion (places istar (tuple istar)))
    (alpha delta : (i : ι) → CommonPrimeCompletion (places i (tuple i)))
    (hvarpi : varpi ≠ 0) (hα : ∀ i, alpha i ≠ 0) (hδ : ∀ i, delta i ≠ 0) (m : ℤ)
    (hm : (m : ℝ) ≤ LocalFieldLogarithm.localNormOrder p varpi -
      ∑ i, (LocalFieldLogarithm.localNormOrder p (alpha i) +
        LocalFieldLogarithm.localNormOrder p (delta i))) :
    ∃ r ∈ arithmeticTupleCanonicalUnitReference places tuple,
      arithmeticTupleTprod places tuple (Function.update 1 istar varpi) =
        ((p : ℚ_[p]) ^ m) • (arithmeticTupleTprod places tuple alpha *
          arithmeticTupleTprod places tuple delta * r) := by
  let e : ι → ℕ := fun i => LocalFieldLogarithm.logShellRamificationExponent
    (K := CommonPrimeCompletion (places i (tuple i))) (p := p)
  obtain ⟨E, hE, hdvd⟩ : ∃ E : ℕ, 0 < E ∧ ∀ i, e i ∣ E :=
    ⟨∏ i, e i, Finset.prod_pos fun i _ =>
      LocalFieldLogarithm.logShellRamificationExponent_pos
        (K := CommonPrimeCompletion (places i (tuple i))) (p := p),
      fun i => Finset.dvd_prod_of_mem e (Finset.mem_univ i)⟩
  obtain ⟨Λ, hΛ⟩ := LocalFieldLogarithm.exists_norm_pow_eq_prime_zpow_of_dvd
    (K := CommonPrimeCompletion (places istar (tuple istar))) (p := p) varpi hvarpi
    (hdvd istar)
  choose A hA using fun i => LocalFieldLogarithm.exists_norm_pow_eq_prime_zpow_of_dvd
    (K := CommonPrimeCompletion (places i (tuple i))) (p := p) (alpha i) (hα i) (hdvd i)
  choose D hD using fun i => LocalFieldLogarithm.exists_norm_pow_eq_prime_zpow_of_dvd
    (K := CommonPrimeCompletion (places i (tuple i))) (p := p) (delta i) (hδ i) (hdvd i)
  refine arithmeticTuple_fractionalAbsorption_elementChain places tuple istar varpi alpha delta
    E hE Λ A D m hΛ hA hD ?_
  have hΛr := LocalFieldLogarithm.natCast_mul_localNormOrder_eq hΛ
  have hAr := fun i => LocalFieldLogarithm.natCast_mul_localNormOrder_eq (hA i)
  have hDr := fun i => LocalFieldLogarithm.natCast_mul_localNormOrder_eq (hD i)
  have hEpos : (0 : ℝ) < (E : ℝ) := by exact_mod_cast hE
  have h1 := mul_le_mul_of_nonneg_left hm hEpos.le
  rw [mul_sub, Finset.mul_sum] at h1
  simp only [mul_add, hΛr, hAr, hDr] at h1
  have key : ((m * (E : ℤ) : ℤ) : ℝ) ≤
      ((Λ - ∑ i, (A i + D i) : ℤ) : ℝ) := by
    push_cast
    linarith [mul_comm (m : ℝ) (E : ℝ)]
  exact_mod_cast key

/-- The paper's real floor bound `m ≤ (Λ - ∑ (A_i + D_i)) / E` is the integer
condition of the element chain. -/
theorem int_mul_le_of_le_div (E : ℕ) (hE : 0 < E) (N m : ℤ)
    (hm : (m : ℝ) ≤ (N : ℝ) / E) : m * E ≤ N := by
  have hE' : (0 : ℝ) < E := by exact_mod_cast hE
  have h := (le_div_iff₀ hE').mp hm
  exact_mod_cast h

end

end LeanFormal.IUT.NumberFieldFinitePlace
