import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFractionalAbsorption
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceUnscaledLogTensorLattice
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVRealBound
import LeanFormal.IUT.Foundations.LocalFields.IntegralTraceDualTensorInclusion
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompactHullScaling

/-!
# Step (v) assembly on the actual tuple block: unconditional value-group data

`FinitePlaceNormalizedUnitScalingLogVolume` computes the degree-normalized
log-volume `μ_log((F c) * O_hol) = -(∑ c_i) log p` under the explicit interface
`ArithmeticTuplePureFractionalScalingData`, which isolates the local
value-group bookkeeping `(1/e_i) ℤ`.

This file discharges that interface on the actual tuple block: from any local
generators `g_i` with `‖g_i‖ = p^{-c_i}` it constructs the full data (common
exponent = product of the actual ramification exponents, integer exponents and
norm-one local units from the discrete value group, the trivial action of the
unit tensor on `O_hol`, and `O_tensor · O_hol = O_hol`).  Consequently the
volume formula holds with no hypothesis beyond the existence of exact local
generators.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open MeasureTheory
open LeanFormal.IUT.LocalFieldPadicTensor LeanFormal.IUT.LocalFieldIntegralUnits
open scoped Pointwise

noncomputable section

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)

omit [Fintype ι] in
/-- The norm of an integral power of `p` in a local factor. -/
theorem norm_prime_zpow_commonPrimeCompletion (i : ι) (n : ℤ) :
    ‖(p : CommonPrimeCompletion (places i (tuple i))) ^ n‖ = ‖(p : ℚ_[p])‖ ^ n := by
  rw [norm_zpow, ← map_natCast (algebraMap ℚ_[p] (CommonPrimeCompletion (places i (tuple i))))
    p, norm_algebraMap']

omit [Fintype ι] in
/-- `O_tensor · O_hol = O_hol`. -/
theorem arithmeticTupleValuationIntegerLattice_mul_holomorphicLattice [Finite ι] :
    letI : Fintype ι := Fintype.ofFinite ι
    arithmeticTupleValuationIntegerLattice places tuple *
        arithmeticTupleHolomorphicLattice places tuple =
      arithmeticTupleHolomorphicLattice places tuple := by
  letI : Fintype ι := Fintype.ofFinite ι
  apply le_antisymm
  · refine Submodule.mul_le.mpr fun r hr x hx => ?_
    have hrint : IsIntegral ℤ_[p] r := by
      obtain ⟨J, hJ, E, hfield, halgebra, e, hE, _, _⟩ :=
        exists_arithmeticTensorTuple_fieldProduct places tuple
      letI := hJ
      letI := hfield
      letI := halgebra
      letI : ∀ j, FiniteDimensional ℚ_[p] (E j) := fun j => (hE j).1
      letI : ∀ j, ProperSpace (E j) := fun j => FiniteDimensional.proper ℚ_[p] (E j)
      letI : ∀ j, IsUltrametricDist (E j) := fun j => (hE j).2.2
      exact arithmeticTupleCanonicalUnitReference_subset_integralClosure places tuple
        (arithmeticTupleValuationIntegerLattice_subset_canonicalUnitReference places tuple e hr)
    exact hrint.mul hx
  · intro x hx
    have h1 : (1 : ArithmeticTensorTupleBlock places tuple) ∈
        arithmeticTupleValuationIntegerLattice places tuple := by
      rw [← arithmeticTupleTprod_one places tuple]
      unfold arithmeticTupleValuationIntegerLattice tensorIntegerLattice submoduleTensorSpan
        tensorIntegralRegion
      exact Submodule.subset_span ⟨1, fun i _ => (mem_integers_iff _).mpr (by simp), rfl⟩
    simpa using Submodule.mul_mem_mul h1 hx

omit [Fintype ι] in
/-- A pure tensor of norm-one local elements acts bijectively on `O_hol`. -/
theorem arithmeticTupleTprod_smul_canonicalUnitReference_of_norm_eq_one [Finite ι]
    (u : (i : ι) → CommonPrimeCompletion (places i (tuple i))) (hu : ∀ i, ‖u i‖ = 1) :
    (arithmeticTupleTprod places tuple u) • arithmeticTupleCanonicalUnitReference places tuple =
      arithmeticTupleCanonicalUnitReference places tuple := by
  have hu0 : ∀ i, u i ≠ 0 := fun i h => by simpa [h] using hu i
  have hint : IsIntegral ℤ_[p] (arithmeticTupleTprod places tuple u) :=
    isIntegral_arithmeticTupleTprod_of_norm_le_one places tuple u fun i => (hu i).le
  have hinvint : IsIntegral ℤ_[p] (arithmeticTupleTprod places tuple (fun i => (u i)⁻¹)) :=
    isIntegral_arithmeticTupleTprod_of_norm_le_one places tuple _ fun i => by
      rw [norm_inv, hu i, inv_one]
  have hmul : arithmeticTupleTprod places tuple u *
      arithmeticTupleTprod places tuple (fun i => (u i)⁻¹) = 1 := by
    rw [arithmeticTupleTprod_mul, ← arithmeticTupleTprod_one places tuple]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hu0 i)
  have hO := arithmeticTupleCanonicalUnitReference_eq_integralClosure places tuple
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [hO] at hy ⊢
    exact hint.mul hy
  · intro hx
    refine ⟨arithmeticTupleTprod places tuple (fun i => (u i)⁻¹) * x, ?_, ?_⟩
    · rw [hO] at hx ⊢
      exact hinvint.mul hx
    · change arithmeticTupleTprod places tuple u *
          (arithmeticTupleTprod places tuple (fun i => (u i)⁻¹) * x) = x
      rw [← mul_assoc, hmul, one_mul]

/-- **Unconditional value-group data.**  Exact local generators
`‖g_i‖ = p^{-c_i}` on the actual tuple block determine the full
`ArithmeticTuplePureFractionalScalingData`. -/
def arithmeticTuplePureFractionalScalingData_ofGenerator (c : ι → ℝ)
    (g : (i : ι) → CommonPrimeCompletion (places i (tuple i)))
    (hg : ∀ i, ‖g i‖ = (p : ℝ) ^ (-(c i))) :
    ArithmeticTuplePureFractionalScalingData places tuple c :=
  let e : ι → ℕ := fun i => LocalFieldLogarithm.logShellRamificationExponent
    (K := CommonPrimeCompletion (places i (tuple i))) (p := p)
  let E : ℕ := ∏ i, e i
  have hg0 : ∀ i, g i ≠ 0 := fun i h => by
    have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    have := hg i
    rw [h, norm_zero] at this
    exact (Real.rpow_pos_of_pos hp _).ne' this.symm
  have hn : ∀ i, ∃ n : ℤ, ‖g i‖ ^ E = ‖(p : ℚ_[p])‖ ^ n := fun i =>
    LocalFieldLogarithm.exists_norm_pow_eq_prime_zpow_of_dvd
      (K := CommonPrimeCompletion (places i (tuple i))) (p := p) (g i) (hg0 i)
      (Finset.dvd_prod_of_mem e (Finset.mem_univ i))
  let n : ι → ℤ := fun i => Classical.choose (hn i)
  have hnspec : ∀ i, ‖g i‖ ^ E = ‖(p : ℚ_[p])‖ ^ n i := fun i => Classical.choose_spec (hn i)
  have hpK0 : ∀ i (k : ℤ), (p : CommonPrimeCompletion (places i (tuple i))) ^ k ≠ 0 :=
    fun i k => zpow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hpnorm0 : ‖(p : ℚ_[p])‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  let unit : (i : ι) → CommonPrimeCompletion (places i (tuple i)) :=
    fun i => ((p : CommonPrimeCompletion (places i (tuple i))) ^ n i)⁻¹ * g i ^ E
  have hunit_norm : ∀ i, ‖unit i‖ = 1 := fun i => by
    change ‖((p : CommonPrimeCompletion (places i (tuple i))) ^ n i)⁻¹ * g i ^ E‖ = 1
    rw [norm_mul, norm_inv, norm_prime_zpow_commonPrimeCompletion places tuple i, norm_pow,
      hnspec i, inv_mul_cancel₀ (zpow_ne_zero _ hpnorm0)]
  { localGenerator := g
    localGenerator_norm := hg
    commonExponent := E
    commonExponent_pos := Finset.prod_pos fun i _ =>
      LocalFieldLogarithm.logShellRamificationExponent_pos
        (K := CommonPrimeCompletion (places i (tuple i))) (p := p)
    integerExponent := n
    localUnit := unit
    localUnit_norm := hunit_norm
    localGenerator_pow := fun i => by
      change g i ^ E = (p : CommonPrimeCompletion (places i (tuple i))) ^ n i *
        (((p : CommonPrimeCompletion (places i (tuple i))) ^ n i)⁻¹ * g i ^ E)
      rw [mul_inv_cancel_left₀ (hpK0 i (n i))]
    order_eq := fun i => by
      have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
      have hlogp : Real.log p ≠ 0 := (Real.log_pos hp1).ne'
      have h := congrArg Real.log (hnspec i)
      rw [Real.log_pow, Real.log_zpow, hg i, Real.log_rpow (by linarith), Padic.norm_p,
        Real.log_inv] at h
      have h' : (c i * (E : ℝ) - (n i : ℝ)) * Real.log p = 0 := by linarith
      rcases mul_eq_zero.mp h' with h0 | h0
      · linarith
      · exact absurd h0 hlogp
    unitTensor_action :=
      arithmeticTupleTprod_smul_canonicalUnitReference_of_norm_eq_one places tuple unit
        hunit_norm
    integerTensor_mul_holomorphic := by
      have h := arithmeticTupleValuationIntegerLattice_mul_holomorphicLattice places tuple
      convert h using 3 }

/-- **Exact normalized volume, unconditional form.**  For exact local
generators `‖g_i‖ = p^{-c_i}`,
`μ_log((F c) * O_hol) = -(∑ c_i) log p` (IV Prop 1.4 (i) normalization). -/
theorem arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic_of_generator
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [Measure.IsAddHaarMeasure μ]
    (c : ι → ℝ) (g : (i : ι) → CommonPrimeCompletion (places i (tuple i)))
    (hg : ∀ i, ‖g i‖ = (p : ℝ) ^ (-(c i))) :
    arithmeticTupleNormalizedLogVolume places tuple μ
      ((arithmeticTupleFractionalLattice places tuple c *
        arithmeticTupleHolomorphicLattice places tuple :
          Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)) :
        Set (ArithmeticTensorTupleBlock places tuple)) =
      -((∑ i, c i) * Real.log (p : ℝ)) :=
  arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic places tuple μ
    (arithmeticTuplePureFractionalScalingData_ofGenerator places tuple c g hg)

/-! ## The Step (v) inclusion (IV Prop 1.2 (ii), first inclusion) -/

/-- A chosen uniformizer of the integers of the `i`-th local factor. -/
noncomputable def arithmeticTupleLocalUniformizer (i : ι) :
    Integers (CommonPrimeCompletion (places i (tuple i))) :=
  letI := LocalFieldLogarithm.isDiscreteValuationRingIntegers
    (K := CommonPrimeCompletion (places i (tuple i))) (p := p)
  Classical.choose (IsDiscreteValuationRing.exists_irreducible
    (Integers (CommonPrimeCompletion (places i (tuple i)))))

omit [Fintype ι] in
theorem arithmeticTupleLocalUniformizer_irreducible (i : ι) :
    Irreducible (arithmeticTupleLocalUniformizer places tuple i) :=
  letI := LocalFieldLogarithm.isDiscreteValuationRingIntegers
    (K := CommonPrimeCompletion (places i (tuple i))) (p := p)
  Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible
    (Integers (CommonPrimeCompletion (places i (tuple i)))))

/-- The paper's exponent `a_i` at the `i`-th factor (actual ramification). -/
noncomputable abbrev arithmeticTupleStepVA (i : ι) : ℝ :=
  LocalFieldLogarithm.logShellPaperAExponent p
    (LocalFieldLogarithm.logShellRamificationExponent
      (K := CommonPrimeCompletion (places i (tuple i))) (p := p))

/-- The paper's element `α_i = π_i^{e_i a_i}` (order `a_i`). -/
noncomputable def arithmeticTupleLocalAlpha (i : ι) : CommonPrimeCompletion (places i (tuple i)) :=
  LocalFieldLogarithm.logShellPaperAlphaElement
    ((arithmeticTupleLocalUniformizer places tuple i :
      Integers (CommonPrimeCompletion (places i (tuple i)))) :
        CommonPrimeCompletion (places i (tuple i))) p
    (LocalFieldLogarithm.logShellRamificationExponent
      (K := CommonPrimeCompletion (places i (tuple i))) (p := p))

omit [Fintype ι] in
theorem norm_arithmeticTupleLocalAlpha (i : ι) :
    ‖arithmeticTupleLocalAlpha places tuple i‖ =
      (p : ℝ) ^ (-(arithmeticTupleStepVA places tuple i)) :=
  LocalFieldLogarithm.norm_logShellPaperAlphaElement
    (K := CommonPrimeCompletion (places i (tuple i))) (p := p)
    (arithmeticTupleLocalUniformizer places tuple i)
    (arithmeticTupleLocalUniformizer_irreducible places tuple i)

/-- If `‖x‖ = p^{-a}` then `ord x = a`. -/
theorem localNormOrder_eq_of_norm_eq_rpow {F : Type*} [Norm F] {x : F} {a : ℝ}
    (h : ‖x‖ = (p : ℝ) ^ (-a)) : LocalFieldLogarithm.localNormOrder p x = a := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hlogp : Real.log p ≠ 0 := (Real.log_pos hp1).ne'
  unfold LocalFieldLogarithm.localNormOrder
  rw [h, Real.log_rpow (by linarith)]
  field_simp

/-- `α · O_tensor ⊆ U`: the tensorized lower inclusion of IV Prop 1.2 (i) in
element form, with `U = log_p(R_I^×)` the unscaled unit-log tensor. -/
theorem arithmeticTupleTprod_alpha_mul_mem_unitLogLattice
    {y : ArithmeticTensorTupleBlock places tuple}
    (hy : y ∈ arithmeticTupleValuationIntegerLattice places tuple) :
    arithmeticTupleTprod places tuple (arithmeticTupleLocalAlpha places tuple) * y ∈
      arithmeticTupleUnitLogLattice places tuple := by
  have hgen : ∀ t : (i : ι) → CommonPrimeCompletion (places i (tuple i)),
      (∀ i, ‖t i‖ ≤ 1) →
        arithmeticTupleTprod places tuple (arithmeticTupleLocalAlpha places tuple) *
          arithmeticTupleTprod places tuple t ∈ arithmeticTupleUnitLogLattice places tuple := by
    intro t ht
    rw [arithmeticTupleTprod_mul]
    unfold arithmeticTupleUnitLogLattice submoduleTensorSpan tensorIntegralRegion
    refine Submodule.subset_span ⟨arithmeticTupleLocalAlpha places tuple * t, fun i _ => ?_, rfl⟩
    apply LocalFieldLogarithm.padicFractionalLattice_paperA_le_unitLogLattice
      (K := CommonPrimeCompletion (places i (tuple i))) (p := p)
    rw [LocalFieldLogarithm.mem_padicFractionalLattice_iff, Pi.mul_apply, norm_mul,
      norm_arithmeticTupleLocalAlpha]
    exact mul_le_of_le_one_right (Real.rpow_nonneg (Nat.cast_nonneg p) _) (ht i)
  unfold arithmeticTupleValuationIntegerLattice tensorIntegerLattice submoduleTensorSpan
    tensorIntegralRegion at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨t, ht, rfl⟩ := hz
    exact hgen t fun i => (mem_integers_iff _).mp (ht i (Set.mem_univ i))
  | zero => rw [mul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
  | smul c a _ ha =>
    rw [LeanFormal.IUT.FinitePadicIntegralLattice.padicInteger_smul_eq, mul_smul_comm,
      ← LeanFormal.IUT.FinitePadicIntegralLattice.padicInteger_smul_eq]
    exact Submodule.smul_mem _ c ha

/-- **IUT IV Prop 1.2 (ii), first inclusion, on the actual tuple block.**
Let `ϖ ∈ K_{i†}` be nonzero with `λ = ord ϖ`, let `δ_i` be nonzero local elements
with `δ · O_hol ⊆ R_I` (`δ = ⊗ δ_i`; Prop 1.1 in element form, `d_i = ord δ_i`),
and `a_i` the paper exponents.  For every integer `m ≤ λ - ∑_i (d_i + a_i)`
(e.g. `m = ⌊λ - d_I - a_I⌋`) and every `ℚ_p`-linear automorphism `φ` preserving
`U = log_p(R_I^×)`, `φ(ϖ · O_hol) ⊆ p^m · U`.

The different input `hδ` is Sagan's theorem (namespace
`IntegralTraceDualTensorInclusion`, name ending in
`DifferentGenerator_mul_mem_of_mem_arithmeticTupleCanonicalUnitReference`)
for the actual local different generators (accepted at its build14); it is a
parameter here only because that module does not currently compile. -/
theorem arithmeticTuple_stepV_image_mem_prime_zpow_smul_unitLogLattice [DecidableEq ι]
    (istar : ι) (varpi : CommonPrimeCompletion (places istar (tuple istar)))
    (hvarpi : varpi ≠ 0)
    (delta : (i : ι) → CommonPrimeCompletion (places i (tuple i))) (hδ0 : ∀ i, delta i ≠ 0)
    (hδ : ∀ x ∈ arithmeticTupleCanonicalUnitReference places tuple,
      arithmeticTupleTprod places tuple delta * x ∈
        arithmeticTupleValuationIntegerLattice places tuple)
    (m : ℤ)
    (hm : (m : ℝ) ≤ LocalFieldLogarithm.localNormOrder p varpi -
      ∑ i, (LocalFieldLogarithm.localNormOrder p (delta i) +
        arithmeticTupleStepVA places tuple i))
    (φ : ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
      ArithmeticTensorTupleBlock places tuple)
    (hφ : ∀ u ∈ arithmeticTupleUnitLogLattice places tuple,
      φ u ∈ arithmeticTupleUnitLogLattice places tuple)
    {x : ArithmeticTensorTupleBlock places tuple}
    (hx : x ∈ arithmeticTupleCanonicalUnitReference places tuple) :
    ∃ u ∈ arithmeticTupleUnitLogLattice places tuple,
      φ (arithmeticTupleTprod places tuple (Function.update 1 istar varpi) * x) =
        ((p : ℚ_[p]) ^ m) • u := by
  have hα0 : ∀ i, arithmeticTupleLocalAlpha places tuple i ≠ 0 := fun i h => by
    have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    have := norm_arithmeticTupleLocalAlpha places tuple i
    rw [h, norm_zero] at this
    exact (Real.rpow_pos_of_pos hp _).ne' this.symm
  have hordα : ∀ i,
      LocalFieldLogarithm.localNormOrder p (arithmeticTupleLocalAlpha places tuple i) =
      arithmeticTupleStepVA places tuple i := fun i =>
    localNormOrder_eq_of_norm_eq_rpow (norm_arithmeticTupleLocalAlpha places tuple i)
  have hm' : (m : ℝ) ≤ LocalFieldLogarithm.localNormOrder p varpi -
      ∑ i, (LocalFieldLogarithm.localNormOrder p (arithmeticTupleLocalAlpha places tuple i) +
        LocalFieldLogarithm.localNormOrder p (delta i)) := by
    have hsum : ∑ i,
        (LocalFieldLogarithm.localNormOrder p (arithmeticTupleLocalAlpha places tuple i) +
          LocalFieldLogarithm.localNormOrder p (delta i)) =
        ∑ i, (LocalFieldLogarithm.localNormOrder p (delta i) +
          arithmeticTupleStepVA places tuple i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hordα i, add_comm]
    rw [hsum]
    exact hm
  obtain ⟨r, hr, hfac⟩ := arithmeticTuple_fractionalAbsorption_of_order places tuple istar varpi
    (arithmeticTupleLocalAlpha places tuple) delta
    hvarpi hα0 hδ0 m hm'
  have hO := arithmeticTupleCanonicalUnitReference_eq_integralClosure places tuple
  have hrx : r * x ∈ arithmeticTupleCanonicalUnitReference places tuple := by
    rw [hO] at hr hx ⊢
    exact hr.mul hx
  have hy : arithmeticTupleTprod places tuple delta *
      (r * x) ∈ arithmeticTupleValuationIntegerLattice places tuple :=
    hδ _ hrx
  have hU := arithmeticTupleTprod_alpha_mul_mem_unitLogLattice places tuple hy
  refine ⟨φ (arithmeticTupleTprod places tuple (arithmeticTupleLocalAlpha places tuple) *
    (arithmeticTupleTprod places tuple delta * (r * x))),
    hφ _ hU, ?_⟩
  rw [hfac, smul_mul_assoc, φ.map_smul]
  congr 2
  ring

/-! ## The Step (v) endpoint: `p^m · U ⊆ (p^m β) · O_hol` and its volume -/

/-- The paper's exponent `b_i` at the `i`-th factor (actual ramification). -/
noncomputable abbrev arithmeticTupleStepVB (i : ι) : ℝ :=
  LocalFieldLogarithm.logShellPaperBExponent p
    (LocalFieldLogarithm.logShellRamificationExponent
      (K := CommonPrimeCompletion (places i (tuple i))) (p := p))

/-- The paper's element `β_i` (order `-b_i`). -/
noncomputable def arithmeticTupleLocalBeta (i : ι) : CommonPrimeCompletion (places i (tuple i)) :=
  LocalFieldLogarithm.logShellPaperBetaElement
    ((arithmeticTupleLocalUniformizer places tuple i :
      Integers (CommonPrimeCompletion (places i (tuple i)))) :
        CommonPrimeCompletion (places i (tuple i))) p
    (LocalFieldLogarithm.logShellRamificationExponent
      (K := CommonPrimeCompletion (places i (tuple i))) (p := p))

omit [Fintype ι] in
theorem norm_arithmeticTupleLocalBeta (i : ι) :
    ‖arithmeticTupleLocalBeta places tuple i‖ =
      (p : ℝ) ^ (arithmeticTupleStepVB places tuple i) :=
  LocalFieldLogarithm.norm_logShellPaperBetaElement
    (K := CommonPrimeCompletion (places i (tuple i))) (p := p)
    (arithmeticTupleLocalUniformizer places tuple i)
    (arithmeticTupleLocalUniformizer_irreducible places tuple i)

omit [Fintype ι] in
theorem arithmeticTupleLocalBeta_ne_zero (i : ι) : arithmeticTupleLocalBeta places tuple i ≠ 0 := by
  intro h
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have := norm_arithmeticTupleLocalBeta places tuple i
  rw [h, norm_zero] at this
  exact (Real.rpow_pos_of_pos hp _).ne' this.symm

/-- `U ⊆ β · O_hol`: the tensorized upper inclusion of IV Prop 1.2 (i) in
element form (`β = ⊗ β_i`, `ord β_i = -b_i`). -/
theorem exists_eq_tprod_beta_mul_of_mem_unitLogLattice
    {u : ArithmeticTensorTupleBlock places tuple}
    (hu : u ∈ arithmeticTupleUnitLogLattice places tuple) :
    ∃ y ∈ arithmeticTupleCanonicalUnitReference places tuple,
      u = arithmeticTupleTprod places tuple (arithmeticTupleLocalBeta places tuple) * y := by
  have hO := arithmeticTupleCanonicalUnitReference_eq_integralClosure places tuple
  unfold arithmeticTupleUnitLogLattice submoduleTensorSpan tensorIntegralRegion at hu
  induction hu using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, hl, rfl⟩ := hz
    refine ⟨arithmeticTupleTprod places tuple
      (fun i => l i / arithmeticTupleLocalBeta places tuple i), ?_, ?_⟩
    · apply integralClosure_subset_arithmeticTupleCanonicalUnitReference places tuple
      apply isIntegral_arithmeticTupleTprod_of_norm_le_one places tuple
      intro i
      have h := LocalFieldLogarithm.unitLogLattice_le_padicFractionalLattice_neg_paperB
        (K := CommonPrimeCompletion (places i (tuple i))) (p := p) (hl i (Set.mem_univ i))
      rw [LocalFieldLogarithm.mem_padicFractionalLattice_iff, neg_neg] at h
      rw [norm_div, norm_arithmeticTupleLocalBeta]
      exact div_le_one_of_le₀ h (Real.rpow_nonneg (Nat.cast_nonneg p) _)
    · rw [arithmeticTupleTprod_mul]
      congr 1
      funext i
      change l i = arithmeticTupleLocalBeta places tuple i *
        (l i / arithmeticTupleLocalBeta places tuple i)
      rw [mul_div_cancel₀ _ (arithmeticTupleLocalBeta_ne_zero places tuple i)]
  | zero =>
    refine ⟨0, ?_, (mul_zero _).symm⟩
    rw [hO]
    exact (integralClosure ℤ_[p] (ArithmeticTensorTupleBlock places tuple)).zero_mem
  | add a b _ _ ha hb =>
    obtain ⟨y₁, hy₁, rfl⟩ := ha
    obtain ⟨y₂, hy₂, rfl⟩ := hb
    refine ⟨y₁ + y₂, ?_, (mul_add _ _ _).symm⟩
    rw [hO] at hy₁ hy₂ ⊢
    exact (integralClosure ℤ_[p] (ArithmeticTensorTupleBlock places tuple)).add_mem hy₁ hy₂
  | smul c a _ ha =>
    obtain ⟨y, hy, rfl⟩ := ha
    refine ⟨c • y, ?_, (mul_smul_comm c _ y).symm⟩
    rw [hO] at hy ⊢
    exact (integralClosure ℤ_[p] (ArithmeticTensorTupleBlock places tuple)).smul_mem hy c

/-- The endpoint generator: `β` with the integer power `p^m` placed in the slot
`i†`.  Its pure tensor is the base-field scalar `p^m` times `⊗ β_i`. -/
noncomputable def arithmeticTupleStepVEndpointGenerator [DecidableEq ι] (istar : ι) (m : ℤ)
    (i : ι) : CommonPrimeCompletion (places i (tuple i)) :=
  if i = istar then (p : CommonPrimeCompletion (places i (tuple i))) ^ m *
    arithmeticTupleLocalBeta places tuple i else arithmeticTupleLocalBeta places tuple i

/-- The endpoint exponent vector: `-b_i`, shifted by `m` in the slot `i†`. -/
noncomputable def arithmeticTupleStepVEndpointExponent [DecidableEq ι] (istar : ι) (m : ℤ)
    (i : ι) : ℝ :=
  -arithmeticTupleStepVB places tuple i + if i = istar then (m : ℝ) else 0

omit [Fintype ι] in
theorem norm_arithmeticTupleStepVEndpointGenerator [DecidableEq ι] (istar : ι) (m : ℤ)
    (i : ι) :
    ‖arithmeticTupleStepVEndpointGenerator places tuple istar m i‖ =
      (p : ℝ) ^ (-(arithmeticTupleStepVEndpointExponent places tuple istar m i)) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  unfold arithmeticTupleStepVEndpointGenerator arithmeticTupleStepVEndpointExponent
  split_ifs with hi
  · rw [norm_mul, norm_prime_zpow_commonPrimeCompletion places tuple i,
      norm_arithmeticTupleLocalBeta, Padic.norm_p, inv_zpow', ← Real.rpow_intCast,
      ← Real.rpow_add hp]
    congr 1
    push_cast
    ring
  · rw [norm_arithmeticTupleLocalBeta]
    congr 1
    ring

theorem sum_arithmeticTupleStepVEndpointExponent [DecidableEq ι] (istar : ι) (m : ℤ) :
    ∑ i, arithmeticTupleStepVEndpointExponent places tuple istar m i =
      (m : ℝ) - ∑ i, arithmeticTupleStepVB places tuple i := by
  unfold arithmeticTupleStepVEndpointExponent
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  ring

omit [Fintype ι] in
/-- The endpoint pure tensor is `p^m • ⊗ β_i`. -/
theorem arithmeticTupleTprod_stepVEndpointGenerator [Finite ι] [DecidableEq ι] (istar : ι)
    (m : ℤ) :
    arithmeticTupleTprod places tuple (arithmeticTupleStepVEndpointGenerator places tuple istar m) =
      ((p : ℚ_[p]) ^ m) •
        arithmeticTupleTprod places tuple (arithmeticTupleLocalBeta places tuple) := by
  have hg : arithmeticTupleStepVEndpointGenerator places tuple istar m =
      (fun i => (p : CommonPrimeCompletion (places i (tuple i))) ^ (if i = istar then m else 0)) *
        arithmeticTupleLocalBeta places tuple := by
    funext i
    by_cases hi : i = istar <;> simp [arithmeticTupleStepVEndpointGenerator, hi]
  letI : Fintype ι := Fintype.ofFinite ι
  rw [hg, ← arithmeticTupleTprod_mul]
  have hscalar := arithmeticTupleTprod_prime_zpow_eq_scalar places tuple
    (fun i => if i = istar then m else 0)
  rw [Finset.sum_ite_eq'] at hscalar
  simp only [Finset.mem_univ, if_true] at hscalar
  change finitePadicTensorTprod (p := p) _ _ * _ = _
  rw [hscalar, smul_mul_assoc, one_mul]

/-- **Step (v) container.**  `p^m · U ⊆ (p^m β) · O_hol`. -/
theorem prime_zpow_smul_mem_stepVEndpoint_of_mem_unitLogLattice [DecidableEq ι]
    (istar : ι) (m : ℤ) {u : ArithmeticTensorTupleBlock places tuple}
    (hu : u ∈ arithmeticTupleUnitLogLattice places tuple) :
    ((p : ℚ_[p]) ^ m) • u ∈
      arithmeticTupleTprod places tuple
          (arithmeticTupleStepVEndpointGenerator places tuple istar m) •
        arithmeticTupleCanonicalUnitReference places tuple := by
  obtain ⟨y, hy, rfl⟩ := exists_eq_tprod_beta_mul_of_mem_unitLogLattice places tuple hu
  refine ⟨y, hy, ?_⟩
  change arithmeticTupleTprod places tuple
    (arithmeticTupleStepVEndpointGenerator places tuple istar m) * y = _
  rw [arithmeticTupleTprod_stepVEndpointGenerator, smul_mul_assoc]

/-- **Step (v) volume of the container.**
`μ_log((p^m β) · O_hol) = -(m - ∑ b_i) log p`. -/
theorem arithmeticTupleNormalizedLogVolume_stepVEndpoint [DecidableEq ι]
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [Measure.IsAddHaarMeasure μ]
    (istar : ι) (m : ℤ) :
    arithmeticTupleNormalizedLogVolume places tuple μ
      (arithmeticTupleTprod places tuple
          (arithmeticTupleStepVEndpointGenerator places tuple istar m) •
        arithmeticTupleCanonicalUnitReference places tuple) =
      (-(m : ℝ) + ∑ i, arithmeticTupleStepVB places tuple i) * Real.log p := by
  let data := arithmeticTuplePureFractionalScalingData_ofGenerator places tuple
    (arithmeticTupleStepVEndpointExponent places tuple istar m)
    (arithmeticTupleStepVEndpointGenerator places tuple istar m)
    (norm_arithmeticTupleStepVEndpointGenerator places tuple istar m)
  have hset := arithmeticTupleFractionalLattice_mul_holomorphic_eq_pureGenerator_smul
    places tuple data
  have hvol := arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic
    places tuple μ data
  rw [hset, sum_arithmeticTupleStepVEndpointExponent] at hvol
  rw [show (-(m : ℝ) + ∑ i, arithmeticTupleStepVB places tuple i) * Real.log p =
    -(((m : ℝ) - ∑ i, arithmeticTupleStepVB places tuple i) * Real.log p) by ring]
  exact hvol

/-- **IUT IV Prop 1.4 (iii), second inequality, on the actual tuple block.**
For `m = ⌊λ - ∑ d_i - ∑ a_i⌋`, every set `S` of positive Haar mass inside the
Step (v) container satisfies
`μ_log(S) ≤ (-λ + ∑ d_i + 1) log p + ∑_{i ∈ I*} (3 + log e_i)`,
where `I*` contains every factor with `e_i > p - 2`. -/
theorem arithmeticTupleNormalizedLogVolume_le_stepVPaperBound [DecidableEq ι]
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [Measure.IsAddHaarMeasure μ]
    (istar : ι) (differentOrder : ι → ℝ) (lambda : ℝ) (exceptional : Finset ι)
    (small_outside : ∀ i, i ∉ exceptional →
      LocalFieldLogarithm.logShellRamificationExponent
        (K := CommonPrimeCompletion (places i (tuple i))) (p := p) ≤ p - 2)
    {S : Set (ArithmeticTensorTupleBlock places tuple)} (hSpos : 0 < μ S)
    (hS : S ⊆ arithmeticTupleTprod places tuple
      (arithmeticTupleStepVEndpointGenerator places tuple istar
        ⌊lambda - ∑ i, differentOrder i - ∑ i, arithmeticTupleStepVA places tuple i⌋) •
          arithmeticTupleCanonicalUnitReference places tuple) :
    arithmeticTupleNormalizedLogVolume places tuple μ S ≤
      (-lambda + ∑ i, differentOrder i + 1) * Real.log p +
        ∑ i ∈ exceptional, (3 + Real.log
          (LocalFieldLogarithm.logShellRamificationExponent
            (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : ℝ)) := by
  set m := ⌊lambda - ∑ i, differentOrder i - ∑ i, arithmeticTupleStepVA places tuple i⌋ with hm
  let data := arithmeticTuplePureFractionalScalingData_ofGenerator places tuple
    (arithmeticTupleStepVEndpointExponent places tuple istar m)
    (arithmeticTupleStepVEndpointGenerator places tuple istar m)
    (norm_arithmeticTupleStepVEndpointGenerator places tuple istar m)
  have hset := arithmeticTupleFractionalLattice_mul_holomorphic_eq_pureGenerator_smul
    places tuple data
  have hle := arithmeticTupleNormalizedLogVolume_le_of_subset_fractionalLattice_mul
    places tuple μ data hSpos (by rw [hset]; exact hS)
  rw [sum_arithmeticTupleStepVEndpointExponent] at hle
  have hpaper := stepVPaperLogVolumeBound (Fact.out : p.Prime)
    (fun i => LocalFieldLogarithm.logShellRamificationExponent
      (K := CommonPrimeCompletion (places i (tuple i))) (p := p))
    (fun i => Nat.succ_le_of_lt (LocalFieldLogarithm.logShellRamificationExponent_pos
      (K := CommonPrimeCompletion (places i (tuple i))) (p := p)))
    differentOrder lambda exceptional small_outside
  have hm' : (-(m : ℝ) + ∑ i, arithmeticTupleStepVB places tuple i) * Real.log p ≤
      (-lambda + ∑ i, differentOrder i + 1) * Real.log p +
        ∑ i ∈ exceptional, (3 + Real.log
          (LocalFieldLogarithm.logShellRamificationExponent
            (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : ℝ)) := hpaper
  linarith

/-! ## Unconditional Step (v): actual different generators -/

/-- The actual local different generator `δ_i` of the `i`-th factor; its order
is the paper's `d_i`. -/
noncomputable abbrev arithmeticTupleLocalDifferent (i : ι) :
    CommonPrimeCompletion (places i (tuple i)) :=
  ((IntegralTraceDualTensorInclusion.localDifferentGenerator (p := p)
    (L := CommonPrimeCompletion (places i (tuple i)))) :
      CommonPrimeCompletion (places i (tuple i)))

omit [Fintype ι] in
theorem arithmeticTupleLocalDifferent_ne_zero (i : ι) :
    arithmeticTupleLocalDifferent places tuple i ≠ 0 := by
  intro h
  exact IntegralTraceDualTensorInclusion.localDifferentGenerator_ne_zero (p := p)
    (L := CommonPrimeCompletion (places i (tuple i))) (Subtype.ext h)

open IntegralTraceDualTensorInclusion in
/-- Prop 1.1 in element form for the actual different generators:
`δ · O_hol ⊆ R_I`. -/
theorem arithmeticTupleTprod_localDifferent_mul_mem
    {x : ArithmeticTensorTupleBlock places tuple}
    (hx : x ∈ arithmeticTupleCanonicalUnitReference places tuple) :
    arithmeticTupleTprod places tuple (arithmeticTupleLocalDifferent places tuple) * x ∈
      arithmeticTupleValuationIntegerLattice places tuple :=
  arithmeticTensorDifferentGenerator_mul_mem_of_mem_arithmeticTupleCanonicalUnitReference
    places tuple hx

/-- **IUT IV Theorem 1.10 Step (v), actual tuple block, unconditional.**
Let `ϖ ∈ K_{i†}` be nonzero, `λ = ord ϖ`, `d_i = ord δ_i` for the actual local
different generators, `a_i, b_i` the paper exponents, and
`m = ⌊λ - ∑ d_i - ∑ a_i⌋`.  Let `S` be any set of positive Haar mass contained
in the union of the possible images `φ(ϖ · O_hol)` over a family of
`ℚ_p`-linear automorphisms `φ` preserving `U = log_p(R_I^×)` (the
indeterminacies (Ind1), (Ind2)).  Then
`μ_log(S) ≤ (-λ + ∑ d_i + 1) log p + ∑_{i ∈ I*} (3 + log e_i)`,
where `I*` contains every factor with `e_i > p - 2`. -/
theorem arithmeticTuple_stepV_normalizedLogVolume_le_paperBound [DecidableEq ι]
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [Measure.IsAddHaarMeasure μ]
    (istar : ι) (varpi : CommonPrimeCompletion (places istar (tuple istar)))
    (hvarpi : varpi ≠ 0)
    (Φ : Set (ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
      ArithmeticTensorTupleBlock places tuple))
    (hΦ : ∀ φ ∈ Φ, ∀ u ∈ arithmeticTupleUnitLogLattice places tuple,
      φ u ∈ arithmeticTupleUnitLogLattice places tuple)
    (exceptional : Finset ι)
    (small_outside : ∀ i, i ∉ exceptional →
      LocalFieldLogarithm.logShellRamificationExponent
        (K := CommonPrimeCompletion (places i (tuple i))) (p := p) ≤ p - 2)
    {S : Set (ArithmeticTensorTupleBlock places tuple)} (hSpos : 0 < μ S)
    (hS : ∀ s ∈ S, ∃ φ ∈ Φ, ∃ x ∈ arithmeticTupleCanonicalUnitReference places tuple,
      s = φ (arithmeticTupleTprod places tuple (Function.update 1 istar varpi) * x)) :
    arithmeticTupleNormalizedLogVolume places tuple μ S ≤
      (-LocalFieldLogarithm.localNormOrder p varpi +
          ∑ i, LocalFieldLogarithm.localNormOrder p (arithmeticTupleLocalDifferent places tuple i) +
          1) * Real.log p +
        ∑ i ∈ exceptional, (3 + Real.log
          (LocalFieldLogarithm.logShellRamificationExponent
            (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : ℝ)) := by
  set lam := LocalFieldLogarithm.localNormOrder p varpi
  set d : ι → ℝ := fun i =>
    LocalFieldLogarithm.localNormOrder p (arithmeticTupleLocalDifferent places tuple i)
  set m := ⌊lam - ∑ i, d i - ∑ i, arithmeticTupleStepVA places tuple i⌋ with hmdef
  have hm : (m : ℝ) ≤ lam - ∑ i, (d i + arithmeticTupleStepVA places tuple i) := by
    rw [Finset.sum_add_distrib, ← sub_sub]
    exact Int.floor_le _
  apply arithmeticTupleNormalizedLogVolume_le_stepVPaperBound places tuple μ istar d lam
    exceptional small_outside hSpos
  intro s hs
  obtain ⟨φ, hφ, x, hx, rfl⟩ := hS s hs
  obtain ⟨u, hu, hequ⟩ := arithmeticTuple_stepV_image_mem_prime_zpow_smul_unitLogLattice
    places tuple istar varpi hvarpi (arithmeticTupleLocalDifferent places tuple)
    (arithmeticTupleLocalDifferent_ne_zero places tuple)
    (fun y hy => arithmeticTupleTprod_localDifferent_mul_mem places tuple hy) m hm φ (hΦ φ hφ) hx
  rw [hequ]
  exact prime_zpow_smul_mem_stepVEndpoint_of_mem_unitLogLattice places tuple istar m hu

/-! ## The holomorphic hull of the union of possible images -/

omit [Fintype ι] in
/-- A pure tensor of nonzero local elements is a unit of the tuple block. -/
theorem isUnit_arithmeticTupleTprod (g : (i : ι) → CommonPrimeCompletion (places i (tuple i)))
    (hg : ∀ i, g i ≠ 0) : IsUnit (arithmeticTupleTprod places tuple g) := by
  have h1 : arithmeticTupleTprod places tuple g *
      arithmeticTupleTprod places tuple (fun i => (g i)⁻¹) = 1 := by
    rw [arithmeticTupleTprod_mul, ← arithmeticTupleTprod_one places tuple]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hg i)
  exact ⟨⟨_, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

omit [Fintype ι] in
theorem arithmeticTupleStepVEndpointGenerator_ne_zero [DecidableEq ι] (istar : ι) (m : ℤ)
    (i : ι) : arithmeticTupleStepVEndpointGenerator places tuple istar m i ≠ 0 := by
  unfold arithmeticTupleStepVEndpointGenerator
  split_ifs
  · exact mul_ne_zero (zpow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero))
      (arithmeticTupleLocalBeta_ne_zero places tuple i)
  · exact arithmeticTupleLocalBeta_ne_zero places tuple i

/-- The set of possible images `{φ(ϖ x) : φ ∈ Φ, x ∈ O_hol}` (Ind1/Ind2). -/
def arithmeticTupleStepVPossibleImages [DecidableEq ι] (istar : ι)
    (varpi : CommonPrimeCompletion (places istar (tuple istar)))
    (Φ : Set (ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
      ArithmeticTensorTupleBlock places tuple)) :
    Set (ArithmeticTensorTupleBlock places tuple) :=
  {s | ∃ φ ∈ Φ, ∃ x ∈ arithmeticTupleCanonicalUnitReference places tuple,
    s = φ (arithmeticTupleTprod places tuple (Function.update 1 istar varpi) * x)}

/-- The possible images have positive Haar mass as soon as `Φ` is nonempty:
they contain the open set `(φ₀ ∘ ϖ)(O_hol)`. -/
theorem measure_arithmeticTupleStepVPossibleImages_pos [DecidableEq ι]
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [Measure.IsAddHaarMeasure μ]
    (istar : ι) (varpi : CommonPrimeCompletion (places istar (tuple istar)))
    (hvarpi : varpi ≠ 0)
    (Φ : Set (ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
      ArithmeticTensorTupleBlock places tuple))
    {φ₀ : ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
      ArithmeticTensorTupleBlock places tuple} (hφ₀ : φ₀ ∈ Φ) :
    0 < μ (arithmeticTupleStepVPossibleImages places tuple istar varpi Φ) := by
  have hw0 : ∀ i, (Function.update 1 istar varpi :
      (i : ι) → CommonPrimeCompletion (places i (tuple i))) i ≠ 0 := by
    intro i
    by_cases hi : i = istar
    · subst hi
      simpa using hvarpi
    · simp [Function.update_of_ne hi]
  obtain ⟨wU, hwU⟩ := isUnit_arithmeticTupleTprod places tuple _ hw0
  let O := arithmeticTupleCanonicalUnitReference places tuple
  let T : Set (ArithmeticTensorTupleBlock places tuple) :=
    (fun y => (↑wU⁻¹ : ArithmeticTensorTupleBlock places tuple) * φ₀.symm y) ⁻¹' O
  have hcont : Continuous (fun y : ArithmeticTensorTupleBlock places tuple =>
      (↑wU⁻¹ : ArithmeticTensorTupleBlock places tuple) * φ₀.symm y) :=
    ((LinearMap.mulLeft ℚ_[p]
      (↑wU⁻¹ : ArithmeticTensorTupleBlock places tuple)).continuous_of_finiteDimensional).comp
        φ₀.symm.toLinearMap.continuous_of_finiteDimensional
  have hopen : IsOpen T :=
    (isOpen_arithmeticTupleCanonicalUnitReference places tuple).preimage hcont
  have hO0 : (0 : ArithmeticTensorTupleBlock places tuple) ∈ O := by
    rw [show O = _ from arithmeticTupleCanonicalUnitReference_eq_integralClosure places tuple]
    exact (integralClosure ℤ_[p] (ArithmeticTensorTupleBlock places tuple)).zero_mem
  have hne : T.Nonempty := ⟨0, by simpa [T] using hO0⟩
  have hsub : T ⊆ arithmeticTupleStepVPossibleImages places tuple istar varpi Φ := by
    intro y hy
    refine ⟨φ₀, hφ₀, (↑wU⁻¹ : ArithmeticTensorTupleBlock places tuple) * φ₀.symm y, hy, ?_⟩
    change y = φ₀ (arithmeticTupleTprod places tuple (Function.update 1 istar varpi) *
      ((↑wU⁻¹ : ArithmeticTensorTupleBlock places tuple) * φ₀.symm y))
    rw [← mul_assoc, ← hwU, Units.mul_inv, one_mul, LinearEquiv.apply_symm_apply]
  exact lt_of_lt_of_le (hopen.measure_pos μ hne) (measure_mono hsub)

/-- Every possible image lies in the Step (v) container. -/
theorem arithmeticTupleStepVPossibleImages_subset_endpoint [DecidableEq ι]
    (istar : ι) (varpi : CommonPrimeCompletion (places istar (tuple istar)))
    (hvarpi : varpi ≠ 0)
    (Φ : Set (ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
      ArithmeticTensorTupleBlock places tuple))
    (hΦ : ∀ φ ∈ Φ, ∀ u ∈ arithmeticTupleUnitLogLattice places tuple,
      φ u ∈ arithmeticTupleUnitLogLattice places tuple)
    (m : ℤ)
    (hm : (m : ℝ) ≤ LocalFieldLogarithm.localNormOrder p varpi -
      ∑ i, (LocalFieldLogarithm.localNormOrder p (arithmeticTupleLocalDifferent places tuple i) +
        arithmeticTupleStepVA places tuple i)) :
    arithmeticTupleStepVPossibleImages places tuple istar varpi Φ ⊆
      arithmeticTupleTprod places tuple
          (arithmeticTupleStepVEndpointGenerator places tuple istar m) •
        arithmeticTupleCanonicalUnitReference places tuple := by
  rintro s ⟨φ, hφ, x, hx, rfl⟩
  obtain ⟨u, hu, hequ⟩ := arithmeticTuple_stepV_image_mem_prime_zpow_smul_unitLogLattice
    places tuple istar varpi hvarpi (arithmeticTupleLocalDifferent places tuple)
    (arithmeticTupleLocalDifferent_ne_zero places tuple)
    (fun y hy => arithmeticTupleTprod_localDifferent_mul_mem places tuple hy) m hm φ (hΦ φ hφ) hx
  rw [hequ]
  exact prime_zpow_smul_mem_stepVEndpoint_of_mem_unitLogLattice places tuple istar m hu

section StepVHull

variable {J : Type (max u v)} [Finite J] {E : J → Type (max u v)}
  [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
  [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]

/-- The holomorphic hull of a subset of the tuple block (the smallest `λ · O_hol`
with every component of `λ` nonzero, IUT III Remark 3.9.5), computed in a
field-product decomposition `e`. -/
def arithmeticTupleHolomorphicHull
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (A : Set (ArithmeticTensorTupleBlock places tuple)) :
    Set (ArithmeticTensorTupleBlock places tuple) :=
  e.symm '' LocalFieldProductHull.hull (e '' A)

omit [Fintype ι] [Finite J] [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)] in
theorem subset_arithmeticTupleHolomorphicHull
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (A : Set (ArithmeticTensorTupleBlock places tuple)) :
    A ⊆ arithmeticTupleHolomorphicHull places tuple e A :=
  fun x hx => ⟨e x, LocalFieldProductHull.subset_hull _ ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩

omit [Fintype ι] in
/-- A unit translate of `O_hol` is a coordinate region `λ · O`. -/
theorem smul_canonicalUnitReference_eq_region [Finite ι]
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j))
    {g : ArithmeticTensorTupleBlock places tuple} (hg : IsUnit g) :
    g • arithmeticTupleCanonicalUnitReference places tuple =
      e.symm '' LocalFieldProductHull.region (e g) := by
  letI : Fintype ι := Fintype.ofFinite ι
  have hg' : ∀ j, (e g) j ≠ 0 := fun j => ((Pi.isUnit_iff.mp (hg.map e)) j).ne_zero
  rw [arithmeticTupleCanonicalUnitReference_eq places tuple e,
    arithmeticTupleUnitReferencePullback, LocalFieldProductHull.region_eq_mul_unitRegion _ hg']
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨e g * y, ⟨y, hy, rfl⟩, ?_⟩
    change e.symm (e g * y) = g * e.symm y
    rw [map_mul, AlgEquiv.symm_apply_apply]
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨e.symm y, ⟨y, hy, rfl⟩, ?_⟩
    change g * e.symm y = e.symm (e g * y)
    rw [map_mul, AlgEquiv.symm_apply_apply]

omit [Fintype ι] in
/-- Minimality: a set inside a unit translate of `O_hol` has its holomorphic hull
inside the same translate. -/
theorem arithmeticTupleHolomorphicHull_subset_smul [Finite ι]
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j))
    {A : Set (ArithmeticTensorTupleBlock places tuple)}
    {g : ArithmeticTensorTupleBlock places tuple} (hg : IsUnit g)
    (hA : A ⊆ g • arithmeticTupleCanonicalUnitReference places tuple) :
    arithmeticTupleHolomorphicHull places tuple e A ⊆
      g • arithmeticTupleCanonicalUnitReference places tuple := by
  have hg' : ∀ j, (e g) j ≠ 0 := fun j => ((Pi.isUnit_iff.mp (hg.map e)) j).ne_zero
  rw [smul_canonicalUnitReference_eq_region places tuple e hg] at hA ⊢
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨y, LocalFieldProductHull.hull_minimal hg' ?_ hy, rfl⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨z, hz, hzx⟩ := hA hx
  rw [← hzx, AlgEquiv.apply_symm_apply]
  exact hz

/-- **IUT IV Theorem 1.10 Step (v) on the actual tuple block.**  The
holomorphic hull of the union of possible images `φ(ϖ · O_hol)` (over any
nonempty family `Φ` of `ℚ_p`-linear automorphisms preserving
`U = log_p(R_I^×)`) has degree-normalized log-volume at most
`(-λ + ∑ d_i + 1) log p + ∑_{i ∈ I*} (3 + log e_i)`, with `λ = ord ϖ`,
`d_i = ord δ_i` for the actual different generators, and `I*` containing every
factor with `e_i > p - 2`.  This is the second inequality of IV Prop 1.4 (iii)
with the paper's constants. -/
theorem arithmeticTuple_stepV_hull_normalizedLogVolume_le_paperBound [DecidableEq ι]
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [Measure.IsAddHaarMeasure μ]
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (istar : ι) (varpi : CommonPrimeCompletion (places istar (tuple istar)))
    (hvarpi : varpi ≠ 0)
    (Φ : Set (ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
      ArithmeticTensorTupleBlock places tuple))
    (hΦne : Φ.Nonempty)
    (hΦ : ∀ φ ∈ Φ, ∀ u ∈ arithmeticTupleUnitLogLattice places tuple,
      φ u ∈ arithmeticTupleUnitLogLattice places tuple)
    (exceptional : Finset ι)
    (small_outside : ∀ i, i ∉ exceptional →
      LocalFieldLogarithm.logShellRamificationExponent
        (K := CommonPrimeCompletion (places i (tuple i))) (p := p) ≤ p - 2) :
    arithmeticTupleNormalizedLogVolume places tuple μ
        (arithmeticTupleHolomorphicHull places tuple e
          (arithmeticTupleStepVPossibleImages places tuple istar varpi Φ)) ≤
      (-LocalFieldLogarithm.localNormOrder p varpi +
          ∑ i, LocalFieldLogarithm.localNormOrder p (arithmeticTupleLocalDifferent places tuple i) +
          1) * Real.log p +
        ∑ i ∈ exceptional, (3 + Real.log
          (LocalFieldLogarithm.logShellRamificationExponent
            (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : ℝ)) := by
  set lam := LocalFieldLogarithm.localNormOrder p varpi
  set d : ι → ℝ := fun i =>
    LocalFieldLogarithm.localNormOrder p (arithmeticTupleLocalDifferent places tuple i)
  set m := ⌊lam - ∑ i, d i - ∑ i, arithmeticTupleStepVA places tuple i⌋ with hmdef
  have hm : (m : ℝ) ≤ lam - ∑ i, (d i + arithmeticTupleStepVA places tuple i) := by
    rw [Finset.sum_add_distrib, ← sub_sub]
    exact Int.floor_le _
  obtain ⟨φ₀, hφ₀⟩ := hΦne
  have himg := arithmeticTupleStepVPossibleImages_subset_endpoint places tuple istar varpi
    hvarpi Φ hΦ m hm
  have hunit := isUnit_arithmeticTupleTprod places tuple _
    (arithmeticTupleStepVEndpointGenerator_ne_zero places tuple istar m)
  have hhull := arithmeticTupleHolomorphicHull_subset_smul places tuple e hunit himg
  have hpos : 0 < μ (arithmeticTupleHolomorphicHull places tuple e
      (arithmeticTupleStepVPossibleImages places tuple istar varpi Φ)) :=
    lt_of_lt_of_le
      (measure_arithmeticTupleStepVPossibleImages_pos places tuple μ istar varpi hvarpi Φ hφ₀)
      (measure_mono (subset_arithmeticTupleHolomorphicHull places tuple e _))
  exact arithmeticTupleNormalizedLogVolume_le_stepVPaperBound places tuple μ istar d lam
    exceptional small_outside hpos hhull

end StepVHull

end

end LeanFormal.IUT.NumberFieldFinitePlace
