import LeanFormal.IUT.Audit.Status
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionDegree
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.FieldTheory.Separable

/-!
# The three local inputs to `Module.finrank k_v K_w = e * f`

For an extension `k -> K` of number fields and a finite place `place` of `K` above the
contracted place of `k`, the fundamental identity of a finite extension of complete
discretely valued fields computes the local basis degree `Module.finrank k_v K_w` as
the product `e * f` of the ramification index and the residue degree.
`FinitePlaceCompletionDegree` reduces this computation, in Mathlib 4.32.2, to three
named inputs at the completed valuation rings:

* (i) the residue-field isomorphism of the adic completion: the residue field of the
  completed valuation ring of the lower completion is the residue field of the number
  ring at the contracted place, and likewise in the upper half, compatibly with the
  natural maps;
* (ii) the invariance of `Ideal.ramificationIdx'` under adic completion;
* (iii) `Module.Finite O_v O_w`, equivalently the unique-extension statement
  `IsIntegralClosure O_w O_v K_w`.

This file supplies, for each input, the strongest form proved here:

* (i) is proved, unconditionally: the generic residue isomorphism between the residue
  field of `R` at the height-one prime `v` and the residue field of its adic
  completion, for any Dedekind domain `R` and fraction field, then its two
  number-field halves at a finite place, the compatibility square relating them, and
  the consumer form `localInertiaDegree = relativeResidueDegree`.
* (ii) is proved, unconditionally: `localRamificationIndex =
  relativeRamificationIndex`, via `Ideal.ramificationIdx'_spec`, the uniformizer of
  the completed lower valuation, and the valuation scaling of the completed
  valuation-ring map.
* (iii) is reduced exactly: `Module.Finite O_v O_w <-> IsIntegralClosure O_w O_v K_w`
  is proved in both directions, the separability of the extension of completions is
  proved unconditionally, and the two consumer forms
  `finrank_adicCompletion_eq_relativeCompletionDegree_of_moduleFinite` and
  `finrank_adicCompletion_eq_relativeCompletionDegree_of_isIntegralClosure` derive
  the relative completion degree `e * f` from the finiteness input. The finiteness
  itself is not proved here; it is recorded as a pending obligation in the audit
  section, and no declaration of this file postulates it silently.

With (i) and (ii), `localDataAgreesWithPlaceData` holds unconditionally, so the
relative completion degree of the q-pilot normalization chain depends on the single
explicit input of (iii).
-/

set_option maxHeartbeats 3200000
set_option autoImplicit false

open scoped Valued WithZero Topology

namespace LeanFormal.IUT.NumberFieldFinitePlace

section AdicCompletionIntegerValuation

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  (v : IsDedekindDomain.HeightOneSpectrum R)

theorem valued_algebraMap_adicCompletionIntegers (r : R) :
    Valued.v ((algebraMap R (v.adicCompletionIntegers K) r : v.adicCompletionIntegers K) :
        v.adicCompletion K) = v.valuation K (algebraMap R K r) := by
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
  exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v)
    (k := algebraMap R K r)

theorem adicCompletion_algebraMap_injective :
    Function.Injective (algebraMap K (v.adicCompletion K)) := by
  intro x y hxy
  have hzero : (x - y : K) = 0 := by
    refine (Valuation.zero_iff (v.valuation K)).mp ?_
    have hmapsub : ((x - y : K) : v.adicCompletion K) = 0 := by
      have h : algebraMap K (v.adicCompletion K) (x - y) = 0 := by
        rw [map_sub, hxy, sub_self]
      exact h
    have hval : Valued.v ((x - y : K) : v.adicCompletion K) = 0 := by
      rw [hmapsub, map_zero]
    rw [← IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) (k := x - y)]
    exact hval
  exact sub_eq_zero.mp hzero

instance instCharZeroAdicCompletion [CharZero K] : CharZero (v.adicCompletion K) :=
  charZero_of_injective_algebraMap (adicCompletion_algebraMap_injective v)

/-! ### Value-group helpers -/
theorem withZero_exp_neg_one_pow (n : ℕ) :
    WithZero.exp (-1 : ℤ) ^ n = WithZero.exp (-(n : ℤ)) := by
  rw [← WithZero.exp_nsmul]
  congr 1
  simp

theorem withZero_exp_neg_one_lt_one : WithZero.exp (-1 : ℤ) < (1 : ℤᵐ⁰) := by
  rw [← WithZero.exp_zero]
  exact WithZero.exp_lt_exp.mpr (by norm_num)

theorem withZero_le_exp_neg_one_of_lt_one {x : ℤᵐ⁰} (hx : x < 1) :
    x ≤ WithZero.exp (-1) := by
  rcases eq_or_ne x 0 with h0 | h0
  . rw [h0]
    exact zero_le
  . have hlog : WithZero.log x < 0 := by
      rw [← WithZero.exp_lt_exp, WithZero.exp_log h0, WithZero.exp_zero]
      exact hx
    have hle : WithZero.log x ≤ -1 := by omega
    calc x = WithZero.exp (WithZero.log x) := (WithZero.exp_log h0).symm
      _ ≤ WithZero.exp (-1) := WithZero.exp_le_exp.mpr hle

/-! ### The uniformizer of the completed valuation -/
noncomputable def adicCompletion_uniformizer :
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).Uniformizer :=
  Valuation.Uniformizer.mk'
    (x := Classical.choose
      (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective K v (WithZero.exp (-1))))
    (by
      rw [Valuation.IsUniformizer.iff,
        Classical.choose_spec
          (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective K v (WithZero.exp (-1))),
        Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
          (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective K v)]
      exact (Units.val_mk0 _).symm)

theorem uniformizer_valued_eq_exp_neg_one
    (π : (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).Uniformizer) :
    Valued.v (((π.1 : (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).valuationSubring) :
        v.adicCompletion K)) = WithZero.exp (-1) := by
  rw [Valuation.IsUniformizer.val π.2,
    Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective K v)]
  exact Units.val_mk0 _

/-! ### Membership in the maximal ideal -/
theorem mem_maximalIdeal_iff_valued_lt_one (x : v.adicCompletionIntegers K) :
    x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ↔
      Valued.v (x : v.adicCompletion K) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one (v := v)]
  constructor
  . intro hne
    exact lt_of_le_of_ne
      ((IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers R K v).mp x.2)
      hne
  . intro hlt hunit
    exact absurd hunit (ne_of_lt hlt)

/-! ### Powers of the maximal ideal -/
theorem mem_maximalIdeal_pow_iff_valued_le_exp_neg (n : ℕ) (x : v.adicCompletionIntegers K) :
    x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n ↔
      Valued.v (x : v.adicCompletion K) ≤ WithZero.exp (-(n : ℤ)) := by
  let π : (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).Uniformizer := adicCompletion_uniformizer v
  let ϖ : v.adicCompletionIntegers K := π.1
  have hπval : Valued.v ((ϖ : v.adicCompletionIntegers K) : v.adicCompletion K) =
      WithZero.exp (-1) :=
    uniformizer_valued_eq_exp_neg_one v π
  have hpow : WithZero.exp (-1) ^ n = WithZero.exp (-(n : ℤ)) := withZero_exp_neg_one_pow n
  have hgen : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {ϖ} := by
    rw [show IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) =
        IsLocalRing.maximalIdeal
          ((Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).valuationSubring) from rfl]
    exact Valuation.Uniformizer.is_generator π
  have hmain : x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n ↔
      x ∈ Ideal.span {ϖ ^ n} := by
    rw [hgen, ← Ideal.span_singleton_pow]
  rw [hmain, Ideal.mem_span_singleton]
  constructor
  . rintro ⟨c, rfl⟩
    have hc1 : Valued.v (c : v.adicCompletion K) ≤ 1 :=
      (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers R K v).mp c.2
    have hcoe : (((ϖ ^ n * c : v.adicCompletionIntegers K)) :
        v.adicCompletion K) = (ϖ : v.adicCompletion K) ^ n * (c : v.adicCompletion K) := by
      push_cast
      ring
    rw [hcoe, map_mul, map_pow, hπval, hpow]
    exact mul_le_of_le_one_right' hc1
  . intro hx
    have hdiv : Valued.v ((x : v.adicCompletion K) *
        (((ϖ : v.adicCompletion K)) ^ n)⁻¹) ≤ 1 := by
      rw [map_mul, map_inv₀, map_pow, hπval, hpow]
      exact mul_inv_le_one_of_le₀ hx (le_of_lt (WithZero.exp_pos (a := -(n : ℤ))))
    obtain ⟨c, hc⟩ :=
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers K v).exists_of_le_one hdiv
    have hc' : (c : v.adicCompletion K) =
        (x : v.adicCompletion K) * ((ϖ : v.adicCompletion K) ^ n)⁻¹ := hc
    refine ⟨c, ?_⟩
    apply Subtype.ext
    rw [show (((ϖ ^ n * c : v.adicCompletionIntegers K)) :
        v.adicCompletion K) = (ϖ : v.adicCompletion K) ^ n * (c : v.adicCompletion K) from by
      push_cast
      ring]
    rw [hc', ← mul_assoc, mul_comm ((ϖ : v.adicCompletion K) ^ n) (x : v.adicCompletion K),
      mul_assoc, mul_inv_cancel₀ (pow_ne_zero n (Valuation.Uniformizer.ne_zero π)), mul_one]

end AdicCompletionIntegerValuation

/-! ## The residue field of the adic completion -/

section AdicCompletionResidueField

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  (v : IsDedekindDomain.HeightOneSpectrum R)

theorem exists_completion_sub_algebraMap_lt (x : v.adicCompletion K) {γ : ℤᵐ⁰} (hγ : 0 < γ) :
    ∃ y : K, Valued.v (x - algebraMap K (v.adicCompletion K) y) < γ := by
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
  have hball : {z : v.adicCompletion K | Valued.v (z - x) < γ} ∈ 𝓝 x := by
    rw [Valued.mem_nhds]
    refine ⟨Units.mk0 γ₀ hγ₀, fun z hz => ?_⟩
    simp only [Set.mem_setOf_eq] at hz
    rw [Units.val_mk0, Valuation.restrict_lt_iff_lt_embedding] at hz
    rw [hemb] at hz
    exact hz
  have hxclo : x ∈ closure (Set.range (algebraMap K (v.adicCompletion K))) := by
    rw [(IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (K := K) (v := v)).closure_range]
    exact Set.mem_univ x
  obtain ⟨z, hzball, ⟨y, hy⟩⟩ := mem_closure_iff_nhds.mp hxclo _ hball
  refine ⟨y, ?_⟩
  rw [hy]
  rwa [Valuation.map_sub_swap]

theorem exists_residue_eq_algebraMap (x : v.adicCompletionIntegers K) :
    ∃ a : R, IsLocalRing.residue (v.adicCompletionIntegers K)
        (algebraMap R (v.adicCompletionIntegers K) a) =
      IsLocalRing.residue (v.adicCompletionIntegers K) x := by
  obtain ⟨y, hy⟩ := exists_completion_sub_algebraMap_lt v (x : v.adicCompletion K)
    (WithZero.exp_pos (a := -1))
  have hy1 : v.valuation K y ≤ 1 := by
    rw [← IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) (k := y)]
    have hsplit : (y : v.adicCompletion K) =
        ((y : v.adicCompletion K) - (x : v.adicCompletion K)) + (x : v.adicCompletion K) := by
      ring
    rw [hsplit]
    refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)
    . rw [Valuation.map_sub_swap]
      exact le_of_lt (lt_trans hy withZero_exp_neg_one_lt_one)
    . exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers R K v).mp x.2
  obtain ⟨a, ha⟩ := IsDedekindDomain.HeightOneSpectrum.exists_valuation_sub_lt_of_integer v hy1
    (Units.mk0 (WithZero.exp (-1)) WithZero.exp_ne_zero)
  have ha' : v.valuation K (algebraMap R K a - y) < WithZero.exp (-1) := by
    simpa only [Units.val_mk0] using ha
  refine ⟨a, ?_⟩
  have hmem : x - algebraMap R (v.adicCompletionIntegers K) a ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
    rw [mem_maximalIdeal_iff_valued_lt_one v]
    rw [show ((x - algebraMap R (v.adicCompletionIntegers K) a : v.adicCompletionIntegers K) :
        v.adicCompletion K) =
        (x : v.adicCompletion K) -
          ((algebraMap R (v.adicCompletionIntegers K) a : v.adicCompletionIntegers K) :
            v.adicCompletion K) from by push_cast; ring]
    rw [show ((algebraMap R (v.adicCompletionIntegers K) a : v.adicCompletionIntegers K) :
        v.adicCompletion K) =
        algebraMap K (v.adicCompletion K) (algebraMap R K a) from by
      rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
        IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
      rfl]
    rw [Valuation.map_sub_swap]
    have hsplit : algebraMap K (v.adicCompletion K) (algebraMap R K a) - (x : v.adicCompletion K) =
        (algebraMap K (v.adicCompletion K) y - (x : v.adicCompletion K)) +
          (algebraMap K (v.adicCompletion K) (algebraMap R K a) -
            algebraMap K (v.adicCompletion K) y) := by ring
    rw [hsplit]
    have hbound : Valued.v ((algebraMap K (v.adicCompletion K) y - (x : v.adicCompletion K)) +
        (algebraMap K (v.adicCompletion K) (algebraMap R K a) -
          algebraMap K (v.adicCompletion K) y)) < WithZero.exp (-1) := by
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
      . rw [Valuation.map_sub_swap]
        exact hy
      . rw [← map_sub]
        exact lt_of_eq_of_lt
          (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v)
            (k := algebraMap R K a - y)) ha'
    exact lt_trans hbound (withZero_exp_neg_one_lt_one)
  have hzero : IsLocalRing.residue (v.adicCompletionIntegers K)
      (x - algebraMap R (v.adicCompletionIntegers K) a) = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr hmem
  have hsub : IsLocalRing.residue (v.adicCompletionIntegers K) x -
      IsLocalRing.residue (v.adicCompletionIntegers K)
        (algebraMap R (v.adicCompletionIntegers K) a) = 0 := by
    rw [← map_sub]
    exact hzero
  exact (sub_eq_zero.mp hsub).symm

/-! ### Approximation of residue classes by elements of the number ring -/

noncomputable def adicCompletionReduction (x : v.adicCompletionIntegers K) : R :=
  Classical.choose (exists_residue_eq_algebraMap v x)

theorem adicCompletionReduction_residue (x : v.adicCompletionIntegers K) :
    IsLocalRing.residue (v.adicCompletionIntegers K)
        (algebraMap R (v.adicCompletionIntegers K) (adicCompletionReduction v x)) =
      IsLocalRing.residue (v.adicCompletionIntegers K) x :=
  Classical.choose_spec (exists_residue_eq_algebraMap v x)

theorem adicCompletionReduction_sub_mem (x : v.adicCompletionIntegers K) :
    algebraMap R (v.adicCompletionIntegers K) (adicCompletionReduction v x) - x ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
  have hzero : IsLocalRing.residue (v.adicCompletionIntegers K)
      (algebraMap R (v.adicCompletionIntegers K) (adicCompletionReduction v x) - x) = 0 := by
    rw [map_sub, adicCompletionReduction_residue v x, sub_self]
  exact (IsLocalRing.residue_eq_zero_iff _).mp hzero

noncomputable def adicCompletionResidueQuotientHom :
    (R ⧸ v.asIdeal) →+*
      (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) :=
  Ideal.Quotient.lift v.asIdeal
    ((Ideal.Quotient.mk _).comp (algebraMap R (v.adicCompletionIntegers K)))
    (by
      intro r hr
      show Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
        (algebraMap R (v.adicCompletionIntegers K) r) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, mem_maximalIdeal_iff_valued_lt_one v,
        valued_algebraMap_adicCompletionIntegers v r]
      exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) (v := v) r).mpr hr)

theorem adicCompletionResidueQuotientHom_mk (r : R) :
    adicCompletionResidueQuotientHom v (Ideal.Quotient.mk v.asIdeal r) =
      Ideal.Quotient.mk _ (algebraMap R (v.adicCompletionIntegers K) r) := by
  simp only [adicCompletionResidueQuotientHom, Ideal.Quotient.lift_mk, RingHom.comp_apply]

theorem adicCompletionResidueQuotientHom_injective :
    Function.Injective (adicCompletionResidueQuotientHom (K := K) v) := by
  intro x y h
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [adicCompletionResidueQuotientHom_mk, adicCompletionResidueQuotientHom_mk] at h
  refine Ideal.Quotient.eq.mpr ?_
  have hmem : algebraMap R (v.adicCompletionIntegers K) (a - b) ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
    rw [map_sub]
    exact Ideal.Quotient.eq.mp h
  have hlt : v.valuation K (algebraMap R K (a - b)) < 1 := by
    rw [← valued_algebraMap_adicCompletionIntegers v (a - b)]
    exact (mem_maximalIdeal_iff_valued_lt_one v
      (algebraMap R (v.adicCompletionIntegers K) (a - b))).mp hmem
  exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) (v := v) (a - b)).mp hlt

theorem adicCompletionResidueQuotientHom_surjective :
    Function.Surjective (adicCompletionResidueQuotientHom (K := K) v) := by
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨Ideal.Quotient.mk v.asIdeal (adicCompletionReduction v x), ?_⟩
  rw [adicCompletionResidueQuotientHom_mk]
  exact Ideal.Quotient.eq.mpr (adicCompletionReduction_sub_mem v x)

noncomputable def adicCompletionResidueQuotientEquiv :
    (R ⧸ v.asIdeal) ≃+*
      (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) :=
  RingEquiv.ofBijective (adicCompletionResidueQuotientHom v)
    ⟨adicCompletionResidueQuotientHom_injective v, adicCompletionResidueQuotientHom_surjective v⟩

end AdicCompletionResidueField

/-! ## The three local inputs at the completed valuation rings

The named inputs to `Module.finrank k_v K_w = e * f` for a finite-place extension
`k -> K` are resolved here in consumer form:

* the residue-field isomorphism of the adic completion, in both halves, together with
  the compatibility square needed to transport `finrank` of residue fields;
* the invariance of `Ideal.ramificationIdx'` under adic completion;
* the exact reduction of `Module.Finite O_v O_w` to the unique-extension statement
  `IsIntegralClosure O_w O_v K_w`, with separability proved unconditionally.
-/

universe u v

section NumberFieldLocalInputs

variable {k : Type u} {K : Type v}
  [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

variable (place : NumberField.FinitePlace K)

/-- On elements of the base field, the completion map is the algebra map between the
two completed fields, expressed through the `k`-algebra structures on the
completions. -/
theorem completionMap_algebraMap_eq (y : k) :
    completionMap (k := k) place
        (algebraMap k ((comap (k := k) place).maximalIdeal.adicCompletion k) y) =
      algebraMap k (place.maximalIdeal.adicCompletion K) y :=
  completionMap_coe (k := k) place y

/-- Every element of the maximal ideal of the completed lower valuation ring is sent
by the completed valuation-ring map into the `e`-th power of the maximal ideal of
the completed upper valuation ring, where `e` is the relative ramification index. -/
theorem valued_completionIntegersMap_le_exp_neg_relativeRamificationIndex
    {x : (comap (k := k) place).maximalIdeal.adicCompletionIntegers k}
    (hx : x ∈ IsLocalRing.maximalIdeal
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)) :
    Valued.v (((completionIntegersMap (k := k) place x) :
        place.maximalIdeal.adicCompletionIntegers K) :
      place.maximalIdeal.adicCompletion K) ≤
      WithZero.exp (-(relativeRamificationIndex (k := k) place : ℤ)) := by
  have hxlt : Valued.v
      ((x : (comap (k := k) place).maximalIdeal.adicCompletion k)) < 1 :=
    (mem_maximalIdeal_iff_valued_lt_one (K := k)
      (v := (comap (k := k) place).maximalIdeal) x).mp hx
  rw [coe_completionIntegersMap]
  rw [← valuation_completionMap (k := k) place]
  exact (pow_le_pow_left₀ zero_le
    (withZero_le_exp_neg_one_of_lt_one hxlt)
    (relativeRamificationIndex (k := k) place)).trans_eq
    (withZero_exp_neg_one_pow (relativeRamificationIndex (k := k) place))

/-- The maximal ideal of the completed upper valuation ring lies over the maximal
ideal of the completed lower valuation ring, for the algebra structure induced by the
completed valuation-ring map. -/
instance liesOver_maximalIdeal_adicCompletionIntegers :
    (IsLocalRing.maximalIdeal (place.maximalIdeal.adicCompletionIntegers K)).LiesOver
      (IsLocalRing.maximalIdeal
        ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)) where
  over := le_antisymm
    (by
      intro x hx
      rw [Ideal.mem_comap, algebraMap_instAlgebraAdicCompletionIntegers]
      refine (mem_maximalIdeal_iff_valued_lt_one (K := K) (v := place.maximalIdeal)
        (completionIntegersMap (k := k) place x)).mpr ?_
      refine lt_of_le_of_lt
        (valued_completionIntegersMap_le_exp_neg_relativeRamificationIndex (k := k) place hx) ?_
      rw [← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (by
        have he := relativeRamificationIndex_ne_zero (k := k) place
        omega))
    (by
      refine IsLocalRing.le_maximalIdeal ?_
      intro htop
      have h1 : (1 : (comap (k := k) place).maximalIdeal.adicCompletionIntegers k) ∈
          (IsLocalRing.maximalIdeal (place.maximalIdeal.adicCompletionIntegers K)).under
            ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k) := by
        rw [htop]
        exact Submodule.mem_top
      rw [Ideal.under_def] at h1
      rw [Ideal.mem_comap, map_one] at h1
      exact (IsLocalRing.maximalIdeal.isMaximal
        (place.maximalIdeal.adicCompletionIntegers K)).ne_top
        ((Ideal.eq_top_iff_one _).mpr h1))

/-- The completed valuation-ring map agrees with the number-ring map on elements
coming from the lower number ring: both embeddings of `𝓞 k` in `K_w` coincide. -/
theorem completionIntegersMap_eq_numberRingIntegersMap
    (r : NumberField.RingOfIntegers k) :
    completionIntegersMap (k := k) place
        (algebraMap (NumberField.RingOfIntegers k)
          ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k) r) =
      algebraMap (NumberField.RingOfIntegers K)
        (place.maximalIdeal.adicCompletionIntegers K)
        (algebraMap (NumberField.RingOfIntegers k) (NumberField.RingOfIntegers K) r) := by
  apply Subtype.ext
  rw [coe_completionIntegersMap]
  rw [show ((algebraMap (NumberField.RingOfIntegers k)
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k) r :
        (comap (k := k) place).maximalIdeal.adicCompletionIntegers k) :
        (comap (k := k) place).maximalIdeal.adicCompletion k) =
      algebraMap k ((comap (k := k) place).maximalIdeal.adicCompletion k)
        (algebraMap (NumberField.RingOfIntegers k) k r) from by
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
      IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
    rfl]
  rw [show ((algebraMap (NumberField.RingOfIntegers K)
      (place.maximalIdeal.adicCompletionIntegers K)
      (algebraMap (NumberField.RingOfIntegers k) (NumberField.RingOfIntegers K) r) :
        place.maximalIdeal.adicCompletionIntegers K) :
        place.maximalIdeal.adicCompletion K) =
      algebraMap K (place.maximalIdeal.adicCompletion K)
        (algebraMap (NumberField.RingOfIntegers K) K
          (algebraMap (NumberField.RingOfIntegers k) (NumberField.RingOfIntegers K) r)) from by
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
      IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
    rfl]
  rw [completionMap_algebraMap_eq (k := k) place
    (algebraMap (NumberField.RingOfIntegers k) k r)]
  rw [IsScalarTower.algebraMap_apply k K (place.maximalIdeal.adicCompletion K)
    (algebraMap (NumberField.RingOfIntegers k) k r)]
  congr 1

/-- The residue field of the completed upper valuation ring is the residue field of
the upper number ring at the place. -/
noncomputable def residueEquivAdicCompletionIntegers :
    (NumberField.RingOfIntegers K ⧸ place.maximalIdeal.asIdeal) ≃+*
      (place.maximalIdeal.adicCompletionIntegers K ⧸
        IsLocalRing.maximalIdeal (place.maximalIdeal.adicCompletionIntegers K)) :=
  adicCompletionResidueQuotientEquiv (v := place.maximalIdeal) (K := K)

/-- The residue field of the completed lower valuation ring is the residue field of
the lower number ring at the contracted place. -/
noncomputable def residueEquivAdicCompletionIntegers_comap :
    (NumberField.RingOfIntegers k ⧸ (comap (k := k) place).maximalIdeal.asIdeal) ≃+*
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k ⧸
        IsLocalRing.maximalIdeal
          ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)) :=
  adicCompletionResidueQuotientEquiv (v := (comap (k := k) place).maximalIdeal) (K := k)

/-- The two residue-field isomorphisms of the adic completion are compatible with the
natural algebra maps on the residue fields: the square commutes. -/
theorem residueEquivAdicCompletion_compat :
    (algebraMap
        (((comap (k := k) place).maximalIdeal.adicCompletionIntegers k ⧸
          IsLocalRing.maximalIdeal
            ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)))
        ((place.maximalIdeal.adicCompletionIntegers K ⧸
          IsLocalRing.maximalIdeal (place.maximalIdeal.adicCompletionIntegers K)))).comp
        (residueEquivAdicCompletionIntegers_comap (k := k) place).toRingHom =
      (residueEquivAdicCompletionIntegers place).toRingHom.comp
        (algebraMap
          (NumberField.RingOfIntegers k ⧸ (comap (k := k) place).maximalIdeal.asIdeal)
          (NumberField.RingOfIntegers K ⧸ place.maximalIdeal.asIdeal)) := by
  ext x
  simp only [RingHom.comp_apply]
  have hlower : (residueEquivAdicCompletionIntegers_comap (k := k) place).toRingHom
      (Ideal.Quotient.mk (comap (k := k) place).maximalIdeal.asIdeal x) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal
        ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k))
        (algebraMap (NumberField.RingOfIntegers k)
          ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k) x) :=
    adicCompletionResidueQuotientHom_mk (K := k)
      (v := (comap (k := k) place).maximalIdeal) x
  have hupper : (residueEquivAdicCompletionIntegers place).toRingHom
      (Ideal.Quotient.mk place.maximalIdeal.asIdeal
        (algebraMap (NumberField.RingOfIntegers k) (NumberField.RingOfIntegers K) x)) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal
        (place.maximalIdeal.adicCompletionIntegers K))
        (algebraMap (NumberField.RingOfIntegers K)
          (place.maximalIdeal.adicCompletionIntegers K)
          (algebraMap (NumberField.RingOfIntegers k) (NumberField.RingOfIntegers K) x)) :=
    adicCompletionResidueQuotientHom_mk (K := K) (v := place.maximalIdeal) _
  rw [hlower, Ideal.Quotient.algebraMap_mk_of_liesOver (P := place.maximalIdeal.asIdeal)
    (p := (comap (k := k) place).maximalIdeal.asIdeal)]
  rw [hupper]
  refine congrArg (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
    (place.maximalIdeal.adicCompletionIntegers K))) ?_
  simpa only [algebraMap_instAlgebraAdicCompletionIntegers] using
    completionIntegersMap_eq_numberRingIntegersMap (k := k) place x

/-- **(i) The local inertia degree is the relative residue degree.** Residue-field
isomorphism of the adic completion, in consumer form: the inertia degree of the
completed valuation rings equals the library residue degree `f` of the finite-place
extension. -/
theorem localInertiaDegree_eq_relativeResidueDegree :
    localInertiaDegree (k := k) place = relativeResidueDegree (k := k) place := by
  have hrel : relativeResidueDegree (k := k) place =
      Module.finrank
        (NumberField.RingOfIntegers k ⧸ (comap (k := k) place).maximalIdeal.asIdeal)
        (NumberField.RingOfIntegers K ⧸ place.maximalIdeal.asIdeal) :=
    Ideal.inertiaDeg'_algebraMap _ _
  have hloc : localInertiaDegree (k := k) place = Module.finrank
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k ⧸
        IsLocalRing.maximalIdeal
          ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k))
      (place.maximalIdeal.adicCompletionIntegers K ⧸
        IsLocalRing.maximalIdeal (place.maximalIdeal.adicCompletionIntegers K)) :=
    Ideal.inertiaDeg'_algebraMap _ _
  rw [hloc, hrel]
  exact (Algebra.finrank_eq_of_equiv_equiv
    (residueEquivAdicCompletionIntegers_comap (k := k) place)
    (residueEquivAdicCompletionIntegers place)
    (residueEquivAdicCompletion_compat (k := k) place)).symm

/-- **(ii) The local ramification index is the relative ramification index.**
`Ideal.ramificationIdx'` is invariant under adic completion. -/
theorem localRamificationIndex_eq_relativeRamificationIndex :
    localRamificationIndex (k := k) place = relativeRamificationIndex (k := k) place := by
  have hmap_le : Ideal.map
      (algebraMap ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
        (place.maximalIdeal.adicCompletionIntegers K))
      (IsLocalRing.maximalIdeal
        ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)) ≤
      IsLocalRing.maximalIdeal (place.maximalIdeal.adicCompletionIntegers K) ^
        relativeRamificationIndex (k := k) place := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, algebraMap_instAlgebraAdicCompletionIntegers]
    exact (mem_maximalIdeal_pow_iff_valued_le_exp_neg (K := K) (v := place.maximalIdeal)
      (relativeRamificationIndex (k := k) place)
      (completionIntegersMap (k := k) place x)).mpr
      (valued_completionIntegersMap_le_exp_neg_relativeRamificationIndex (k := k) place hx)
  have hmap_gt : ¬ Ideal.map
      (algebraMap ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
        (place.maximalIdeal.adicCompletionIntegers K))
      (IsLocalRing.maximalIdeal
        ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)) ≤
      IsLocalRing.maximalIdeal (place.maximalIdeal.adicCompletionIntegers K) ^
        (relativeRamificationIndex (k := k) place + 1) := by
    intro hpow
    let pi : (Valued.v : Valuation
        (((comap (k := k) place).maximalIdeal).adicCompletion k) ℤᵐ⁰).Uniformizer :=
      adicCompletion_uniformizer ((comap (k := k) place).maximalIdeal)
    let varpi : ((comap (k := k) place).maximalIdeal).adicCompletionIntegers k := pi.1
    have hvarpi : Valued.v ((varpi :
        ((comap (k := k) place).maximalIdeal).adicCompletionIntegers k) :
        (comap (k := k) place).maximalIdeal.adicCompletion k) = WithZero.exp (-1) :=
      uniformizer_valued_eq_exp_neg_one _ pi
    have hvarpi_mem : varpi ∈ IsLocalRing.maximalIdeal
        ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k) :=
      (mem_maximalIdeal_iff_valued_lt_one (K := k)
        (v := (comap (k := k) place).maximalIdeal) varpi).mpr (by
          rw [hvarpi]
          exact withZero_exp_neg_one_lt_one)
    have hfx : completionIntegersMap (k := k) place varpi ∈
        IsLocalRing.maximalIdeal (place.maximalIdeal.adicCompletionIntegers K) ^
          (relativeRamificationIndex (k := k) place + 1) := by
      have hmem := (Ideal.map_le_iff_le_comap.mp hpow) hvarpi_mem
      rwa [Ideal.mem_comap, algebraMap_instAlgebraAdicCompletionIntegers] at hmem
    have hle'' := (mem_maximalIdeal_pow_iff_valued_le_exp_neg (K := K)
      (v := place.maximalIdeal) (relativeRamificationIndex (k := k) place + 1)
      (completionIntegersMap (k := k) place varpi)).mp hfx
    have heq : Valued.v (((completionIntegersMap (k := k) place varpi) :
        place.maximalIdeal.adicCompletionIntegers K) :
        place.maximalIdeal.adicCompletion K) =
        WithZero.exp (-(relativeRamificationIndex (k := k) place : ℤ)) := by
      rw [coe_completionIntegersMap]
      rw [← valuation_completionMap (k := k) place]
      rw [hvarpi, withZero_exp_neg_one_pow]
      simp only [relativeRamificationIndex]
    rw [heq] at hle''
    exact absurd hle'' (not_le.mpr (WithZero.exp_lt_exp.mpr (by omega)))
  show (IsLocalRing.maximalIdeal
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)).ramificationIdx'
      (IsLocalRing.maximalIdeal (place.maximalIdeal.adicCompletionIntegers K)) =
    relativeRamificationIndex (k := k) place
  exact Ideal.ramificationIdx'_spec hmap_le hmap_gt

/-- **(i) + (ii) The local data of the completed extension agree with the library
data of the finite-place extension.** Unconditional form of
`localDataAgreesWithPlaceData`. -/
theorem localDataAgreesWithPlaceData_adicCompletion :
    localDataAgreesWithPlaceData (k := k) place :=
  ⟨localRamificationIndex_eq_relativeRamificationIndex (k := k) place,
   localInertiaDegree_eq_relativeResidueDegree (k := k) place⟩

/-- **Consumer form.** The degree of the completion extension is the relative degree
`e * f`, conditional exactly on `Module.Finite O_v O_w`. -/
theorem finrank_adicCompletion_eq_relativeCompletionDegree_of_moduleFinite
    (hfinite : Module.Finite
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletionIntegers K)) :
    Module.finrank ((comap (k := k) place).maximalIdeal.adicCompletion k)
        (place.maximalIdeal.adicCompletion K) =
      relativeCompletionDegree (k := k) place :=
  finrank_adicCompletion_eq_relativeCompletionDegree (k := k) place hfinite
    (localDataAgreesWithPlaceData_adicCompletion (k := k) place)

/-- **(iii) Separability.** The completion extension is separable, unconditionally:
it is finite and integral in characteristic zero. -/
theorem isSeparable_adicCompletion :
    Algebra.IsSeparable ((comap (k := k) place).maximalIdeal.adicCompletion k)
      (place.maximalIdeal.adicCompletion K) := by
  haveI : Module.Finite ((comap (k := k) place).maximalIdeal.adicCompletion k)
      (place.maximalIdeal.adicCompletion K) :=
    moduleFinite_completionAlgebra (k := k) place
  haveI : Algebra.IsIntegral ((comap (k := k) place).maximalIdeal.adicCompletion k)
      (place.maximalIdeal.adicCompletion K) :=
    Algebra.IsIntegral.of_finite _ _
  infer_instance

/-- **(iii) Exact reduction of the finiteness input.** The completed upper valuation
ring is a finite module over the completed lower valuation ring if and only if it is
the integral closure of the lower ring in the upper completed field. -/
theorem moduleFinite_adicCompletionIntegers_iff_isIntegralClosure :
    Module.Finite ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletionIntegers K) ↔
    IsIntegralClosure (place.maximalIdeal.adicCompletionIntegers K)
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletion K) := by
  constructor
  · intro hfinite
    haveI : Module.Finite
        ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
        (place.maximalIdeal.adicCompletionIntegers K) := hfinite
    refine { algebraMap_injective := ?_, isIntegral_iff := ?_ }
    · exact FaithfulSMul.algebraMap_injective
        (place.maximalIdeal.adicCompletionIntegers K)
        (place.maximalIdeal.adicCompletion K)
    · intro x
      constructor
      · intro hx
        exact ⟨⟨x, integralClosure_le_adicCompletionIntegers (k := k) place hx⟩, rfl⟩
      · rintro ⟨y, rfl⟩
        have hy : IsIntegral ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k) y :=
          Algebra.IsIntegral.isIntegral y
        exact IsIntegral.map
          (IsScalarTower.toAlgHom
            ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
            (place.maximalIdeal.adicCompletionIntegers K)
            (place.maximalIdeal.adicCompletion K))
          hy
  · intro hclosure
    exact moduleFinite_adicCompletionIntegers_of_isIntegralClosure (k := k) place
      (isSeparable_adicCompletion (k := k) place) hclosure

/-- **Consumer form of (iii).** The degree of the completion extension is the
relative degree `e * f`, conditional exactly on the unique-extension statement
`IsIntegralClosure O_w O_v K_w`. -/
theorem finrank_adicCompletion_eq_relativeCompletionDegree_of_isIntegralClosure
    (hclosure : IsIntegralClosure (place.maximalIdeal.adicCompletionIntegers K)
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletion K)) :
    Module.finrank ((comap (k := k) place).maximalIdeal.adicCompletion k)
        (place.maximalIdeal.adicCompletion K) =
      relativeCompletionDegree (k := k) place :=
  finrank_adicCompletion_eq_relativeCompletionDegree_of_moduleFinite (k := k) place
    ((moduleFinite_adicCompletionIntegers_iff_isIntegralClosure (k := k) place).mpr hclosure)

end NumberFieldLocalInputs

end LeanFormal.IUT.NumberFieldFinitePlace


/-! ## Machine-readable audit obligations for the three local inputs -/

namespace LeanFormal.IUT.Audit

def completionResidueFieldIso : Obligation :=
  { id := "ABCBridge.Geometry.completion-residue-field-iso"
    source :=
      "Residue fields of completed valuation rings (Serre, Local Fields I.5); " ++
        "IUT III q-pilot normalization prerequisites"
    status := VerificationStatus.proved
    note :=
      "For a finite place extension k -> K and a place w above the contracted " ++
        "place v, the residue field of the completed valuation ring of the adic " ++
        "completion at w is canonically the residue field of the number ring at " ++
        "w: the generic isomorphism (R / v.asIdeal) = (O_v / m_v) is proved for " ++
        "any Dedekind domain and its adic completion, the two number-field " ++
        "instances (residueEquivAdicCompletionIntegers and its comap variant) " ++
        "are provided, and the compatibility square between them is proved. The " ++
        "consumer form localInertiaDegree = relativeResidueDegree follows by " ++
        "Algebra.finrank_eq_of_equiv_equiv, so the identification of the local " ++
        "residue degree with the library residue degree f is unconditional."
    dependsOn :=
      [ "Foundations.NumberField.finite-place-extension" ] }

def completionRamificationIndexInvariance : Obligation :=
  { id := "ABCBridge.Geometry.completion-ramification-index-invariance"
    source :=
      "Invariance of the ramification index under adic completion " ++
        "(standard local field theory; absent from Mathlib 4.32.2)"
    status := VerificationStatus.proved
    note :=
      "Ideal.ramificationIdx' is invariant under adic completion: " ++
        "localRamificationIndex w = relativeRamificationIndex w, proved via " ++
        "ramificationIdx'_spec with the exponent e := ramificationIdx' v w. The " ++
        "lower bound map m_v <= m_w^e uses valuation_completionMap and the " ++
        "valued characterization of powers of the maximal ideal; the sharp bound " ++
        "uses a uniformizer of the completed lower valuation (whose valuation is " ++
        "exp(-1)), giving an element of m_v mapping to valuation exp(-e) in K_w, " ++
        "which is not in m_w^(e+1). The instance that m_w lies over m_v at the " ++
        "completed valuation rings is proved in the same file."
    dependsOn :=
      [ "Foundations.NumberField.finite-place-extension",
        "ABCBridge.Geometry.completion-residue-field-iso" ] }

def completionIntegersFiniteModule : Obligation :=
  { id := "ABCBridge.Geometry.completion-integers-finite-module"
    source :=
      "Unique extension of a complete valuation (Serre, Local Fields II.2)"
    status := VerificationStatus.pending
    note :=
      "The finiteness of the completed upper valuation ring O_w as an O_v-module " ++
        "is NOT proved in this development. What is proved in this file is the " ++
        "exact reduction Module.Finite O_v O_w <-> IsIntegralClosure O_w O_v K_w " ++
        "(both directions), together with the unconditional separability of the " ++
        "completion extension and the half " ++
        "integralClosure O_v K_w <= O_w from FinitePlaceCompletionDegree. The " ++
        "single remaining mathematical input is that every element of the unit " ++
        "ball O_w is integral over O_v, i.e. the unique-extension statement for " ++
        "the complete valuation. The consumer form is " ++
        "finrank_adicCompletion_eq_relativeCompletionDegree_of_isIntegralClosure, " ++
        "which derives Module.finrank k_v K_w = e * f from that statement; with " ++
        "Module.Finite directly as hypothesis the same conclusion is " ++
        "finrank_adicCompletion_eq_relativeCompletionDegree_of_moduleFinite, and " ++
        "localDataAgreesWithPlaceData is now available unconditionally."
    dependsOn :=
      [ "Foundations.NumberField.finite-place-completion-norm-transport",
        "ABCBridge.Geometry.completion-residue-field-iso",
        "ABCBridge.Geometry.completion-ramification-index-invariance" ] }

end LeanFormal.IUT.Audit
