import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitCurveFivePlace
import LeanFormal.IUT.Foundations.Geometry.ReductionBaseChange
import LeanFormal.IUT.Foundations.Geometry.GenericNodalReduction
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic

/-!
# Split multiplicative reduction of the concrete split curve at 2161

The curve `y^2 + xy = x^3 + 5` has `c₄ = 1` and discriminant
`Δ = -10805 = -5 * 2161`.  At the rational prime `2161` the discriminant is a
nonunit, while `c₄` stays a unit, so the curve has multiplicative reduction.
The tangent-cone polynomial at `2161` is `X^2 + X - 1080`, which factors as
`(X - 73)(X - 2087)` modulo `2161`; hence the reduction is split
multiplicative.

The local computation is performed over `ℤ_[2161]` and transported to the
actual height-one adic completion of `ℚ` at the prime `2161`, exactly as in
`ConcreteSplitCurveFivePlace` for the prime `5`.
-/

namespace LeanFormal.IUT

noncomputable section

open Polynomial

local instance concrete2161PrimeFact : Fact (Nat.Prime 2161) :=
  ⟨by norm_num⟩

/-! ## The rational prime 2161 and its actual finite place -/

def concrete2161Prime : Nat.Primes :=
  ⟨2161, by norm_num⟩

def concrete2161HeightOne :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := NumberField.RingOfIntegers ℚ)).symm
    concrete2161Prime

def concrete2161Place : NumberField.FinitePlace ℚ :=
  NumberField.FinitePlace.mk concrete2161HeightOne

@[simp] theorem concrete2161Place_maximalIdeal :
    concrete2161Place.maximalIdeal = concrete2161HeightOne := by
  exact NumberField.FinitePlace.maximalIdeal_mk concrete2161HeightOne

@[simp] theorem concrete2161Place_underlyingPrime :
    NumberFieldFinitePlace.underlyingPrime concrete2161Place = concrete2161HeightOne := by
  exact concrete2161Place_maximalIdeal

theorem concrete2161HeightOne_natGenerator :
    Rat.HeightOneSpectrum.natGenerator concrete2161HeightOne = 2161 := by
  exact congrArg (fun p : Nat.Primes => p.1)
    ((Rat.HeightOneSpectrum.primesEquiv
      (R := NumberField.RingOfIntegers ℚ)).apply_symm_apply concrete2161Prime)

theorem concrete2161HeightOne_2161_mem :
    (2161 : NumberField.RingOfIntegers ℚ) ∈ concrete2161HeightOne.asIdeal := by
  apply (Ideal.apply_mem_of_equiv_iff
    (I := concrete2161HeightOne.asIdeal)
    (f := Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ))).mp
  have hdiv : Rat.HeightOneSpectrum.natGenerator concrete2161HeightOne ∣ 2161 := by
    rw [concrete2161HeightOne_natGenerator]
  have hmap :=
    (Rat.HeightOneSpectrum.natGenerator_dvd_iff concrete2161HeightOne).mp hdiv
  convert hmap using 1
  rw [Rat.IsIntegralClosure.intEquiv_apply_eq_ringOfIntegersEquiv]
  exact map_intCast Rat.ringOfIntegersEquiv 2161

/-! ## The explicit equation over `ℚ_[2161]` and its integral model -/

abbrev concrete2161LocalField := ℚ_[2161]

abbrev concrete2161LocalIntegers := ℤ_[2161]

def concrete2161CurveLocal : WeierstrassCurve concrete2161LocalField :=
  WeierstrassCurve.mk 1 0 0 0 5

def concrete2161CurveIntegral : WeierstrassCurve concrete2161LocalIntegers :=
  WeierstrassCurve.mk 1 0 0 0 5

theorem concrete2161CurveIntegral_map_eq_local :
    (concrete2161CurveIntegral.map
      (algebraMap concrete2161LocalIntegers concrete2161LocalField)) =
      concrete2161CurveLocal := by
  rfl

theorem concrete2161CurveLocal_map_eq_rational :
    concrete2161CurveLocal =
      concreteSplitCurve.map (algebraMap ℚ concrete2161LocalField) := by
  ext <;> rfl

theorem concrete2161CurveIntegral_is_integral :
    WeierstrassCurve.IsIntegral concrete2161LocalIntegers concrete2161CurveLocal := by
  refine ⟨⟨concrete2161CurveIntegral, ?_⟩⟩
  exact concrete2161CurveIntegral_map_eq_local

theorem concrete2161CurveIntegral_a₁ :
    concrete2161CurveIntegral.a₁ = (1 : concrete2161LocalIntegers) := by
  rfl

theorem concrete2161CurveIntegral_a₂ :
    concrete2161CurveIntegral.a₂ = (0 : concrete2161LocalIntegers) := by
  rfl

theorem concrete2161CurveIntegral_a₃ :
    concrete2161CurveIntegral.a₃ = (0 : concrete2161LocalIntegers) := by
  rfl

theorem concrete2161CurveIntegral_a₄ :
    concrete2161CurveIntegral.a₄ = (0 : concrete2161LocalIntegers) := by
  rfl

theorem concrete2161CurveIntegral_a₆ :
    concrete2161CurveIntegral.a₆ = (5 : concrete2161LocalIntegers) := by
  rfl

theorem concrete2161CurveIntegral_b₂ :
    concrete2161CurveIntegral.b₂ = (1 : concrete2161LocalIntegers) := by
  norm_num [concrete2161CurveIntegral, WeierstrassCurve.b₂]

theorem concrete2161CurveIntegral_b₄ :
    concrete2161CurveIntegral.b₄ = (0 : concrete2161LocalIntegers) := by
  norm_num [concrete2161CurveIntegral, WeierstrassCurve.b₄]

theorem concrete2161CurveIntegral_b₆ :
    concrete2161CurveIntegral.b₆ = (20 : concrete2161LocalIntegers) := by
  norm_num [concrete2161CurveIntegral, WeierstrassCurve.b₆]

theorem concrete2161CurveIntegral_b₈ :
    concrete2161CurveIntegral.b₈ = (5 : concrete2161LocalIntegers) := by
  norm_num [concrete2161CurveIntegral, WeierstrassCurve.b₈]

theorem concrete2161CurveIntegral_c₄ :
    concrete2161CurveIntegral.c₄ = (1 : concrete2161LocalIntegers) := by
  norm_num [concrete2161CurveIntegral, WeierstrassCurve.c₄,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄]

theorem concrete2161CurveIntegral_delta :
    concrete2161CurveIntegral.Δ = (-10805 : concrete2161LocalIntegers) := by
  norm_num [concrete2161CurveIntegral, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem concrete2161CurveLocal_b₂ :
    concrete2161CurveLocal.b₂ = (1 : concrete2161LocalField) := by
  norm_num [concrete2161CurveLocal, WeierstrassCurve.b₂]

theorem concrete2161CurveLocal_b₄ :
    concrete2161CurveLocal.b₄ = (0 : concrete2161LocalField) := by
  norm_num [concrete2161CurveLocal, WeierstrassCurve.b₄]

theorem concrete2161CurveLocal_b₆ :
    concrete2161CurveLocal.b₆ = (20 : concrete2161LocalField) := by
  norm_num [concrete2161CurveLocal, WeierstrassCurve.b₆]

theorem concrete2161CurveLocal_c₄ :
    concrete2161CurveLocal.c₄ = (1 : concrete2161LocalField) := by
  norm_num [concrete2161CurveLocal, WeierstrassCurve.c₄,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄]

theorem concrete2161CurveLocal_delta :
    concrete2161CurveLocal.Δ = (-10805 : concrete2161LocalField) := by
  norm_num [concrete2161CurveLocal, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-! ## The prime 2161 is a uniformizer of `ℤ_[2161]` -/

theorem concrete2161_mem_maximalIdeal :
    (2161 : concrete2161LocalIntegers) ∈
      IsLocalRing.maximalIdeal concrete2161LocalIntegers := by
  rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
  exact (PadicInt.norm_natCast_lt_one_iff (p := 2161) (n := 2161)).2 (by norm_num)

theorem concrete2161CurveIntegral_c₄_isUnit :
    IsUnit concrete2161CurveIntegral.c₄ := by
  rw [concrete2161CurveIntegral_c₄]
  exact isUnit_one

theorem concrete2161CurveIntegral_delta_mem_maximalIdeal :
    concrete2161CurveIntegral.Δ ∈ IsLocalRing.maximalIdeal concrete2161LocalIntegers := by
  rw [concrete2161CurveIntegral_delta]
  rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
  simpa using
    (PadicInt.norm_intCast_lt_one_iff (p := 2161) (z := (-10805 : ℤ))).2
      (by norm_num : (2161 : ℤ) ∣ -10805)

theorem concrete2161CurveLocal_delta_ne_zero :
    concrete2161CurveLocal.Δ ≠ 0 := by
  rw [concrete2161CurveLocal_delta]
  norm_num

theorem concrete2161CurveLocal_isElliptic :
    concrete2161CurveLocal.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  exact isUnit_iff_ne_zero.mpr concrete2161CurveLocal_delta_ne_zero

theorem concrete2161CurveLocal_delta_valuation_lt_one :
    (IsDiscreteValuationRing.maximalIdeal concrete2161LocalIntegers).valuation
      concrete2161LocalField concrete2161CurveLocal.Δ < 1 := by
  rw [← concrete2161CurveIntegral_map_eq_local]
  rw [WeierstrassCurve.map_Δ]
  change (IsDiscreteValuationRing.maximalIdeal concrete2161LocalIntegers).valuation
    concrete2161LocalField
      (algebraMap concrete2161LocalIntegers concrete2161LocalField
        concrete2161CurveIntegral.Δ) < 1
  exact ((IsDiscreteValuationRing.maximalIdeal concrete2161LocalIntegers).valuation_lt_one_iff_mem
    (K := concrete2161LocalField) concrete2161CurveIntegral.Δ).mpr
      concrete2161CurveIntegral_delta_mem_maximalIdeal

theorem concrete2161CurveLocal_c₄_valuation_eq_one :
    (IsDiscreteValuationRing.maximalIdeal concrete2161LocalIntegers).valuation
      concrete2161LocalField concrete2161CurveLocal.c₄ = 1 := by
  rw [← concrete2161CurveIntegral_map_eq_local]
  rw [WeierstrassCurve.map_c₄]
  exact ((IsDiscreteValuationRing.maximalIdeal concrete2161LocalIntegers).valuation_eq_one_iff_notMem
    (K := concrete2161LocalField)).mpr
      (IsLocalRing.notMem_maximalIdeal.mpr concrete2161CurveIntegral_c₄_isUnit)

theorem concrete2161CurveLocal_isMinimal :
    WeierstrassCurve.IsMinimal concrete2161LocalIntegers concrete2161CurveLocal := by
  letI : WeierstrassCurve.IsIntegral concrete2161LocalIntegers concrete2161CurveLocal :=
    concrete2161CurveIntegral_is_integral
  exact isMinimal_of_isIntegral_valuation_c₄_eq_one
    concrete2161LocalIntegers concrete2161CurveLocal
    concrete2161CurveLocal_c₄_valuation_eq_one

theorem concrete2161CurveLocal_hasMultiplicativeReduction :
    concrete2161CurveLocal.HasMultiplicativeReduction concrete2161LocalIntegers := by
  letI : WeierstrassCurve.IsIntegral concrete2161LocalIntegers concrete2161CurveLocal :=
    concrete2161CurveIntegral_is_integral
  letI : WeierstrassCurve.IsMinimal concrete2161LocalIntegers concrete2161CurveLocal :=
    concrete2161CurveLocal_isMinimal
  exact
    { badReduction := concrete2161CurveLocal_delta_valuation_lt_one
      multiplicativeReduction := concrete2161CurveLocal_c₄_valuation_eq_one }

theorem concrete2161CurveLocal_integralModel_eq_integral :
    letI : WeierstrassCurve.IsIntegral concrete2161LocalIntegers concrete2161CurveLocal :=
      concrete2161CurveIntegral_is_integral
    concrete2161CurveLocal.integralModel concrete2161LocalIntegers =
      concrete2161CurveIntegral := by
  letI : WeierstrassCurve.IsIntegral concrete2161LocalIntegers concrete2161CurveLocal :=
    concrete2161CurveIntegral_is_integral
  apply WeierstrassCurve.map_injective
    (FaithfulSMul.algebraMap_injective concrete2161LocalIntegers concrete2161LocalField)
  change
    (concrete2161CurveLocal.integralModel concrete2161LocalIntegers).baseChange
        concrete2161LocalField =
      concrete2161CurveIntegral.baseChange concrete2161LocalField
  rw [WeierstrassCurve.baseChange_integralModel_eq]
  exact concrete2161CurveIntegral_map_eq_local.symm

/-! ## The tangent-cone polynomial and its splitting at 2161 -/

theorem concrete2161CurveIntegral_splitReductionPolynomial :
    splitReductionPolynomial concrete2161CurveIntegral =
      X ^ 2 + X - C (1080 : concrete2161LocalIntegers) := by
  rw [splitReductionPolynomial, concrete2161CurveIntegral]
  norm_num [WeierstrassCurve.c₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆]

theorem concrete2161_sum_mem_maximalIdeal :
    (73 : concrete2161LocalIntegers) + 2087 + 1 ∈
      IsLocalRing.maximalIdeal concrete2161LocalIntegers := by
  have h : (73 : concrete2161LocalIntegers) + 2087 + 1 = (2161 : concrete2161LocalIntegers) := by
    norm_num
  rw [h]
  exact concrete2161_mem_maximalIdeal

theorem concrete2161_product_mem_maximalIdeal :
    (73 : concrete2161LocalIntegers) * 2087 + 1080 ∈
      IsLocalRing.maximalIdeal concrete2161LocalIntegers := by
  have h : (73 : concrete2161LocalIntegers) * 2087 + 1080 =
      (71 : concrete2161LocalIntegers) * 2161 := by
    norm_num
  rw [h]
  exact Ideal.mul_mem_left _ _ concrete2161_mem_maximalIdeal

theorem concrete2161_residue_roots_sum :
    IsLocalRing.residue concrete2161LocalIntegers (73 : concrete2161LocalIntegers) +
        IsLocalRing.residue concrete2161LocalIntegers (2087 : concrete2161LocalIntegers) = -1 := by
  have h0 : IsLocalRing.residue concrete2161LocalIntegers
      ((73 : concrete2161LocalIntegers) + 2087 + 1) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact concrete2161_sum_mem_maximalIdeal
  have h1 : IsLocalRing.residue concrete2161LocalIntegers (73 : concrete2161LocalIntegers) +
      IsLocalRing.residue concrete2161LocalIntegers (2087 : concrete2161LocalIntegers) + 1 = 0 := by
    simpa using h0
  linear_combination h1

theorem concrete2161_residue_roots_product :
    IsLocalRing.residue concrete2161LocalIntegers (73 : concrete2161LocalIntegers) *
        IsLocalRing.residue concrete2161LocalIntegers (2087 : concrete2161LocalIntegers) =
      -(IsLocalRing.residue concrete2161LocalIntegers (1080 : concrete2161LocalIntegers)) := by
  have h0 : IsLocalRing.residue concrete2161LocalIntegers
      ((73 : concrete2161LocalIntegers) * 2087 + 1080) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact concrete2161_product_mem_maximalIdeal
  have h1 : IsLocalRing.residue concrete2161LocalIntegers (73 : concrete2161LocalIntegers) *
      IsLocalRing.residue concrete2161LocalIntegers (2087 : concrete2161LocalIntegers) +
      IsLocalRing.residue concrete2161LocalIntegers (1080 : concrete2161LocalIntegers) = 0 := by
    simpa using h0
  linear_combination h1

theorem concrete2161CurveIntegral_splitReductionPolynomial_factors :
    (X ^ 2 + X - C (1080 : concrete2161LocalIntegers)).map
        (IsLocalRing.residue concrete2161LocalIntegers) =
      (X - C (IsLocalRing.residue concrete2161LocalIntegers (73 : concrete2161LocalIntegers))) *
        (X - C (IsLocalRing.residue concrete2161LocalIntegers (2087 : concrete2161LocalIntegers))) := by
  let a := IsLocalRing.residue concrete2161LocalIntegers (73 : concrete2161LocalIntegers)
  let b := IsLocalRing.residue concrete2161LocalIntegers (2087 : concrete2161LocalIntegers)
  let c := IsLocalRing.residue concrete2161LocalIntegers (1080 : concrete2161LocalIntegers)
  have hsum : a + b = -1 := concrete2161_residue_roots_sum
  have hprod : a * b = -c := concrete2161_residue_roots_product
  have hmap : (X ^ 2 + X - C (1080 : concrete2161LocalIntegers)).map
      (IsLocalRing.residue concrete2161LocalIntegers) =
      X ^ 2 + X - C c := by
    change (X ^ 2 + X - C (1080 : concrete2161LocalIntegers)).map
        (IsLocalRing.residue concrete2161LocalIntegers) =
      X ^ 2 + X - C (IsLocalRing.residue concrete2161LocalIntegers
        (1080 : concrete2161LocalIntegers))
    simp
  rw [hmap]
  have hfac : (X - C a) * (X - C b) = X ^ 2 + X - C c := by
    calc (X - C a) * (X - C b)
        = X ^ 2 - (C a + C b) * X + C a * C b := by ring
      _ = X ^ 2 - C (a + b) * X + C (a * b) := by rw [C_add, C_mul]
      _ = X ^ 2 - C (-1) * X + C (-c) := by rw [hsum, hprod]
      _ = X ^ 2 + X - C c := by
            rw [C_neg, C_neg, C_1]
            ring
  rw [← hfac]

theorem concrete2161CurveIntegral_splitReductionPolynomial_splits :
    Polynomial.Splits ((splitReductionPolynomial concrete2161CurveIntegral).map
      (IsLocalRing.residue concrete2161LocalIntegers)) := by
  rw [concrete2161CurveIntegral_splitReductionPolynomial]
  rw [concrete2161CurveIntegral_splitReductionPolynomial_factors]
  exact Polynomial.Splits.mul
    (Polynomial.Splits.X_sub_C _) (Polynomial.Splits.X_sub_C _)

theorem concrete2161CurveLocal_hasSplitMultiplicativeReduction :
    concrete2161CurveLocal.HasSplitMultiplicativeReduction concrete2161LocalIntegers := by
  letI : WeierstrassCurve.IsIntegral concrete2161LocalIntegers concrete2161CurveLocal :=
    concrete2161CurveIntegral_is_integral
  letI : WeierstrassCurve.IsMinimal concrete2161LocalIntegers concrete2161CurveLocal :=
    concrete2161CurveLocal_isMinimal
  letI : concrete2161CurveLocal.HasMultiplicativeReduction concrete2161LocalIntegers :=
    concrete2161CurveLocal_hasMultiplicativeReduction
  refine { splitMultiplicativeReduction := ?_ }
  rw [concrete2161CurveLocal_integralModel_eq_integral]
  change Polynomial.Splits
    ((splitReductionPolynomial concrete2161CurveIntegral).map
      (IsLocalRing.residue concrete2161LocalIntegers))
  exact concrete2161CurveIntegral_splitReductionPolynomial_splits

/-! ## Transport to the actual adic completion at 2161 -/

abbrev concrete2161Completion := concrete2161HeightOne.adicCompletion ℚ

abbrev concrete2161CompletionIntegers :=
  concrete2161HeightOne.adicCompletionIntegers ℚ

noncomputable def concrete2161PadicEquiv :
    concrete2161LocalField ≃A[ℚ] concrete2161Completion :=
  Padic.adicCompletionEquiv (R := NumberField.RingOfIntegers ℚ)
    concrete2161Prime

noncomputable def concrete2161PadicIntEquiv :
    concrete2161LocalIntegers ≃A[ℤ] concrete2161CompletionIntegers :=
  PadicInt.adicCompletionIntegersEquiv (R := NumberField.RingOfIntegers ℚ)
    concrete2161Prime

theorem concrete2161PadicEquiv_algebraMap (x : ℚ) :
    concrete2161PadicEquiv
        (algebraMap ℚ concrete2161LocalField x) =
      algebraMap ℚ concrete2161Completion x := by
  exact concrete2161PadicEquiv.commutes x

theorem concrete2161PadicIntEquiv_coe (x : concrete2161LocalIntegers) :
    (concrete2161PadicIntEquiv x : concrete2161Completion) =
      concrete2161PadicEquiv (x : concrete2161LocalField) := by
  exact PadicInt.coe_adicCompletionIntegersEquiv_apply
    (R := NumberField.RingOfIntegers ℚ) concrete2161Prime x

def concreteSplitCurveAt2161 : WeierstrassCurve concrete2161Completion :=
  concreteSplitCurve.baseChange concrete2161Completion

theorem concrete2161CurveLocal_map_to_completion :
    concrete2161CurveLocal.map concrete2161PadicEquiv.toRingEquiv.toRingHom =
      concreteSplitCurveAt2161 := by
  ext <;> simp [concrete2161CurveLocal, concreteSplitCurveAt2161,
    concreteSplitCurve, WeierstrassCurve.baseChange]
  simpa using congrArg (fun z : concrete2161Completion => z.toCompletion)
    (concrete2161PadicEquiv_algebraMap 5)

theorem concreteSplitCurveAt2161_hasSplitMultiplicativeReduction :
    HasSplitMultiplicativeReductionOnMinimalModel
      concrete2161CompletionIntegers concreteSplitCurveAt2161 := by
  rw [← concrete2161CurveLocal_map_to_completion]
  letI : IsLocalHom concrete2161PadicIntEquiv.toRingEquiv.toRingHom := by
    refine ⟨fun x hx => ?_⟩
    simpa using hx.map concrete2161PadicIntEquiv.toRingEquiv.symm.toMonoidHom
  exact hasSplitMultiplicativeReductionOnMinimalModel_map_of_commutes
    concrete2161PadicIntEquiv.toRingEquiv.toRingHom
    concrete2161PadicEquiv.toRingEquiv.toRingHom
    (by
      apply RingHom.ext
      intro x
      change concrete2161PadicEquiv (algebraMap concrete2161LocalIntegers
        concrete2161LocalField x) =
        algebraMap concrete2161CompletionIntegers concrete2161Completion
          (concrete2161PadicIntEquiv x)
      change concrete2161PadicEquiv (algebraMap concrete2161LocalIntegers
        concrete2161LocalField x) = (concrete2161PadicIntEquiv x : concrete2161Completion)
      rw [concrete2161PadicIntEquiv_coe]
      congr 1)
    concrete2161CurveLocal
    ⟨1, by simpa using concrete2161CurveLocal_hasSplitMultiplicativeReduction⟩

theorem concreteSplitCurveAt2161_hasMultiplicativeReduction :
    HasMultiplicativeReductionOnMinimalModel
      concrete2161CompletionIntegers concreteSplitCurveAt2161 := by
  rcases concreteSplitCurveAt2161_hasSplitMultiplicativeReduction with ⟨C, hC⟩
  exact ⟨C, hC.toHasMultiplicativeReduction⟩

theorem concreteSplitPuncturedCurve_hasSplitMultiplicativeReductionAt_2161 :
    concreteSplitPuncturedCurve.HasSplitMultiplicativeReductionAt
      concrete2161Place := by
  unfold PuncturedEllipticCurve.HasSplitMultiplicativeReductionAt
  let F : ∀ z : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers ℚ), WeierstrassCurve (z.adicCompletion ℚ) :=
    fun z => concreteSplitCurve.baseChange (z.adicCompletion ℚ)
  have htransport :=
    transport_splitMultiplicativeReduction_along_heightOne_eq F
      concrete2161Place_underlyingPrime.symm
      (by
        change HasSplitMultiplicativeReductionOnMinimalModel
          concrete2161CompletionIntegers concreteSplitCurveAt2161
        exact concreteSplitCurveAt2161_hasSplitMultiplicativeReduction)
  simpa [F, concreteSplitPuncturedCurve] using htransport

theorem concreteSplitPuncturedCurve_hasMultiplicativeReductionAt_2161 :
    concreteSplitPuncturedCurve.HasMultiplicativeReductionAt concrete2161Place := by
  exact PuncturedEllipticCurve.hasSplitMultiplicativeReductionAt_imp_multiplicative
    concreteSplitPuncturedCurve_hasSplitMultiplicativeReductionAt_2161

structure ConcreteSplitCurve2161Certificate where
  place : NumberField.FinitePlace ℚ
  place_eq : place = concrete2161Place
  completion : WeierstrassCurve concrete2161Completion
  completion_eq : completion = concreteSplitCurveAt2161
  splitMultiplicative :
    HasSplitMultiplicativeReductionOnMinimalModel
      concrete2161CompletionIntegers completion
  globalSplitMultiplicative :
    concreteSplitPuncturedCurve.HasSplitMultiplicativeReductionAt concrete2161Place

def concreteSplitCurve2161Certificate :
    ConcreteSplitCurve2161Certificate where
  place := concrete2161Place
  place_eq := rfl
  completion := concreteSplitCurveAt2161
  completion_eq := rfl
  splitMultiplicative := concreteSplitCurveAt2161_hasSplitMultiplicativeReduction
  globalSplitMultiplicative :=
    concreteSplitPuncturedCurve_hasSplitMultiplicativeReductionAt_2161

/-! ## Public target statements -/

/-- The rational finite place at the prime `2161`. -/
def S2687Place : NumberField.FinitePlace ℚ :=
  concrete2161Place

@[simp] theorem S2687Place_maximalIdeal :
    S2687Place.maximalIdeal = concrete2161HeightOne := by
  exact concrete2161Place_maximalIdeal

theorem S2687Place_natGenerator :
    Rat.HeightOneSpectrum.natGenerator S2687Place.maximalIdeal = 2161 := by
  rw [S2687Place_maximalIdeal]
  exact concrete2161HeightOne_natGenerator

theorem S2687HasSplitMultiplicativeReductionAt2161 :
    concreteSplitPuncturedCurve.HasSplitMultiplicativeReductionAt S2687Place :=
  concreteSplitPuncturedCurve_hasSplitMultiplicativeReductionAt_2161

theorem S2687HasMultiplicativeReductionAt2161 :
    concreteSplitPuncturedCurve.HasMultiplicativeReductionAt S2687Place :=
  concreteSplitPuncturedCurve_hasMultiplicativeReductionAt_2161

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def concreteSplitCurve2161 : Obligation :=
  { id := "Foundations.Geometry.concrete-split-curve-2161"
    source := "IUT I, Definition 3.1(b); rational finite place 2161"
    status := VerificationStatus.proved
    note :=
      "The explicit rational curve y^2 + xy = x^3 + 5 has c4 = 1 and " ++
        "discriminant -10805 = -5 * 2161. At the actual height-one prime " ++
        "2161 the tangent-cone polynomial is X^2 + X - 1080, which factors " ++
        "through the roots 73 and 2087; the split multiplicative reduction " ++
        "is transported from the concrete p-adic model to the genuine adic " ++
        "completion and to the global punctured curve." 
    dependsOn := ["Foundations.Geometry.concrete-split-curve-five-place",
      "Foundations.Geometry.elliptic-reduction-base-change"] }

end LeanFormal.IUT.Audit
