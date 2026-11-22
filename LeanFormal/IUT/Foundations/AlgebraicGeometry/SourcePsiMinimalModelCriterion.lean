/-
  Local minimal-model criterion for an actual integral Weierstrass model.

  Corrected minimality: an integral model is minimal when every change of
  coordinates over K with integral transformed coefficients and integral scaling
  factor has unit scaling factor.  Changes with nonintegral scaling (for example
  u = pi^{-1}) are not counterexamples; they scale the discriminant upward rather
  than downward.  This file proves the criterion in this exact form, shows that a
  nonunit integral scaling factor is divisible by the actual uniformizer, and
  isolates the general (u,r,s,t) reduction step as the exact residual.

  No model, uniformizer, or scaling is fabricated.
-/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiResidueRingFinite

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.SourcePsiMinimalModelCriterion

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralUnits
open LeanFormal.IUT.SourcePsiIntegralUnitsCompletion
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiIntegralModelMinimality
open LeanFormal.IUT.AdicCompletionFractionField
open LeanFormal.IUT.SourcePsiResidueRingFinite
open IsDedekindDomain HeightOneSpectrum

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

/-- The actual uniformizer of the adic completion integers. -/
abbrev SourcePsiCriterionUniformizer : SourcePsiCompletionIntegerRing S v :=
  sourcePsiUniformizerUnconditional S v

/-- An element of K is integral when it is in the image of the adic completion
integers. -/
def IsCompletionIntegralElement
    (x : SourcePsiCompletionFractionField S v) : Prop :=
  ∃ r : SourcePsiCompletionIntegerRing S v,
    algebraMap (SourcePsiCompletionIntegerRing S v)
      (SourcePsiCompletionFractionField S v) r = x

/-- A change has integral transformed coefficients. -/
def SourcePsiChangeIntegral
    (M : SourcePsiIntegralModelData S v)
    (C : VariableChange (SourcePsiCompletionFractionField S v)) : Prop :=
  SourcePsiIntegralWeierstrassCurve S v
    (C • (M.curve.map
      (algebraMap (SourcePsiCompletionIntegerRing S v)
        (SourcePsiCompletionFractionField S v))))

/-- Corrected minimality: integral changes with integral scaling factor have unit
scaling factor. -/
def SourcePsiIntegralModelMinimalCorrected
    (M : SourcePsiIntegralModelData S v) : Prop :=
  ∀ C : VariableChange (SourcePsiCompletionFractionField S v),
    SourcePsiChangeIntegral S v M C →
      IsCompletionIntegralElement S v (C.u : SourcePsiCompletionFractionField S v) →
        IsCompletionIntegralUnit S v (C.u : SourcePsiCompletionFractionField S v)

/-- Nonminimality in the corrected sense is exactly the existence of an integral
change with integral nonunit scaling factor. -/
theorem SourcePsiIntegralModel_not_minimalCorrected_iff :
    (¬ SourcePsiIntegralModelMinimalCorrected S v M) ↔
      ∃ C : VariableChange (SourcePsiCompletionFractionField S v),
        SourcePsiChangeIntegral S v M C ∧
          IsCompletionIntegralElement S v (C.u : SourcePsiCompletionFractionField S v) ∧
            ¬ IsCompletionIntegralUnit S v (C.u : SourcePsiCompletionFractionField S v) := by
  constructor
  · intro h
    classical
    by_contra hno
    apply h
    intro C hC hint hu
    by_contra hunit
    exact hno ⟨C, hC, hint, hunit⟩
  · rintro ⟨C, hC, hint, hunit⟩ hmin
    exact hunit (hmin C hC hint)

/-- An integral nonunit scaling factor is not a unit. -/
theorem nonunit_integral_scaling_not_unit
    (M : SourcePsiIntegralModelData S v)
    (C : VariableChange (SourcePsiCompletionFractionField S v))
    (hint : IsCompletionIntegralElement S v (C.u : SourcePsiCompletionFractionField S v))
    (hnot : ¬ IsCompletionIntegralUnit S v (C.u : SourcePsiCompletionFractionField S v)) :
    ¬ IsUnit (Classical.choose hint : SourcePsiCompletionIntegerRing S v) := by
  intro hunit
  apply hnot
  refine ⟨Classical.choose hint, ?_⟩
  rw [Classical.choose_spec hint]
  exact hunit.unit

/-- A nonunit integral scaling factor lies in the maximal ideal, hence is
divisible by the actual uniformizer. -/
theorem exists_uniformizer_mul_of_integral_nonunit
    (r : SourcePsiCompletionIntegerRing S v) (hr : ¬ IsUnit r) :
    ∃ r' : SourcePsiCompletionIntegerRing S v,
      r = SourcePsiCriterionUniformizer S v * r' := by
  have hmem : r ∈ IsLocalRing.maximalIdeal (SourcePsiCompletionIntegerRing S v) :=
    IsLocalRing.mem_maximalIdeal_of_not_isUnit r hr
  rw [sourcePsiUniformizerUnconditional_maximalIdeal_eq S v] at hmem
  obtain ⟨r', hr'⟩ := Ideal.mem_span_singleton.mp hmem
  exact ⟨r', hr'⟩

/-- The actual uniformizer is nonunit and integral. -/
theorem SourcePsiCriterionUniformizer_nonunit :
    ¬ IsUnit (SourcePsiCriterionUniformizer S v) :=
  sourcePsiUniformizerUnconditional_not_unit S v

/-- The actual uniformizer is an integral element of K. -/
theorem SourcePsiCriterionUniformizer_integralElement :
    IsCompletionIntegralElement S v
      (algebraMap (SourcePsiCompletionIntegerRing S v)
        (SourcePsiCompletionFractionField S v)
        (SourcePsiCriterionUniformizer S v)) :=
  ⟨SourcePsiCriterionUniformizer S v, rfl⟩

/-- If a change with integral nonunit scaling exists, a uniformizer-divided
scaling exists on the level of the scaling factor: u = pi * r' with r' integral
(up to the chosen integral representative of u). -/
theorem nonunit_integral_change_has_uniformizer_factor
    (M : SourcePsiIntegralModelData S v)
    (C : VariableChange (SourcePsiCompletionFractionField S v))
    (hint : IsCompletionIntegralElement S v (C.u : SourcePsiCompletionFractionField S v))
    (hnot : ¬ IsCompletionIntegralUnit S v (C.u : SourcePsiCompletionFractionField S v)) :
    ∃ r' : SourcePsiCompletionIntegerRing S v,
      (C.u : SourcePsiCompletionFractionField S v) =
        algebraMap (SourcePsiCompletionIntegerRing S v)
          (SourcePsiCompletionFractionField S v)
          (SourcePsiCriterionUniformizer S v * r') := by
  let r : SourcePsiCompletionIntegerRing S v := Classical.choose hint
  have hr_spec : algebraMap (SourcePsiCompletionIntegerRing S v)
      (SourcePsiCompletionFractionField S v) r =
      (C.u : SourcePsiCompletionFractionField S v) := Classical.choose_spec hint
  have hr_nonunit : ¬ IsUnit r := by
    intro hunit
    apply hnot
    exact ⟨r, hr_spec.trans (by rw [← hr_spec])⟩
  obtain ⟨r', hr'⟩ := exists_uniformizer_mul_of_integral_nonunit S v r hr_nonunit
  exact ⟨r', by rw [← hr_spec, hr', map_mul]⟩

/-! ## Exact criterion and residual

Proved:
- corrected minimality is equivalent to absence of an integral change with
  integral nonunit scaling;
- any integral nonunit scaling factor is divisible by the actual uniformizer;
- existence of such a scaling gives a uniformizer factor of the scaling.

Still missing:
1. the general (u,r,s,t) normalisation: a uniformizer factor in u does not yet
   produce a uniformizer-scaled change with r = s = t = 0 and all coefficients
   integral (translations and unit factors must be absorbed/compared);
2. the equivalence between corrected minimality and the pure uniformizer-divisibility
   criterion for all coefficients;
3. the full minimal-model existence/uniqueness theorem;
4. comparison with the source special fiber and stable reduction.

These are the exact residual steps.  No model or change is fabricated.
-/

/-! ## Uniformizer-divisibility obstruction in the corrected criterion

theorem SourcePsiCriterionUniformizer_algebraMap_ne_zero :
    algebraMap (SourcePsiCompletionIntegerRing S v)
      (SourcePsiCompletionFractionField S v)
      (SourcePsiCriterionUniformizer S v) ≠ 0 :=
  sourcePsiUniformizerUnconditional_algebraMap_ne_zero S v

theorem SourcePsiCriterionUniformizer_valuation_lt_one :
    Valued.v (algebraMap (SourcePsiCompletionIntegerRing S v)
      (SourcePsiCompletionFractionField S v)
      (SourcePsiCriterionUniformizer S v)) < 1 :=
  sourcePsiUniformizerUnconditional_valuation_lt_one S v

theorem SourcePsiCriterionUniformizer_pow_mem_maximalIdeal
    {n : ℕ} (hn : 0 < n) :
    SourcePsiCriterionUniformizer S v ^ n ∈
      IsLocalRing.maximalIdeal (SourcePsiCompletionIntegerRing S v) :=
  sourcePsiUniformizerUnconditional_pow_mem_maximalIdeal S v hn

/-- Uniform divisibility by the actual uniformizer gives an integral change with
uniformizer scaling (scaling factor u = pi, r = s = t = 0). -/
theorem uniformizerDivisibility_change_integral
    (M : SourcePsiIntegralModelData S v)
    (hdiv : SourcePsiUniformlyDivisible S v M
      (SourcePsiCriterionUniformizer S v)) :
    SourcePsiChangeIntegral S v M
      (sourcePsiUniformScaling S v (SourcePsiCriterionUniformizer S v)
        (SourcePsiCriterionUniformizer_algebraMap_ne_zero S v)) :=
  sourcePsiUniformScaling_integral S v M (SourcePsiCriterionUniformizer S v)
    (SourcePsiCriterionUniformizer_algebraMap_ne_zero S v) hdiv

/-- The scaling factor of the uniformizer change is integral and nonunit. -/
theorem uniformizerDivisibility_scaling_integral_nonunit :
    IsCompletionIntegralElement S v
        ((sourcePsiUniformScaling S v (SourcePsiCriterionUniformizer S v)
          (SourcePsiCriterionUniformizer_algebraMap_ne_zero S v)).u :
          SourcePsiCompletionFractionField S v) ∧
      ¬ IsCompletionIntegralUnit S v
        ((sourcePsiUniformScaling S v (SourcePsiCriterionUniformizer S v)
          (SourcePsiCriterionUniformizer_algebraMap_ne_zero S v)).u :
          SourcePsiCompletionFractionField S v) :=
  ⟨⟨SourcePsiCriterionUniformizer S v, rfl⟩,
    fun hunit => SourcePsiCriterionUniformizer_nonunit S v (by
      obtain ⟨r, hr⟩ := hunit
      exact IsUnit.of_eq (by simpa using hr))⟩

/-- Uniformizer divisibility obstructs corrected minimality: the explicit
uniformizer scaling is an integral change with integral nonunit scaling. -/
theorem SourcePsiIntegralModel_not_minimalCorrected_of_uniformizerDivisibility
    (M : SourcePsiIntegralModelData S v)
    (hdiv : SourcePsiUniformlyDivisible S v M
      (SourcePsiCriterionUniformizer S v)) :
    ¬ SourcePsiIntegralModelMinimalCorrected S v M := by
  intro hmin
  let C := sourcePsiUniformScaling S v (SourcePsiCriterionUniformizer S v)
    (SourcePsiCriterionUniformizer_algebraMap_ne_zero S v)
  have hCint : SourcePsiChangeIntegral S v M C :=
    uniformizerDivisibility_change_integral S v M hdiv
  have hint : IsCompletionIntegralElement S v
      (C.u : SourcePsiCompletionFractionField S v) :=
    (uniformizerDivisibility_scaling_integral_nonunit S v).1
  have hunit : IsCompletionIntegralUnit S v
      (C.u : SourcePsiCompletionFractionField S v) :=
    hmin C hCint hint
  exact (uniformizerDivisibility_scaling_integral_nonunit S v).2 hunit

/-- Corrected minimality excludes uniformizer uniform divisibility. -/
theorem SourcePsiIntegralModelMinimalCorrected_no_uniformizerDivisibility
    (M : SourcePsiIntegralModelData S v)
    (hmin : SourcePsiIntegralModelMinimalCorrected S v M) :
    ¬ SourcePsiUniformlyDivisible S v M
      (SourcePsiCriterionUniformizer S v) :=
  fun hdiv =>
    SourcePsiIntegralModel_not_minimalCorrected_of_uniformizerDivisibility S v M hdiv hmin

/-! ## Exact minimal-model criterion residual

Proved:
- corrected minimality is equivalent to absence of an integral change with
  integral nonunit scaling;
- any integral nonunit scaling factor is divisible by the actual uniformizer;
- uniformizer uniform divisibility gives the explicit integral uniformizer
  scaling and obstructs corrected minimality.

Still missing:
1. general (u,r,s,t) absorption: a uniformizer factor of u does not yet produce
   a pure uniformizer-scaled change with r = s = t = 0 while keeping all
   transformed coefficients integral;
2. the converse: corrected minimality from absence of all uniformizer-scaled
   reductions (requires the general absorption/normalisation);
3. full minimal-model existence/uniqueness;
4. comparison with source special fiber and stable reduction.

These are exact residual proof steps.  No model or change is fabricated.

end LeanFormal.IUT.SourcePsiMinimalModelCriterion

end