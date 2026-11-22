/-
  Converse direction of the corrected minimality criterion.

  Corrected minimality excludes exactly the integral changes with integral
  nonunit scaling.  Every integral nonunit scaling factor has a uniformizer
  factor, so corrected minimality excludes uniformizer-divisible integral
  changes.  The remaining changes are classified as:
  * integral unit scaling (allowed isomorphisms of integral models);
  * integral nonunit scaling (uniformizer-divisible obstruction);
  * nonintegral scaling (outside the corrected criterion; scales the discriminant
    upward and is not a minimality counterexample).

  The general absorption of a uniformizer factor into a pure (u=pi,r=s=t=0)
  change plus an integral residual change remains the exact residual.  No model
  or change is fabricated.
-/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiMinimalModelCriterion

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.SourcePsiMinimalModelConverse

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralUnits
open LeanFormal.IUT.SourcePsiIntegralUnitsCompletion
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiIntegralModelMinimality
open LeanFormal.IUT.AdicCompletionFractionField
open LeanFormal.IUT.SourcePsiResidueRingFinite
open LeanFormal.IUT.SourcePsiMinimalModelCriterion
open IsDedekindDomain HeightOneSpectrum

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))
  (M : SourcePsiIntegralModelData S v)

/-- The scaling factor of a change is an integral unit. -/
def SourcePsiScalingIntegralUnit
    (C : VariableChange (SourcePsiCompletionFractionField S v)) : Prop :=
  IsCompletionIntegralUnit S v (C.u : SourcePsiCompletionFractionField S v)

/-- The scaling factor is integral but not a unit. -/
def SourcePsiScalingIntegralNonunit
    (C : VariableChange (SourcePsiCompletionFractionField S v)) : Prop :=
  IsCompletionIntegralElement S v (C.u : SourcePsiCompletionFractionField S v) ∧
    ¬ IsCompletionIntegralUnit S v (C.u : SourcePsiCompletionFractionField S v)

/-- The scaling factor is not integral. -/
def SourcePsiScalingNonintegral
    (C : VariableChange (SourcePsiCompletionFractionField S v)) : Prop :=
  ¬ IsCompletionIntegralElement S v (C.u : SourcePsiCompletionFractionField S v)

/-- Exact classification of the scaling factor of any change. -/
theorem SourcePsiScaling_trichotomy
    (C : VariableChange (SourcePsiCompletionFractionField S v)) :
    SourcePsiScalingIntegralUnit S v C ∨
      SourcePsiScalingIntegralNonunit S v C ∨
        SourcePsiScalingNonintegral S v C := by
  by_cases hint : IsCompletionIntegralElement S v
      (C.u : SourcePsiCompletionFractionField S v)
  · by_cases hunit : IsCompletionIntegralUnit S v
        (C.u : SourcePsiCompletionFractionField S v)
    · exact Or.inl hunit
    · exact Or.inr (Or.inl ⟨hint, hunit⟩)
  · exact Or.inr (Or.inr hint)

/-- Corrected minimality is exactly absence of integral changes with integral
nonunit scaling. -/
theorem SourcePsiIntegralModelMinimalCorrected_iff_no_integralNonunit :
    SourcePsiIntegralModelMinimalCorrected S v M ↔
      ¬ ∃ C : VariableChange (SourcePsiCompletionFractionField S v),
        SourcePsiChangeIntegral S v M C ∧
          SourcePsiScalingIntegralNonunit S v C := by
  rw [SourcePsiIntegralModel_not_minimalCorrected_iff]
  constructor
  · intro hmin ⟨C, hC, hint, hunit⟩
    exact hmin ⟨C, hC, hint, hunit⟩
  · intro hno hmin
    exact hno (by
      classical
      by_contra hne
      apply hmin
      intro C hC hint hu
      by_contra hunit
      exact hne ⟨C, hC, hint, hunit⟩)

/-- Corrected minimality excludes any integral change whose scaling is an
integral nonunit. -/
theorem SourcePsiIntegralModelMinimalCorrected_no_integralNonunit_change
    (hmin : SourcePsiIntegralModelMinimalCorrected S v M)
    (C : VariableChange (SourcePsiCompletionFractionField S v))
    (hC : SourcePsiChangeIntegral S v M C)
    (hscale : SourcePsiScalingIntegralNonunit S v C) : False := by
  exact (SourcePsiIntegralModelMinimalCorrected_iff_no_integralNonunit S v M).mp
    hmin ⟨C, hC, hscale⟩

/-- Corrected minimality excludes uniformizer uniform divisibility. -/
theorem SourcePsiIntegralModelMinimalCorrected_no_uniformizerDivisibility
    (hmin : SourcePsiIntegralModelMinimalCorrected S v M) :
    ¬ SourcePsiUniformlyDivisible S v M (SourcePsiCriterionUniformizer S v) :=
  SourcePsiIntegralModelMinimalCorrected_no_uniformizerDivisibility S v M hmin

/-- A nonminimality witness is exactly an integral change with integral nonunit
scaling. -/
theorem SourcePsiIntegralModel_nonminimal_witness
    (h : ¬ SourcePsiIntegralModelMinimalCorrected S v M) :
    ∃ C : VariableChange (SourcePsiCompletionFractionField S v),
      SourcePsiChangeIntegral S v M C ∧
        SourcePsiScalingIntegralNonunit S v C := by
  obtain ⟨C, hC, hint, hunit⟩ :=
    (SourcePsiIntegralModel_not_minimalCorrected_iff S v M).mp h
  exact ⟨C, hC, hint, hunit⟩

/-- The scaling factor of any nonminimality witness has a uniformizer factor. -/
theorem SourcePsiIntegralModel_nonminimal_witness_uniformizer_factor
    (h : ¬ SourcePsiIntegralModelMinimalCorrected S v M) :
    ∃ (C : VariableChange (SourcePsiCompletionFractionField S v))
      (r' : SourcePsiCompletionIntegerRing S v),
        SourcePsiChangeIntegral S v M C ∧
          (C.u : SourcePsiCompletionFractionField S v) =
            algebraMap (SourcePsiCompletionIntegerRing S v)
              (SourcePsiCompletionFractionField S v)
              (SourcePsiCriterionUniformizer S v * r') := by
  obtain ⟨C, hC, hscale⟩ := SourcePsiIntegralModel_nonminimal_witness S v M h
  obtain ⟨r', hr'⟩ := nonunit_integral_change_has_uniformizer_factor S v M C
    hscale.1 hscale.2
  exact ⟨C, r', hC, hr'⟩

/-! ## Classification of the remaining changes

A change whose scaling is an integral unit is an isomorphism of integral models
and is not excluded by corrected minimality.  A change whose scaling is
nonintegral is outside the corrected criterion; it is not classified as a
minimality obstruction here.  The only excluded class is the integral nonunit
scaling class, and its scaling factor has a uniformizer factor.

## Exact absorption residual

Given a witness C with u = pi * r', one wants to write C as a pure uniformizer
scaling (u = pi, r = s = t = 0) followed by an integral residual change, and then
show that the residual change either has unit scaling (so is harmless) or yields
a pure uniformizer-divisible coefficient criterion.  The group law of
Weierstrass changes mixes u,r,s,t; the integrality of the residual r',s',t' is
not automatic.  This absorption/normalisation is the exact missing step.

Missing exact residual:
1. decomposition C = C_pure_uniformizer * C_residual with C_residual integral;
2. integrality of the residual r',s',t';
3. the converse: absence of pure uniformizer-divisible integral changes implies
   corrected minimality;
4. full minimal-model existence/uniqueness;
5. source special-fiber/stable reduction comparison.

No model or change is fabricated.
-/

/-! ## Pure uniformizer changes and absorption data

/-- The pure uniformizer scaling change with u = pi^n and r = s = t = 0. -/
noncomputable def sourcePsiPureUniformizerChange (n : ℕ) :
    VariableChange (SourcePsiCompletionFractionField S v) where
  u := Units.mk0
    ((algebraMap (SourcePsiCompletionIntegerRing S v)
      (SourcePsiCompletionFractionField S v)
      (SourcePsiCriterionUniformizer S v)) ^ n)
    (pow_ne_zero n (SourcePsiCriterionUniformizer_algebraMap_ne_zero S v))
  r := 0
  s := 0
  t := 0

/-- Exact absorption datum: a change factors as a pure uniformizer scaling
followed by an integral residual change.  No inhabitant is asserted. -/
structure SourcePsiUniformizerAbsorptionData
    (C : VariableChange (SourcePsiCompletionFractionField S v)) where
  n : ℕ
  n_pos : 0 < n
  residual : VariableChange (SourcePsiCompletionFractionField S v)
  decomposition : C = sourcePsiPureUniformizerChange S v n * residual
  residual_integral : SourcePsiIntegralWeierstrassCurve S v
    (residual • (M.curve.map
      (algebraMap (SourcePsiCompletionIntegerRing S v)
        (SourcePsiCompletionFractionField S v))))

/-- Exact absorption residual for a nonminimality witness. -/
def SourcePsiUniformizerAbsorptionResidual : Prop :=
  ∃ (C : VariableChange (SourcePsiCompletionFractionField S v)),
    SourcePsiChangeIntegral S v M C ∧
      SourcePsiScalingIntegralNonunit S v C ∧
        Nonempty (SourcePsiUniformizerAbsorptionData S v M C)

theorem SourcePsiScalingIntegralUnit_not_nonunit
    (C : VariableChange (SourcePsiCompletionFractionField S v))
    (h : SourcePsiScalingIntegralUnit S v C) :
    ¬ SourcePsiScalingIntegralNonunit S v C :=
  fun hnu => hnu.2 h

theorem SourcePsiScalingIntegralNonunit_not_unit
    (C : VariableChange (SourcePsiCompletionFractionField S v))
    (h : SourcePsiScalingIntegralNonunit S v C) :
    ¬ SourcePsiScalingIntegralUnit S v C :=
  fun hu => h.2 hu

theorem SourcePsiScalingIntegralNonunit_not_nonintegral
    (C : VariableChange (SourcePsiCompletionFractionField S v))
    (h : SourcePsiScalingIntegralNonunit S v C) :
    ¬ SourcePsiScalingNonintegral S v C :=
  fun hni => hni h.1

theorem SourcePsiScalingNonintegral_not_integral
    (C : VariableChange (SourcePsiCompletionFractionField S v))
    (h : SourcePsiScalingNonintegral S v C) :
    ¬ IsCompletionIntegralElement S v
      (C.u : SourcePsiCompletionFractionField S v) := h

/-- Nonintegral scaling changes are outside the corrected minimality criterion:
the criterion only constrains integral scaling factors. -/
theorem SourcePsiIntegralModelMinimalCorrected_not_obstructed_by_nonintegral_scaling
    (hmin : SourcePsiIntegralModelMinimalCorrected S v M)
    (C : VariableChange (SourcePsiCompletionFractionField S v))
    (hC : SourcePsiChangeIntegral S v M C)
    (hni : SourcePsiScalingNonintegral S v C) :
    ¬ SourcePsiScalingIntegralNonunit S v C :=
  fun hnu => hni hnu.1

/-- Integral unit scaling changes are allowed isomorphisms of integral models;
the corrected criterion does not exclude them. -/
theorem SourcePsiIntegralModelMinimalCorrected_allows_integralUnit_scaling
    (hmin : SourcePsiIntegralModelMinimalCorrected S v M)
    (C : VariableChange (SourcePsiCompletionFractionField S v))
    (hC : SourcePsiChangeIntegral S v M C)
    (hu : SourcePsiScalingIntegralUnit S v C) :
    IsCompletionIntegralUnit S v (C.u : SourcePsiCompletionFractionField S v) :=
  hu

/-- Corrected minimality is exactly the absence of a nonminimality witness
(package form). -/
theorem SourcePsiIntegralModelMinimalCorrected_iff_no_witness :
    SourcePsiIntegralModelMinimalCorrected S v M ↔
      ¬ ∃ C : VariableChange (SourcePsiCompletionFractionField S v),
        SourcePsiChangeIntegral S v M C ∧
          SourcePsiScalingIntegralNonunit S v C :=
  SourcePsiIntegralModelMinimalCorrected_iff_no_integralNonunit S v M

end LeanFormal.IUT.SourcePsiMinimalModelConverse

end