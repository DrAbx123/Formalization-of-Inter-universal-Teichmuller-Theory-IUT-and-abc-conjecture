/-
  Uniqueness and minimality of the constructed integral model under all
  Weierstrass changes.

  The corrected minimality criterion says that an integral model is minimal
  exactly when there is no integral change of coordinates with integral nonunit
  scaling factor.  Consequently every integral change out of a minimal model has
  unit scaling.  A nonunit integral change is therefore an immediate contradiction
  to minimality; the uniformizer absorption gives the concrete residual change
  decomposition for such a witness.

  The file proves the conditional uniqueness/minimality statements exactly.  It
  does not fabricate an actual model with no nonunit changes; that existence is
  recorded as the exact residual.
-/
import Mathlib
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiIntegralUnits
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiIntegralUnitsCompletion
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiIntegralModel
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiIntegralModelMinimality
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiMinimalModelCriterion
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiMinimalModelConverse
import LeanFormal.IUT.Foundations.Arithmetic.PrimeLabels


set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.SourcePsiMinimalModelUniqueness

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralUnits
open LeanFormal.IUT.SourcePsiIntegralUnitsCompletion
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiIntegralModelMinimality
open LeanFormal.IUT.AdicCompletionFractionField
open LeanFormal.IUT.SourcePsiResidueRingFinite
open LeanFormal.IUT.SourcePsiMinimalModelCriterion
open LeanFormal.IUT.SourcePsiMinimalModelConverse
open LeanFormal.IUT.SourcePsiUniformizerAbsorptionFinal
open IsDedekindDomain HeightOneSpectrum

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

/-- A change from one integral model to another: it carries the base-changed
curve of the first model to the base-changed curve of the second. -/
def SourcePsiChangeBetween (M N : SourcePsiIntegralModelData S v)
    (C : VariableChange (SourcePsiCompletionFractionField S v)) : Prop :=
  C • (M.curve.map (algebraMap (SourcePsiCompletionIntegerRing S v)
    (SourcePsiCompletionFractionField S v))) =
    N.curve.map (algebraMap (SourcePsiCompletionIntegerRing S v)
      (SourcePsiCompletionFractionField S v))

/-- An integral change between two models: the transformed curve is the second
integral model, hence has integral coefficients. -/
def SourcePsiIntegralChangeBetween (M N : SourcePsiIntegralModelData S v)
    (C : VariableChange (SourcePsiCompletionFractionField S v)) : Prop :=
  SourcePsiChangeBetween S v M N C ∧ SourcePsiChangeIntegral S v M C

/-- A change whose scaling factor is a completion integral unit. -/
def SourcePsiUnitChange
    (C : VariableChange (SourcePsiCompletionFractionField S v)) : Prop :=
  IsCompletionIntegralUnit S v (C.u : SourcePsiCompletionFractionField S v)

/-- A change whose scaling factor is integral but nonunit. -/
def SourcePsiNonunitIntegralChange
    (C : VariableChange (SourcePsiCompletionFractionField S v)) : Prop :=
  SourcePsiScalingIntegralNonunit S v C

/-- Corrected minimality is exactly absence of an integral change with integral
nonunit scaling. -/
theorem SourcePsiMinimalModel_iff_no_nonunit_integral_change
    (M : SourcePsiIntegralModelData S v) :
    SourcePsiIntegralModelMinimalCorrected S v M ↔
      ¬ ∃ C : VariableChange (SourcePsiCompletionFractionField S v),
        SourcePsiChangeIntegral S v M C ∧
          SourcePsiNonunitIntegralChange S v C :=
  SourcePsiIntegralModelMinimalCorrected_iff_no_integralNonunit S v M

/-- An integral nonunit change contradicts corrected minimality. -/
theorem SourcePsiMinimalModel_not_minimal_of_nonunit_integral_change
    (M : SourcePsiIntegralModelData S v)
    (C : VariableChange (SourcePsiCompletionFractionField S v))
    (hC : SourcePsiChangeIntegral S v M C)
    (hscale : SourcePsiNonunitIntegralChange S v C) :
    ¬ SourcePsiIntegralModelMinimalCorrected S v M :=
  fun hmin =>
    (SourcePsiMinimalModel_iff_no_nonunit_integral_change S v M).mp hmin
      ⟨C, hC, hscale⟩

/-- Contrapositive form: if a model is minimal, no integral change with integral
nonunit scaling can exist. -/
theorem SourcePsiMinimalModel_no_nonunit_integral_change
    (M : SourcePsiIntegralModelData S v)
    (hmin : SourcePsiIntegralModelMinimalCorrected S v M) :
    ¬ ∃ C : VariableChange (SourcePsiCompletionFractionField S v),
      SourcePsiChangeIntegral S v M C ∧
        SourcePsiNonunitIntegralChange S v C :=
  (SourcePsiMinimalModel_iff_no_nonunit_integral_change S v M).mp hmin

/-- Every integral change out of a minimal model has unit scaling, provided the
scaling factor is integral. -/
theorem SourcePsiMinimalModel_integral_change_scaling_unit
    (M : SourcePsiIntegralModelData S v)
    (hmin : SourcePsiIntegralModelMinimalCorrected S v M)
    (C : VariableChange (SourcePsiCompletionFractionField S v))
    (hC : SourcePsiChangeIntegral S v M C)
    (hint : IsCompletionIntegralElement S v
      (C.u : SourcePsiCompletionFractionField S v)) :
    IsCompletionIntegralUnit S v
      (C.u : SourcePsiCompletionFractionField S v) :=
  hmin C hC hint

/-- If an integral change has integral nonunit scaling, corrected minimality is
impossible; equivalently, a minimal model cannot be the source of such a change. -/
theorem SourcePsiMinimalModel_change_scaling_dichotomy
    (M : SourcePsiIntegralModelData S v)
    (C : VariableChange (SourcePsiCompletionFractionField S v))
    (hC : SourcePsiChangeIntegral S v M C)
    (hint : IsCompletionIntegralElement S v
      (C.u : SourcePsiCompletionFractionField S v)) :
    IsCompletionIntegralUnit S v
        (C.u : SourcePsiCompletionFractionField S v) ∨
      ¬ SourcePsiIntegralModelMinimalCorrected S v M := by
  by_cases hunit : IsCompletionIntegralUnit S v
      (C.u : SourcePsiCompletionFractionField S v)
  · exact Or.inl hunit
  · exact Or.inr
      (SourcePsiMinimalModel_not_minimal_of_nonunit_integral_change S v M C hC
        ⟨hint, hunit⟩)

/-- Minimal source of an integral change between two models forces unit scaling
(when the scaling factor is integral). -/
theorem SourcePsiMinimalModel_change_between_models_scaling_unit
    (M N : SourcePsiIntegralModelData S v)
    (hmin : SourcePsiIntegralModelMinimalCorrected S v M)
    (C : VariableChange (SourcePsiCompletionFractionField S v))
    (hC : SourcePsiIntegralChangeBetween S v M N C)
    (hint : IsCompletionIntegralElement S v
      (C.u : SourcePsiCompletionFractionField S v)) :
    IsCompletionIntegralUnit S v
      (C.u : SourcePsiCompletionFractionField S v) :=
  SourcePsiMinimalModel_integral_change_scaling_unit S v M hmin C hC.2 hint

/-- No nonunit integral change between a minimal model and any other integral
model exists. -/
theorem SourcePsiMinimalModel_no_nonunit_change_between_models
    (M N : SourcePsiIntegralModelData S v)
    (hmin : SourcePsiIntegralModelMinimalCorrected S v M) :
    ¬ ∃ C : VariableChange (SourcePsiCompletionFractionField S v),
      SourcePsiIntegralChangeBetween S v M N C ∧
        SourcePsiNonunitIntegralChange S v C := by
  rintro ⟨C, hC, hscale⟩
  exact (SourcePsiMinimalModel_no_nonunit_integral_change S v M hmin)
    ⟨C, hC.2, hscale⟩

/-- Absorption witness package for a nonminimality witness: the witness has the
exact pure-uniformizer absorption with integral residual. -/
theorem SourcePsiMinimalModel_nonminimal_witness_has_absorption
    (M : SourcePsiIntegralModelData S v)
    (h : ¬ SourcePsiIntegralModelMinimalCorrected S v M) :
    ∃ C : VariableChange (SourcePsiCompletionFractionField S v),
      SourcePsiChangeIntegral S v M C ∧
        SourcePsiNonunitIntegralChange S v C ∧
          Nonempty (SourcePsiUniformizerAbsorptionData S v M C) := by
  obtain ⟨C, hC, hscale⟩ :=
    SourcePsiIntegralModel_nonminimal_witness S v M h
  exact ⟨C, hC, hscale,
    sourcePsiUniformizerAbsorptionData_exists S v M C 1 (by norm_num) hC⟩

/-- A nonminimality witness can be absorbed with a pure uniformizer factor; the
residual is integral, so the obstruction is carried entirely by the residual
change. -/
theorem SourcePsiMinimalModel_nonminimal_witness_absorption_residual
    (M : SourcePsiIntegralModelData S v)
    (h : ¬ SourcePsiIntegralModelMinimalCorrected S v M) :
    ∃ (C : VariableChange (SourcePsiCompletionFractionField S v))
      (R : VariableChange (SourcePsiCompletionFractionField S v)),
        SourcePsiChangeIntegral S v M C ∧
          SourcePsiNonunitIntegralChange S v C ∧
            C = sourcePsiPureUniformizerChange S v 1 * R ∧
              SourcePsiIntegralWeierstrassCurve S v
                (R • (M.curve.map
                  (algebraMap (SourcePsiCompletionIntegerRing S v)
                    (SourcePsiCompletionFractionField S v)))) := by
  obtain ⟨C, hC, hscale, hdata⟩ :=
    SourcePsiMinimalModel_nonminimal_witness_has_absorption S v M h
  rcases hdata with ⟨data⟩
  exact ⟨C, data.residual, hC, hscale, data.decomposition,
    data.residual_integral⟩

/-- Model-minimality criterion, final form: minimality is equivalent to the
absence of the explicit integral nonunit scaling witnesses. -/
theorem SourcePsiMinimalModel_minimality_criterion_final
    (M : SourcePsiIntegralModelData S v) :
    SourcePsiIntegralModelMinimalCorrected S v M ↔
      ∀ C : VariableChange (SourcePsiCompletionFractionField S v),
        SourcePsiChangeIntegral S v M C →
          IsCompletionIntegralElement S v
              (C.u : SourcePsiCompletionFractionField S v) →
            IsCompletionIntegralUnit S v
              (C.u : SourcePsiCompletionFractionField S v) :=
  Iff.rfl

/-- Exact residual predicate for model minimality: an actual model all of whose
integral changes have unit scaling.  No inhabitant is asserted. -/
def SourcePsiMinimalModelExistenceResidual : Prop :=
  ∃ M : SourcePsiIntegralModelData S v,
    SourcePsiIntegralModelMinimalCorrected S v M

/-- A minimal model has no nonunit integral change; this is the exact uniqueness
statement proved here. -/
theorem SourcePsiMinimalModel_uniqueness_statement
    (M : SourcePsiIntegralModelData S v)
    (hmin : SourcePsiIntegralModelMinimalCorrected S v M) :
    (¬ ∃ C : VariableChange (SourcePsiCompletionFractionField S v),
      SourcePsiChangeIntegral S v M C ∧
        SourcePsiNonunitIntegralChange S v C) ∧
      (∀ C : VariableChange (SourcePsiCompletionFractionField S v),
        SourcePsiChangeIntegral S v M C →
          IsCompletionIntegralElement S v
              (C.u : SourcePsiCompletionFractionField S v) →
            IsCompletionIntegralUnit S v
              (C.u : SourcePsiCompletionFractionField S v)) :=
  ⟨SourcePsiMinimalModel_no_nonunit_integral_change S v M hmin,
    fun C hC hint =>
      SourcePsiMinimalModel_integral_change_scaling_unit S v M hmin C hC hint⟩



/-- Minimality criterion in all-changes form: every integral change with integral
scaling factor has unit scaling. -/
theorem SourcePsiMinimalModel_minimality_criterion_all_changes
    (M : SourcePsiIntegralModelData S v) :
    SourcePsiIntegralModelMinimalCorrected S v M ↔
      ∀ C : VariableChange (SourcePsiCompletionFractionField S v),
        SourcePsiChangeIntegral S v M C →
          IsCompletionIntegralElement S v
              (C.u : SourcePsiCompletionFractionField S v) →
            IsCompletionIntegralUnit S v
              (C.u : SourcePsiCompletionFractionField S v) :=
  Iff.rfl

/-- Nonminimality is exactly the existence of an integral change with integral
nonunit scaling. -/
theorem SourcePsiMinimalModel_nonminimality_iff_exists_nonunit
    (M : SourcePsiIntegralModelData S v) :
    (¬ SourcePsiIntegralModelMinimalCorrected S v M) ↔
      ∃ C : VariableChange (SourcePsiCompletionFractionField S v),
        SourcePsiChangeIntegral S v M C ∧
          SourcePsiNonunitIntegralChange S v C :=
  (SourcePsiMinimalModel_iff_no_nonunit_integral_change S v M).symm.not

/-- The scaling factor of an absorbed nonminimality witness is either a unit or a
nonunit; the nonunit case is the remaining exact residual. -/
theorem SourcePsiMinimalModel_absorption_scaling_dichotomy
    (M : SourcePsiIntegralModelData S v)
    (h : ¬ SourcePsiIntegralModelMinimalCorrected S v M) :
    ∃ (C R : VariableChange (SourcePsiCompletionFractionField S v)),
      SourcePsiChangeIntegral S v M C ∧
        SourcePsiNonunitIntegralChange S v C ∧
          C = sourcePsiPureUniformizerChange S v 1 * R ∧
            SourcePsiIntegralWeierstrassCurve S v
              (R • (M.curve.map
                (algebraMap (SourcePsiCompletionIntegerRing S v)
                  (SourcePsiCompletionFractionField S v)))) ∧
              (IsCompletionIntegralUnit S v
                  (R.u : SourcePsiCompletionFractionField S v) ∨
                ¬ IsCompletionIntegralUnit S v
                  (R.u : SourcePsiCompletionFractionField S v)) := by
  obtain ⟨C, R, hC, hscale, hdecomp, hint⟩ :=
    SourcePsiMinimalModel_nonminimal_witness_absorption_residual S v M h
  exact ⟨C, R, hC, hscale, hdecomp, hint,
    em (IsCompletionIntegralUnit S v
      (R.u : SourcePsiCompletionFractionField S v))⟩

/-- If every integral change out of M has unit scaling, M is minimal.  This is
the converse direction packaged as existence of no nonunit witness. -/
theorem SourcePsiMinimalModel_minimality_of_all_changes_unit
    (M : SourcePsiIntegralModelData S v)
    (h : ∀ C : VariableChange (SourcePsiCompletionFractionField S v),
      SourcePsiChangeIntegral S v M C →
        IsCompletionIntegralElement S v
            (C.u : SourcePsiCompletionFractionField S v) →
          IsCompletionIntegralUnit S v
            (C.u : SourcePsiCompletionFractionField S v)) :
    SourcePsiIntegralModelMinimalCorrected S v M :=
  h

/-- A minimal model is unique in the following exact scaling sense: any integral
change from it to another integral model has unit scaling, provided the scaling
factor is integral. -/
theorem SourcePsiMinimalModel_unique_scaling_to_any_model
    (M N : SourcePsiIntegralModelData S v)
    (hmin : SourcePsiIntegralModelMinimalCorrected S v M)
    (C : VariableChange (SourcePsiCompletionFractionField S v))
    (hC : SourcePsiIntegralChangeBetween S v M N C)
    (hint : IsCompletionIntegralElement S v
      (C.u : SourcePsiCompletionFractionField S v)) :
    IsCompletionIntegralUnit S v
      (C.u : SourcePsiCompletionFractionField S v) ∧
      ¬ SourcePsiNonunitIntegralChange S v C :=
  ⟨SourcePsiMinimalModel_change_between_models_scaling_unit S v M N hmin C hC hint,
    fun hscale =>
      (SourcePsiMinimalModel_no_nonunit_change_between_models S v M N hmin)
        ⟨C, hC, hscale⟩⟩

/-! ## Exact uniqueness/minimality residual

Proved:
- corrected minimality is exactly absence of integral changes with integral
  nonunit scaling;
- any integral nonunit change contradicts minimality;
- every integral change out of a minimal model has unit scaling (when the scaling
  factor is integral);
- no nonunit change between a minimal model and another integral model exists;
- nonminimality witnesses admit the exact pure-uniformizer absorption with
  integral residual;
- the final minimality criterion is the corrected criterion.

NOT constructed:
1. an actual integral model with no nonunit integral change;
2. integrality of the scaling factor for a general change between two minimal
   models;
3. full uniqueness of minimal models up to integral unit change/translation;
4. comparison of minimal models with the source special fiber and stable
   reduction.

These are the exact residual objects.  No model or change is fabricated.
-/
end LeanFormal.IUT.SourcePsiMinimalModelUniqueness

end