/-
  Final absorption of a uniformizer factor from a general integral change.

  For any integral change C and any n > 0, left multiplication by the pure
  uniformizer scaling P_n with u = pi^n first, r = s = t = 0, gives a residual
  change R with C = P_n * R.  If C has integral transformed coefficients, then R
  also has integral transformed coefficients: the residual coefficients are
  pi^{n w} times the integral C-coefficients at the Weierstrass weights.  This
  constructs the exact absorption datum, with no missing integrality field.

  The converse from absence of pure uniformizer changes is then bounded: a
  residual with unit scaling is an integral unit change, not a pure obstruction;
  the exact residual is the normalization of that unit residual.
-/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiMinimalModelConverse

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.SourcePsiUniformizerAbsorptionFinal

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralUnits
open LeanFormal.IUT.SourcePsiIntegralUnitsCompletion
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiIntegralModelMinimality
open LeanFormal.IUT.AdicCompletionFractionField
open LeanFormal.IUT.SourcePsiResidueRingFinite
open LeanFormal.IUT.SourcePsiMinimalModelCriterion
open LeanFormal.IUT.SourcePsiMinimalModelConverse
open IsDedekindDomain HeightOneSpectrum

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))
  (M : SourcePsiIntegralModelData S v)

/-- The base-changed integral model curve over K. -/
abbrev SourcePsiAbsorptionBaseCurve : WeierstrassCurve (SourcePsiCompletionFractionField S v) :=
  M.curve.map (algebraMap (SourcePsiCompletionIntegerRing S v)
    (SourcePsiCompletionFractionField S v))

/-- The residual change after absorbing the pure uniformizer scaling. -/
noncomputable def sourcePsiAbsorptionResidual
    (C : VariableChange (SourcePsiCompletionFractionField S v)) (n : ℕ) :
    VariableChange (SourcePsiCompletionFractionField S v) where
  u := (sourcePsiPureUniformizerChange S v n).u⁻¹ * C.u
  r := C.r
  s := C.s
  t := C.t

/-- Algebraic absorption: C = P_n * R. -/
theorem sourcePsiAbsorption_decomposition
    (C : VariableChange (SourcePsiCompletionFractionField S v)) (n : ℕ) :
    C = sourcePsiPureUniformizerChange S v n *
      sourcePsiAbsorptionResidual S v C n := by
  ext <;> simp [VariableChange.mul_def, sourcePsiPureUniformizerChange,
    sourcePsiAbsorptionResidual]

/-- The pure uniformizer scaling has r = s = t = 0. -/
theorem sourcePsiPureUniformizerChange_r (n : ℕ) :
    (sourcePsiPureUniformizerChange S v n).r = 0 := rfl

theorem sourcePsiPureUniformizerChange_s (n : ℕ) :
    (sourcePsiPureUniformizerChange S v n).s = 0 := rfl

theorem sourcePsiPureUniformizerChange_t (n : ℕ) :
    (sourcePsiPureUniformizerChange S v n).t = 0 := rfl

/-- The pure uniformizer scaling coefficient formulas. -/
theorem SourcePsiAbsorption_pure_a₁ (n : ℕ)
    (V : WeierstrassCurve (SourcePsiCompletionFractionField S v)) :
    ((sourcePsiPureUniformizerChange S v n) • V).a₁ =
      ((sourcePsiPureUniformizerChange S v n).u : SourcePsiCompletionFractionField S v)⁻¹ *
        V.a₁ := by
  simp [sourcePsiPureUniformizerChange, WeierstrassCurve.variableChange_a₁]

theorem SourcePsiAbsorption_pure_a₂ (n : ℕ)
    (V : WeierstrassCurve (SourcePsiCompletionFractionField S v)) :
    ((sourcePsiPureUniformizerChange S v n) • V).a₂ =
      ((sourcePsiPureUniformizerChange S v n).u : SourcePsiCompletionFractionField S v)⁻¹ ^ 2 *
        V.a₂ := by
  simp [sourcePsiPureUniformizerChange, WeierstrassCurve.variableChange_a₂]

theorem SourcePsiAbsorption_pure_a₃ (n : ℕ)
    (V : WeierstrassCurve (SourcePsiCompletionFractionField S v)) :
    ((sourcePsiPureUniformizerChange S v n) • V).a₃ =
      ((sourcePsiPureUniformizerChange S v n).u : SourcePsiCompletionFractionField S v)⁻¹ ^ 3 *
        V.a₃ := by
  simp [sourcePsiPureUniformizerChange, WeierstrassCurve.variableChange_a₃]

theorem SourcePsiAbsorption_pure_a₄ (n : ℕ)
    (V : WeierstrassCurve (SourcePsiCompletionFractionField S v)) :
    ((sourcePsiPureUniformizerChange S v n) • V).a₄ =
      ((sourcePsiPureUniformizerChange S v n).u : SourcePsiCompletionFractionField S v)⁻¹ ^ 4 *
        V.a₄ := by
  simp [sourcePsiPureUniformizerChange, WeierstrassCurve.variableChange_a₄]

theorem SourcePsiAbsorption_pure_a₆ (n : ℕ)
    (V : WeierstrassCurve (SourcePsiCompletionFractionField S v)) :
    ((sourcePsiPureUniformizerChange S v n) • V).a₆ =
      ((sourcePsiPureUniformizerChange S v n).u : SourcePsiCompletionFractionField S v)⁻¹ ^ 6 *
        V.a₆ := by
  simp [sourcePsiPureUniformizerChange, WeierstrassCurve.variableChange_a₆]

/-- The residual is integral whenever C is integral: the residual coefficients
are pi^{n w} times the integral C-coefficients at the Weierstrass weights. -/
theorem sourcePsiAbsorptionResidual_integral
    (C : VariableChange (SourcePsiCompletionFractionField S v)) (n : ℕ)
    (hC : SourcePsiIntegralWeierstrassCurve S v (C • SourcePsiAbsorptionBaseCurve S v M)) :
    SourcePsiIntegralWeierstrassCurve S v
      (sourcePsiAbsorptionResidual S v C n • SourcePsiAbsorptionBaseCurve S v M) := by
  obtain ⟨c₁, h₁⟩ := hC.1
  obtain ⟨c₂, h₂⟩ := hC.2.1
  obtain ⟨c₃, h₃⟩ := hC.2.2.1
  obtain ⟨c₄, h₄⟩ := hC.2.2.2.1
  obtain ⟨c₆, h₆⟩ := hC.2.2.2.2
  refine ⟨⟨(SourcePsiCriterionUniformizer S v) ^ n * c₁, ?_⟩,
    ⟨(SourcePsiCriterionUniformizer S v) ^ (2 * n) * c₂, ?_⟩,
    ⟨(SourcePsiCriterionUniformizer S v) ^ (3 * n) * c₃, ?_⟩,
    ⟨(SourcePsiCriterionUniformizer S v) ^ (4 * n) * c₄, ?_⟩,
    ⟨(SourcePsiCriterionUniformizer S v) ^ (6 * n) * c₆, ?_⟩⟩
  · have hdec := sourcePsiAbsorption_decomposition S v C n
    have hsmul : C • SourcePsiAbsorptionBaseCurve S v M =
        (sourcePsiPureUniformizerChange S v n) •
          (sourcePsiAbsorptionResidual S v C n • SourcePsiAbsorptionBaseCurve S v M) := by
      rw [hdec, mul_smul]
    calc
      algebraMap (SourcePsiCompletionIntegerRing S v)
          (SourcePsiCompletionFractionField S v)
          ((SourcePsiCriterionUniformizer S v) ^ n * c₁)
          = algebraMap (SourcePsiCompletionIntegerRing S v)
              (SourcePsiCompletionFractionField S v)
              ((SourcePsiCriterionUniformizer S v) ^ n) * (C • SourcePsiAbsorptionBaseCurve S v M).a₁ := by
            rw [map_mul, h₁]
      _ = (sourcePsiPureUniformizerChange S v n).u *
            ((sourcePsiPureUniformizerChange S v n) • (sourcePsiAbsorptionResidual S v C n • SourcePsiAbsorptionBaseCurve S v M)).a₁ := by
            rw [← hsmul]
            simp [sourcePsiPureUniformizerChange, WeierstrassCurve.variableChange_a₁, mul_comm]
      _ = (sourcePsiAbsorptionResidual S v C n • SourcePsiAbsorptionBaseCurve S v M).a₁ := by
            rw [SourcePsiAbsorption_pure_a₁]
            field_simp
            ring
  · have hdec := sourcePsiAbsorption_decomposition S v C n
    have hsmul : C • SourcePsiAbsorptionBaseCurve S v M =
        (sourcePsiPureUniformizerChange S v n) •
          (sourcePsiAbsorptionResidual S v C n • SourcePsiAbsorptionBaseCurve S v M) := by
      rw [hdec, mul_smul]
    calc
      algebraMap (SourcePsiCompletionIntegerRing S v)
          (SourcePsiCompletionFractionField S v)
          ((SourcePsiCriterionUniformizer S v) ^ (2 * n) * c₂)
          = algebraMap (SourcePsiCompletionIntegerRing S v)
              (SourcePsiCompletionFractionField S v)
              ((SourcePsiCriterionUniformizer S v) ^ (2 * n)) * (C • SourcePsiAbsorptionBaseCurve S v M).a₂ := by
            rw [map_mul, h₂]
      _ = (sourcePsiPureUniformizerChange S v n).u ^ 2 *
            ((sourcePsiPureUniformizerChange S v n) • (sourcePsiAbsorptionResidual S v C n • SourcePsiAbsorptionBaseCurve S v M)).a₂ := by
            rw [← hsmul]
            simp [sourcePsiPureUniformizerChange, WeierstrassCurve.variableChange_a₂, mul_comm, mul_assoc, mul_left_comm]
      _ = (sourcePsiAbsorptionResidual S v C n • SourcePsiAbsorptionBaseCurve S v M).a₂ := by
            rw [SourcePsiAbsorption_pure_a₂]
            field_simp
            ring
  · have hdec := sourcePsiAbsorption_decomposition S v C n
    have hsmul : C • SourcePsiAbsorptionBaseCurve S v M =
        (sourcePsiPureUniformizerChange S v n) •
          (sourcePsiAbsorptionResidual S v C n • SourcePsiAbsorptionBaseCurve S v M) := by
      rw [hdec, mul_smul]
    calc
      algebraMap (SourcePsiCompletionIntegerRing S v)
          (SourcePsiCompletionFractionField S v)
          ((SourcePsiCriterionUniformizer S v) ^ (3 * n) * c₃)
          = algebraMap (SourcePsiCompletionIntegerRing S v)
              (SourcePsiCompletionFractionField S v)
              ((SourcePsiCriterionUniformizer S v) ^ (3 * n)) * (C • SourcePsiAbsorptionBaseCurve S v M).a₃ := by
            rw [map_mul, h₃]
      _ = (sourcePsiPureUniformizerChange S v n).u ^ 3 *
            ((sourcePsiPureUniformizerChange S v n) • (sourcePsiAbsorptionResidual S v C n • SourcePsiAbsorptionBaseCurve S v M)).a₃ := by
            rw [← hsmul]
            simp [sourcePsiPureUniformizerChange, WeierstrassCurve.variableChange_a₃, mul_comm, mul_assoc, mul_left_comm]
      _ = (sourcePsiAbsorptionResidual S v C n • SourcePsiAbsorptionBaseCurve S v M).a₃ := by
            rw [SourcePsiAbsorption_pure_a₃]
            field_simp
            ring
  · have hdec := sourcePsiAbsorption_decomposition S v C n
    have hsmul : C • SourcePsiAbsorptionBaseCurve S v M =
        (sourcePsiPureUniformizerChange S v n) •
          (sourcePsiAbsorptionResidual S v C n • SourcePsiAbsorptionBaseCurve S v M) := by
      rw [hdec, mul_smul]
    calc
      algebraMap (SourcePsiCompletionIntegerRing S v)
          (SourcePsiCompletionFractionField S v)
          ((SourcePsiCriterionUniformizer S v) ^ (4 * n) * c₄)
          = algebraMap (SourcePsiCompletionIntegerRing S v)
              (SourcePsiCompletionFractionField S v)
              ((SourcePsiCriterionUniformizer S v) ^ (4 * n)) * (C • SourcePsiAbsorptionBaseCurve S v M).a₄ := by
            rw [map_mul, h₄]
      _ = (sourcePsiPureUniformizerChange S v n).u ^ 4 *
            ((sourcePsiPureUniformizerChange S v n) • (sourcePsiAbsorptionResidual S v C n • SourcePsiAbsorptionBaseCurve S v M)).a₄ := by
            rw [← hsmul]
            simp [sourcePsiPureUniformizerChange, WeierstrassCurve.variableChange_a₄, mul_comm, mul_assoc, mul_left_comm]
      _ = (sourcePsiAbsorptionResidual S v C n • SourcePsiAbsorptionBaseCurve S v M).a₄ := by
            rw [SourcePsiAbsorption_pure_a₄]
            field_simp
            ring
  · have hdec := sourcePsiAbsorption_decomposition S v C n
    have hsmul : C • SourcePsiAbsorptionBaseCurve S v M =
        (sourcePsiPureUniformizerChange S v n) •
          (sourcePsiAbsorptionResidual S v C n • SourcePsiAbsorptionBaseCurve S v M) := by
      rw [hdec, mul_smul]
    calc
      algebraMap (SourcePsiCompletionIntegerRing S v)
          (SourcePsiCompletionFractionField S v)
          ((SourcePsiCriterionUniformizer S v) ^ (6 * n) * c₆)
          = algebraMap (SourcePsiCompletionIntegerRing S v)
              (SourcePsiCompletionFractionField S v)
              ((SourcePsiCriterionUniformizer S v) ^ (6 * n)) * (C • SourcePsiAbsorptionBaseCurve S v M).a₆ := by
            rw [map_mul, h₆]
      _ = (sourcePsiPureUniformizerChange S v n).u ^ 6 *
            ((sourcePsiPureUniformizerChange S v n) • (sourcePsiAbsorptionResidual S v C n • SourcePsiAbsorptionBaseCurve S v M)).a₆ := by
            rw [← hsmul]
            simp [sourcePsiPureUniformizerChange, WeierstrassCurve.variableChange_a₆, mul_comm, mul_assoc, mul_left_comm]
      _ = (sourcePsiAbsorptionResidual S v C n • SourcePsiAbsorptionBaseCurve S v M).a₆ := by
            rw [SourcePsiAbsorption_pure_a₆]
            field_simp
            ring

/-- The pure uniformizer scaling is nonzero on the completion field. -/
theorem sourcePsiPureUniformizerChange_u_ne_zero (n : ℕ) :
    ((sourcePsiPureUniformizerChange S v n).u :
      SourcePsiCompletionFractionField S v) ≠ 0 :=
  Units.ne_zero _

/-- Exact absorption datum: every integral change admits a pure-uniformizer
absorption with integral residual, for every positive exponent. -/
theorem sourcePsiUniformizerAbsorptionData_exists
    (C : VariableChange (SourcePsiCompletionFractionField S v)) (n : ℕ) (hn : 0 < n)
    (hC : SourcePsiChangeIntegral S v M C) :
    Nonempty (SourcePsiUniformizerAbsorptionData S v M C) :=
  ⟨{
    n := n
    n_pos := hn
    residual := sourcePsiAbsorptionResidual S v C n
    decomposition := sourcePsiAbsorption_decomposition S v C n
    residual_integral :=
      sourcePsiAbsorptionResidual_integral S v M C n hC }⟩

/-- Specialization to the surviving nonminimality witness: the witness has an
exact absorption with integral residual. -/
theorem SourcePsiIntegralModel_nonminimal_witness_absorption
    (h : ¬ SourcePsiIntegralModelMinimalCorrected S v M) :
    ∃ C : VariableChange (SourcePsiCompletionFractionField S v),
      SourcePsiChangeIntegral S v M C ∧
        SourcePsiScalingIntegralNonunit S v C ∧
          Nonempty (SourcePsiUniformizerAbsorptionData S v M C) := by
  obtain ⟨C, hC, hscale⟩ := SourcePsiIntegralModel_nonminimal_witness S v M h
  exact ⟨C, hC, hscale,
    sourcePsiUniformizerAbsorptionData_exists S v M C 1 (by norm_num) hC⟩

/-- Exact residual predicate of the absorption converse: the residual change has
unit scaling, so it is an integral unit change and not a pure uniformizer
obstruction. -/
def SourcePsiAbsorptionResidualIsUnit
    (M : SourcePsiIntegralModelData S v)
    (C : VariableChange (SourcePsiCompletionFractionField S v)) : Prop :=
  IsCompletionIntegralUnit S v
    ((sourcePsiAbsorptionResidual S v C 1).u :
      SourcePsiCompletionFractionField S v)

/-- The converse residual class that remains after absorption: either the
residual is a unit-scaling integral change, or one must iterate the absorption.
No implication to corrected minimality is asserted from absence of pure
uniformizer changes alone. -/
def SourcePsiAbsorptionConverseResidual : Prop :=
  ∃ C : VariableChange (SourcePsiCompletionFractionField S v),
    SourcePsiChangeIntegral S v M C ∧
      SourcePsiScalingIntegralNonunit S v C ∧
        ¬ SourcePsiAbsorptionResidualIsUnit S v M C

/-! ## Exact status

Proved:
- the algebraic decomposition C = P_n * R for every change C and n;
- the pure scaling coefficient formulas;
- residual integrality: if C is integral, the residual R is integral;
- existence of the exact absorption datum for every integral C and n > 0;
- existence of an exact absorption for every nonminimality witness.

Not proved:
1. the converse from absence of pure uniformizer changes: absorption leaves a
   residual change whose scaling may be a unit or a further nonunit;
2. the unit-residual normalization C = P_n * R with R an integral unit change;
3. iteration/termination for a nonunit residual (requires the discrete valuation
   length argument);
4. full minimal-model existence/uniqueness and source special-fiber comparison.

These are exact residual statements.  No model or change is fabricated.
-/

end LeanFormal.IUT.SourcePsiUniformizerAbsorptionFinal

end