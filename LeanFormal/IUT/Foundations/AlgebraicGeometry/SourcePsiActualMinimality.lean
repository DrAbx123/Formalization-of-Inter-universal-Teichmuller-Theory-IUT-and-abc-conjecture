import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiActualMinimalModelReduction
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiIntegralModelReduction
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiIntegralModel
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.SourcePsiActualMinimality

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiIntegralModelReduction
open LeanFormal.IUT.SourcePsiActualMinimalModelReduction
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

abbrev correctedBaseCurve (M : SourcePsiIntegralModelData S v) :
    WeierstrassCurve (SourcePsiActualField S v) :=
  actualBaseChangeCurve S v M

abbrev correctedMinimalModel (M : SourcePsiIntegralModelData S v) :
    WeierstrassCurve (SourcePsiActualField S v) :=
  actualMinimalModel S v M

theorem correctedMinimalModel_isMinimal
    (M : SourcePsiIntegralModelData S v) :
    WeierstrassCurve.IsMinimal (SourcePsiActualIntegers S v)
      (correctedMinimalModel S v M) :=
  inferInstance

theorem correctedMinimalModel_isIntegral
    (M : SourcePsiIntegralModelData S v) :
    WeierstrassCurve.IsIntegral (SourcePsiActualIntegers S v)
      (correctedMinimalModel S v M) :=
  inferInstance

theorem correctedMinimalModel_baseChange
    (M : SourcePsiIntegralModelData S v) :
    (actualMinimalIntegralModel S v M).map
        (algebraMap (SourcePsiActualIntegers S v) (SourcePsiActualField S v)) =
      correctedMinimalModel S v M :=
  actualMinimalIntegralModel_baseChange S v M

abbrev correctedMinimalReduction (M : SourcePsiIntegralModelData S v) :
    WeierstrassCurve (SourcePsiActualResidueField S v) :=
  actualMinimalReduction S v M

theorem correctedMinimalReduction_eq_residueMap
    (M : SourcePsiIntegralModelData S v) :
    correctedMinimalReduction S v M =
      (actualMinimalIntegralModel S v M).map
        (IsLocalRing.residue (SourcePsiActualIntegers S v)) :=
  rfl

def correctedMinimalModelHasNonzeroDiscriminant
    (M : SourcePsiIntegralModelData S v) : Prop :=
  (correctedMinimalModel S v M).Δ ≠ 0

theorem correctedMinimalModel_discriminant_ne_zero_of_hyp
    (M : SourcePsiIntegralModelData S v)
    (hΔ : correctedMinimalModelHasNonzeroDiscriminant S v M) :
    (correctedMinimalModel S v M).Δ ≠ 0 :=
  hΔ

theorem correctedMinimalModel_valuation_le_of_integral_change
    (M : SourcePsiIntegralModelData S v)
    (C : WeierstrassCurve.VariableChange (SourcePsiActualField S v))
    (hC : WeierstrassCurve.IsIntegral (SourcePsiActualIntegers S v)
      (C • correctedMinimalModel S v M)) :
    WeierstrassCurve.valuation_Δ_aux (SourcePsiActualIntegers S v)
        (C • correctedMinimalModel S v M) ≤
      WeierstrassCurve.valuation_Δ_aux (SourcePsiActualIntegers S v)
        (correctedMinimalModel S v M) :=
  (correctedMinimalModel_isMinimal S v M).val_Δ_maximal.2 hC

theorem correctedMinimalModel_discriminant_variableChange
    (M : SourcePsiIntegralModelData S v)
    (C : WeierstrassCurve.VariableChange (SourcePsiActualField S v)) :
    (C • correctedMinimalModel S v M).Δ =
      (C.u : SourcePsiActualField S v)⁻¹ ^ 12 *
        (correctedMinimalModel S v M).Δ :=
  WeierstrassCurve.variableChange_Δ C (correctedMinimalModel S v M)

theorem correctedMinimalModel_integral_change_unit
    (M : SourcePsiIntegralModelData S v)
    (hΔ : correctedMinimalModelHasNonzeroDiscriminant S v M)
    (C : WeierstrassCurve.VariableChange (SourcePsiActualField S v))
    (hC : WeierstrassCurve.IsIntegral (SourcePsiActualIntegers S v)
      (C • correctedMinimalModel S v M))
    (hCmin : WeierstrassCurve.IsMinimal (SourcePsiActualIntegers S v)
      (C • correctedMinimalModel S v M)) :
    Valued.v (C.u : SourcePsiActualField S v) = 1 :=
  by
  let W := correctedMinimalModel S v M
  have hWint : WeierstrassCurve.IsIntegral (SourcePsiActualIntegers S v) W :=
    inferInstance
  have hle : WeierstrassCurve.valuation_Δ_aux (SourcePsiActualIntegers S v)
        (C • W) ≤ WeierstrassCurve.valuation_Δ_aux (SourcePsiActualIntegers S v) W :=
    (correctedMinimalModel_isMinimal S v M).val_Δ_maximal.2 hC
  have hge : WeierstrassCurve.valuation_Δ_aux (SourcePsiActualIntegers S v) W ≤
      WeierstrassCurve.valuation_Δ_aux (SourcePsiActualIntegers S v) (C • W) :=
    hCmin.val_Δ_maximal.2 (by simpa using hWint)
  have heq : WeierstrassCurve.valuation_Δ_aux (SourcePsiActualIntegers S v)
        (C • W) = WeierstrassCurve.valuation_Δ_aux (SourcePsiActualIntegers S v) W :=
    le_antisymm hle hge
  have hval : WeierstrassCurve.valuation_Δ_aux (SourcePsiActualIntegers S v) W =
      Valued.v W.Δ :=
    WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral W
  have hvalC : WeierstrassCurve.valuation_Δ_aux (SourcePsiActualIntegers S v) (C • W) =
      Valued.v (C • W).Δ :=
    WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral (C • W)
  have hΔeq : Valued.v (C • W).Δ = Valued.v W.Δ := by
    rw [← hvalC, ← hval]
    exact heq
  rw [WeierstrassCurve.variableChange_Δ, map_mul, map_pow, map_inv₀,
    Valued.v.map_units] at hΔeq
  have hWu : Valued.v W.Δ ≠ 0 := by
    simpa [map_zero] using ((Valued.v).ne_zero_iff).mpr (hΔ)
  have hpow : (Valued.v (C.u : SourcePsiActualField S v))⁻¹ ^ 12 = 1 := by
    have := hΔeq
    rw [hWu] at this
    exact mul_right_cancel₀ hWu this
  exact inv_pow_eq_one_iff.mp hpow

theorem correctedMinimalModel_integral_minimal_change_unit
    (M : SourcePsiIntegralModelData S v)
    (hΔ : correctedMinimalModelHasNonzeroDiscriminant S v M)
    (C : WeierstrassCurve.VariableChange (SourcePsiActualField S v))
    (hC : WeierstrassCurve.IsIntegral (SourcePsiActualIntegers S v)
      (C • correctedMinimalModel S v M))
    (hmin : WeierstrassCurve.IsMinimal (SourcePsiActualIntegers S v)
      (C • correctedMinimalModel S v M)) :
    Valued.v (C.u : SourcePsiActualField S v) = 1 :=
  correctedMinimalModel_integral_change_unit S v M hΔ C hC hmin

structure CorrectedMinimalModelData where
  model : SourcePsiIntegralModelData S v
  curve : WeierstrassCurve (SourcePsiActualField S v)
  curve_eq : curve = correctedMinimalModel S v model
  minimal : WeierstrassCurve.IsMinimal (SourcePsiActualIntegers S v) curve

noncomputable def correctedMinimalModelData
    (M : SourcePsiIntegralModelData S v) : CorrectedMinimalModelData S v where
  model := M
  curve := correctedMinimalModel S v M
  curve_eq := rfl
  minimal := correctedMinimalModel_isMinimal S v M

theorem correctedMinimalModelData_curve_eq
    (M : SourcePsiIntegralModelData S v) :
    (correctedMinimalModelData S v M).curve = correctedMinimalModel S v M :=
  rfl

theorem correctedMinimalModelData_isMinimal
    (M : SourcePsiIntegralModelData S v) :
    WeierstrassCurve.IsMinimal (SourcePsiActualIntegers S v)
      (correctedMinimalModelData S v M).curve :=
  (correctedMinimalModelData S v M).minimal

theorem correctedMinimalModel_uniqueness_unitChange
    (M : SourcePsiIntegralModelData S v)
    (hΔ : correctedMinimalModelHasNonzeroDiscriminant S v M)
    (C : WeierstrassCurve.VariableChange (SourcePsiActualField S v))
    (hC : WeierstrassCurve.IsIntegral (SourcePsiActualIntegers S v)
      (C • correctedMinimalModel S v M))
    (hmin : WeierstrassCurve.IsMinimal (SourcePsiActualIntegers S v)
      (C • correctedMinimalModel S v M)) :
    Valued.v (C.u : SourcePsiActualField S v) = 1 :=
  correctedMinimalModel_integral_minimal_change_unit S v M hΔ C hC hmin

theorem correctedMinimalReduction_eq_selectedIntegralModel
    (M : SourcePsiIntegralModelData S v) :
    correctedMinimalReduction S v M =
      (actualMinimalIntegralModel S v M).map
        (IsLocalRing.residue (SourcePsiActualIntegers S v)) :=
  rfl

theorem correctedMinimalReduction_original_reducedCurve
    (M : SourcePsiIntegralModelData S v) :
    M.curve.map (IsLocalRing.residue (SourcePsiActualIntegers S v)) =
      SourcePsiReducedCurve S v M :=
  by
  ext <;> rfl

theorem correctedMinimalModel_exists_variableChange
    (M : SourcePsiIntegralModelData S v) :
    ∃ C : WeierstrassCurve.VariableChange (SourcePsiActualField S v),
      correctedMinimalModel S v M = C • correctedBaseCurve S v M :=
  ⟨actualMinimalChange S v M, actualMinimalModel_eq_smul S v M⟩

/-- The reduction of the corrected minimal model has the expected five
residue coefficients. -/
theorem correctedMinimalReduction_coefficients
    (M : SourcePsiIntegralModelData S v) :
    (correctedMinimalReduction S v M).a₁ =
        IsLocalRing.residue (SourcePsiActualIntegers S v)
          (actualMinimalIntegralModel S v M).a₁ ∧
      (correctedMinimalReduction S v M).a₂ =
        IsLocalRing.residue (SourcePsiActualIntegers S v)
          (actualMinimalIntegralModel S v M).a₂ ∧
      (correctedMinimalReduction S v M).a₃ =
        IsLocalRing.residue (SourcePsiActualIntegers S v)
          (actualMinimalIntegralModel S v M).a₃ ∧
      (correctedMinimalReduction S v M).a₄ =
        IsLocalRing.residue (SourcePsiActualIntegers S v)
          (actualMinimalIntegralModel S v M).a₄ ∧
      (correctedMinimalReduction S v M).a₆ =
        IsLocalRing.residue (SourcePsiActualIntegers S v)
          (actualMinimalIntegralModel S v M).a₆ :=
  actualMinimalReduction_coefficients S v M

/-- Same-discriminant integral change form of the unit-change statement. -/
theorem correctedMinimalModel_unitChange_of_sameDiscriminant
    (M : SourcePsiIntegralModelData S v)
    (hΔ : correctedMinimalModelHasNonzeroDiscriminant S v M)
    (C : WeierstrassCurve.VariableChange (SourcePsiActualField S v))
    (hC : WeierstrassCurve.IsIntegral (SourcePsiActualIntegers S v)
      (C • correctedMinimalModel S v M))
    (hΔeq : Valued.v (C • correctedMinimalModel S v M).Δ =
      Valued.v (correctedMinimalModel S v M).Δ) :
    Valued.v (C.u : SourcePsiActualField S v) = 1 :=
  by
  let W := correctedMinimalModel S v M
  have hWu : Valued.v W.Δ ≠ 0 := by
    simpa [map_zero] using ((Valued.v).ne_zero_iff).mpr hΔ
  have hformula : Valued.v (C • W).Δ =
      (Valued.v (C.u : SourcePsiActualField S v))⁻¹ ^ 12 * Valued.v W.Δ := by
    rw [WeierstrassCurve.variableChange_Δ, map_mul, map_pow, map_inv₀,
      Valued.v.map_units]
  rw [hformula] at hΔeq
  have hpow : (Valued.v (C.u : SourcePsiActualField S v))⁻¹ ^ 12 = 1 := by
    exact mul_right_cancel₀ hWu hΔeq
  exact inv_pow_eq_one_iff.mp hpow

/-- Corrected minimal-model uniqueness data: the actual corrected model, its
nonzero discriminant condition, and the unit-change exclusion for every
integral minimal change. -/
structure CorrectedMinimalModelUniquenessData where
  model : SourcePsiIntegralModelData S v
  discr_ne_zero : correctedMinimalModelHasNonzeroDiscriminant S v model
  minimal : WeierstrassCurve.IsMinimal (SourcePsiActualIntegers S v)
    (correctedMinimalModel S v model)
  unit_change :
    ∀ (C : WeierstrassCurve.VariableChange (SourcePsiActualField S v)),
      WeierstrassCurve.IsIntegral (SourcePsiActualIntegers S v)
        (C • correctedMinimalModel S v model) →
      WeierstrassCurve.IsMinimal (SourcePsiActualIntegers S v)
        (C • correctedMinimalModel S v model) →
      Valued.v (C.u : SourcePsiActualField S v) = 1

noncomputable def correctedMinimalModelUniquenessData
    (M : SourcePsiIntegralModelData S v)
    (hΔ : correctedMinimalModelHasNonzeroDiscriminant S v M) :
    CorrectedMinimalModelUniquenessData S v where
  model := M
  discr_ne_zero := hΔ
  minimal := correctedMinimalModel_isMinimal S v M
  unit_change := fun C hC hmin =>
    correctedMinimalModel_integral_minimal_change_unit S v M hΔ C hC hmin

theorem correctedMinimalModelUniquenessData_minimal
    (M : SourcePsiIntegralModelData S v)
    (hΔ : correctedMinimalModelHasNonzeroDiscriminant S v M) :
    WeierstrassCurve.IsMinimal (SourcePsiActualIntegers S v)
      (correctedMinimalModel S v (correctedMinimalModelUniquenessData S v M hΔ).model) :=
  (correctedMinimalModelUniquenessData S v M hΔ).minimal

theorem correctedMinimalModelUniquenessData_unit_change
    (M : SourcePsiIntegralModelData S v)
    (hΔ : correctedMinimalModelHasNonzeroDiscriminant S v M)
    (C : WeierstrassCurve.VariableChange (SourcePsiActualField S v))
    (hC : WeierstrassCurve.IsIntegral (SourcePsiActualIntegers S v)
      (C • correctedMinimalModel S v M))
    (hmin : WeierstrassCurve.IsMinimal (SourcePsiActualIntegers S v)
      (C • correctedMinimalModel S v M)) :
    Valued.v (C.u : SourcePsiActualField S v) = 1 :=
  (correctedMinimalModelUniquenessData S v M hΔ).unit_change C hC hmin

/-- Corrected minimality package: the actual Mathlib minimal model is minimal,
its discriminant is nonzero under the explicit hypothesis, and every integral
minimal change has unit scaling. -/
theorem correctedMinimalModel_minimality_package
    (M : SourcePsiIntegralModelData S v)
    (hΔ : correctedMinimalModelHasNonzeroDiscriminant S v M) :
    WeierstrassCurve.IsMinimal (SourcePsiActualIntegers S v)
        (correctedMinimalModel S v M) ∧
      (correctedMinimalModel S v M).Δ ≠ 0 ∧
      (∀ (C : WeierstrassCurve.VariableChange (SourcePsiActualField S v)),
        WeierstrassCurve.IsIntegral (SourcePsiActualIntegers S v)
          (C • correctedMinimalModel S v M) →
        WeierstrassCurve.IsMinimal (SourcePsiActualIntegers S v)
          (C • correctedMinimalModel S v M) →
        Valued.v (C.u : SourcePsiActualField S v) = 1) :=
  ⟨correctedMinimalModel_isMinimal S v M,
    correctedMinimalModel_discriminant_ne_zero_of_hyp S v M hΔ,
    fun C hC hmin =>
      correctedMinimalModel_integral_minimal_change_unit S v M hΔ C hC hmin⟩
end LeanFormal.IUT.SourcePsiActualMinimality
