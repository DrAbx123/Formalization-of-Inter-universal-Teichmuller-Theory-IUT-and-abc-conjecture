import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiActualMinimality
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiMinimalModelUniqueness
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiActualMinimalModelReduction
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Tactic

/-!
# Final corrected minimal-model uniqueness

From the actual Mathlib minimal models of the base-changed source curve, prove
that any actual change between two such minimal models has unit scaling, and
derive the corrected uniqueness statement up to a unit-scaling Weierstrass
change.  The nonzero-discriminant hypothesis is explicit; no minimality or
uniqueness is fabricated.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.SourcePsiMinimalModelUniquenessFinal

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiIntegralModelReduction
open LeanFormal.IUT.SourcePsiActualMinimalModelReduction
open LeanFormal.IUT.SourcePsiActualMinimality
open LeanFormal.IUT.SourcePsiMinimalModelUniqueness
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

abbrev ActualCorrectedMinimalCurve (M : SourcePsiIntegralModelData S v) :
    WeierstrassCurve (SourcePsiActualField S v) :=
  correctedMinimalModel S v M

abbrev ActualCorrectedMinimalReduction (M : SourcePsiIntegralModelData S v) :
    WeierstrassCurve (SourcePsiActualResidueField S v) :=
  correctedMinimalReduction S v M

/-- A corrected minimal model together with the actual change realizing it. -/
structure ActualCorrectedMinimalModelData where
  model : SourcePsiIntegralModelData S v
  curve : WeierstrassCurve (SourcePsiActualField S v)
  change : WeierstrassCurve.VariableChange (SourcePsiActualField S v)
  curve_eq : curve = change • actualBaseChangeCurve S v model
  minimal : WeierstrassCurve.IsMinimal (SourcePsiActualIntegers S v) curve
  discr_ne_zero : curve.Δ ≠ 0

noncomputable def actualCorrectedMinimalModelData
    (M : SourcePsiIntegralModelData S v)
    (hΔ : correctedMinimalModelHasNonzeroDiscriminant S v M) :
    ActualCorrectedMinimalModelData S v where
  model := M
  curve := correctedMinimalModel S v M
  change := actualMinimalChange S v M
  curve_eq := actualMinimalModel_eq_smul S v M
  minimal := correctedMinimalModel_isMinimal S v M
  discr_ne_zero := correctedMinimalModel_discriminant_ne_zero_of_hyp S v M hΔ

theorem actualCorrectedMinimalModelData_isMinimal
    (M : SourcePsiIntegralModelData S v)
    (hΔ : correctedMinimalModelHasNonzeroDiscriminant S v M) :
    WeierstrassCurve.IsMinimal (SourcePsiActualIntegers S v)
      (actualCorrectedMinimalModelData S v M hΔ).curve :=
  (actualCorrectedMinimalModelData S v M hΔ).minimal

/-- Two actual corrected minimal models related by an actual Weierstrass change. -/
structure ActualMinimalModelChangeData where
  source : SourcePsiIntegralModelData S v
  target : SourcePsiIntegralModelData S v
  change : WeierstrassCurve.VariableChange (SourcePsiActualField S v)
  change_eq : change • correctedMinimalModel S v source =
    correctedMinimalModel S v target
  source_minimal : WeierstrassCurve.IsMinimal (SourcePsiActualIntegers S v)
    (correctedMinimalModel S v source)
  target_minimal : WeierstrassCurve.IsMinimal (SourcePsiActualIntegers S v)
    (correctedMinimalModel S v target)
  source_discr_ne_zero : (correctedMinimalModel S v source).Δ ≠ 0
  target_discr_ne_zero : (correctedMinimalModel S v target).Δ ≠ 0

noncomputable def actualMinimalModelChangeData
    (M N : SourcePsiIntegralModelData S v)
    (C : WeierstrassCurve.VariableChange (SourcePsiActualField S v))
    (hC : C • correctedMinimalModel S v M = correctedMinimalModel S v N)
    (hΔM : correctedMinimalModelHasNonzeroDiscriminant S v M)
    (hΔN : correctedMinimalModelHasNonzeroDiscriminant S v N) :
    ActualMinimalModelChangeData S v where
  source := M
  target := N
  change := C
  change_eq := hC
  source_minimal := correctedMinimalModel_isMinimal S v M
  target_minimal := correctedMinimalModel_isMinimal S v N
  source_discr_ne_zero := correctedMinimalModel_discriminant_ne_zero_of_hyp S v M hΔM
  target_discr_ne_zero := correctedMinimalModel_discriminant_ne_zero_of_hyp S v N hΔN

/-- The actual discriminant comparison between two minimal models: the change
does not increase the discriminant valuation in either direction. -/
theorem actualMinimalModelChange_valuation_le
    (D : ActualMinimalModelChangeData S v) :
    WeierstrassCurve.valuation_Δ_aux (SourcePsiActualIntegers S v)
        (D.change • correctedMinimalModel S v D.source) ≤
      WeierstrassCurve.valuation_Δ_aux (SourcePsiActualIntegers S v)
        (correctedMinimalModel S v D.source) :=
  D.source_minimal.val_Δ_maximal.2 (by
    rw [D.change_eq]
    exact inferInstance)

theorem actualMinimalModelChange_valuation_ge
    (D : ActualMinimalModelChangeData S v) :
    WeierstrassCurve.valuation_Δ_aux (SourcePsiActualIntegers S v)
        (correctedMinimalModel S v D.source) ≤
      WeierstrassCurve.valuation_Δ_aux (SourcePsiActualIntegers S v)
        (D.change • correctedMinimalModel S v D.source) :=
  by
  have hchange_inv : D.change⁻¹ • correctedMinimalModel S v D.target =
      correctedMinimalModel S v D.source := by
    rw [← D.change_eq]
    simp
  have hCint : WeierstrassCurve.IsIntegral (SourcePsiActualIntegers S v)
      (D.change⁻¹ • correctedMinimalModel S v D.target) :=
    by
    rw [hchange_inv]
    exact inferInstance
  have hle := D.target_minimal.val_Δ_maximal.2 hCint
  simpa [hchange_inv] using hle

theorem actualMinimalModelChange_valuation_eq
    (D : ActualMinimalModelChangeData S v) :
    WeierstrassCurve.valuation_Δ_aux (SourcePsiActualIntegers S v)
        (D.change • correctedMinimalModel S v D.source) =
      WeierstrassCurve.valuation_Δ_aux (SourcePsiActualIntegers S v)
        (correctedMinimalModel S v D.source) :=
  le_antisymm (actualMinimalModelChange_valuation_le S v D)
    (actualMinimalModelChange_valuation_ge S v D)

/-- The actual discriminant equality between two minimal models. -/
theorem actualMinimalModelChange_discriminant_eq
    (D : ActualMinimalModelChangeData S v) :
    (D.change • correctedMinimalModel S v D.source).Δ =
      (correctedMinimalModel S v D.source).Δ :=
  by
  have hval := actualMinimalModelChange_valuation_eq S v D
  have hvalC := WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral
    (R := SourcePsiActualIntegers S v)
    (D.change • correctedMinimalModel S v D.source)
  have hvalM := WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral
    (R := SourcePsiActualIntegers S v)
    (correctedMinimalModel S v D.source)
  rw [hvalC, hvalM] at hval
  exact hval

/-- Unit-scaling theorem for a change between two actual minimal models. -/
theorem actualMinimalModelChange_unit_scaling
    (D : ActualMinimalModelChangeData S v) :
    Valued.v (D.change.u : SourcePsiActualField S v) = 1 :=
  by
  let W := correctedMinimalModel S v D.source
  have hWu : Valued.v W.Δ ≠ 0 := by
    simpa [map_zero] using ((Valued.v).ne_zero_iff).mpr D.source_discr_ne_zero
  have hΔeq : Valued.v (D.change • W).Δ = Valued.v W.Δ :=
  by
    have h := actualMinimalModelChange_discriminant_eq S v D
    rw [h]
  have hformula : Valued.v (D.change • W).Δ =
      (Valued.v (D.change.u : SourcePsiActualField S v))⁻¹ ^ 12 *
        Valued.v W.Δ := by
    rw [WeierstrassCurve.variableChange_Δ, map_mul, map_pow, map_inv₀,
      Valued.v.map_units]
  rw [hformula] at hΔeq
  have hpow : (Valued.v (D.change.u : SourcePsiActualField S v))⁻¹ ^ 12 = 1 := by
    exact mul_right_cancel₀ hWu hΔeq
  exact inv_pow_eq_one_iff.mp hpow

/-- The corrected minimal-model uniqueness statement for an actual change. -/
def ActualMinimalModelUniquenessStatement
    (M N : SourcePsiIntegralModelData S v) : Prop :=
  ∃ C : WeierstrassCurve.VariableChange (SourcePsiActualField S v),
    C • correctedMinimalModel S v M = correctedMinimalModel S v N ∧
      Valued.v (C.u : SourcePsiActualField S v) = 1

theorem actualMinimalModel_uniqueness_of_change
    (M N : SourcePsiIntegralModelData S v)
    (hΔM : correctedMinimalModelHasNonzeroDiscriminant S v M)
    (hΔN : correctedMinimalModelHasNonzeroDiscriminant S v N)
    (C : WeierstrassCurve.VariableChange (SourcePsiActualField S v))
    (hC : C • correctedMinimalModel S v M = correctedMinimalModel S v N) :
    ActualMinimalModelUniquenessStatement S v M N :=
  ⟨C, hC,
    actualMinimalModelChange_unit_scaling S v
      (actualMinimalModelChangeData S v M N C hC hΔM hΔN)⟩

theorem actualMinimalModel_uniqueness_iff_exists_change
    (M N : SourcePsiIntegralModelData S v)
    (hΔM : correctedMinimalModelHasNonzeroDiscriminant S v M)
    (hΔN : correctedMinimalModelHasNonzeroDiscriminant S v N) :
    ActualMinimalModelUniquenessStatement S v M N ↔
      ∃ C : WeierstrassCurve.VariableChange (SourcePsiActualField S v),
        C • correctedMinimalModel S v M = correctedMinimalModel S v N :=
  by
  constructor
  · rintro ⟨C, hC, _⟩
    exact ⟨C, hC⟩
  · rintro ⟨C, hC⟩
    exact actualMinimalModel_uniqueness_of_change S v M N hΔM hΔN C hC

/-- The corrected uniqueness statement makes the reduction independent of the
chosen actual minimal model in the unit-change sense: the change has unit scaling
and both reductions are explicit residue reductions of the selected integral
models. -/
theorem actualMinimalModel_uniqueness_reduction_compat
    (M N : SourcePsiIntegralModelData S v)
    (hΔM : correctedMinimalModelHasNonzeroDiscriminant S v M)
    (hΔN : correctedMinimalModelHasNonzeroDiscriminant S v N)
    (C : WeierstrassCurve.VariableChange (SourcePsiActualField S v))
    (hC : C • correctedMinimalModel S v M = correctedMinimalModel S v N) :
    Valued.v (C.u : SourcePsiActualField S v) = 1 ∧
      correctedMinimalReduction S v M =
        (actualMinimalIntegralModel S v M).map
          (IsLocalRing.residue (SourcePsiActualIntegers S v)) ∧
      correctedMinimalReduction S v N =
        (actualMinimalIntegralModel S v N).map
          (IsLocalRing.residue (SourcePsiActualIntegers S v)) :=
  ⟨actualMinimalModelChange_unit_scaling S v
      (actualMinimalModelChangeData S v M N C hC hΔM hΔN),
    rfl, rfl⟩

/-- Package: the actual corrected minimal models are unique up to a
unit-scaling change. -/
theorem actualMinimalModel_uniqueness_package
    (M N : SourcePsiIntegralModelData S v)
    (hΔM : correctedMinimalModelHasNonzeroDiscriminant S v M)
    (hΔN : correctedMinimalModelHasNonzeroDiscriminant S v N)
    (C : WeierstrassCurve.VariableChange (SourcePsiActualField S v))
    (hC : C • correctedMinimalModel S v M = correctedMinimalModel S v N) :
    ActualMinimalModelUniquenessStatement S v M N ∧
      Valued.v (C.u : SourcePsiActualField S v) = 1 :=
  ⟨actualMinimalModel_uniqueness_of_change S v M N hΔM hΔN C hC,
    actualMinimalModelChange_unit_scaling S v
      (actualMinimalModelChangeData S v M N C hC hΔM hΔN)⟩

/-- Witness data for the corrected minimal-model uniqueness statement. -/
structure ActualMinimalModelUniquenessWitness where
  source : SourcePsiIntegralModelData S v
  target : SourcePsiIntegralModelData S v
  change : WeierstrassCurve.VariableChange (SourcePsiActualField S v)
  change_eq : change • correctedMinimalModel S v source =
    correctedMinimalModel S v target
  unit_scaling : Valued.v (change.u : SourcePsiActualField S v) = 1

noncomputable def actualMinimalModelUniquenessWitness
    (M N : SourcePsiIntegralModelData S v)
    (hΔM : correctedMinimalModelHasNonzeroDiscriminant S v M)
    (hΔN : correctedMinimalModelHasNonzeroDiscriminant S v N)
    (C : WeierstrassCurve.VariableChange (SourcePsiActualField S v))
    (hC : C • correctedMinimalModel S v M = correctedMinimalModel S v N) :
    ActualMinimalModelUniquenessWitness S v where
  source := M
  target := N
  change := C
  change_eq := hC
  unit_scaling := actualMinimalModelChange_unit_scaling S v
    (actualMinimalModelChangeData S v M N C hC hΔM hΔN)

theorem actualMinimalModelUniquenessWitness_change_eq
    (M N : SourcePsiIntegralModelData S v)
    (hΔM : correctedMinimalModelHasNonzeroDiscriminant S v M)
    (hΔN : correctedMinimalModelHasNonzeroDiscriminant S v N)
    (C : WeierstrassCurve.VariableChange (SourcePsiActualField S v))
    (hC : C • correctedMinimalModel S v M = correctedMinimalModel S v N) :
    (actualMinimalModelUniquenessWitness S v M N hΔM hΔN C hC).change •
        correctedMinimalModel S v M =
      correctedMinimalModel S v N :=
  (actualMinimalModelUniquenessWitness S v M N hΔM hΔN C hC).change_eq

theorem actualMinimalModelUniquenessWitness_unit_scaling
    (M N : SourcePsiIntegralModelData S v)
    (hΔM : correctedMinimalModelHasNonzeroDiscriminant S v M)
    (hΔN : correctedMinimalModelHasNonzeroDiscriminant S v N)
    (C : WeierstrassCurve.VariableChange (SourcePsiActualField S v))
    (hC : C • correctedMinimalModel S v M = correctedMinimalModel S v N) :
    Valued.v ((actualMinimalModelUniquenessWitness S v M N hΔM hΔN C hC).change.u :
        SourcePsiActualField S v) = 1 :=
  (actualMinimalModelUniquenessWitness S v M N hΔM hΔN C hC).unit_scaling

theorem actualMinimalModel_uniqueness_witness_statement
    (M N : SourcePsiIntegralModelData S v)
    (hΔM : correctedMinimalModelHasNonzeroDiscriminant S v M)
    (hΔN : correctedMinimalModelHasNonzeroDiscriminant S v N)
    (C : WeierstrassCurve.VariableChange (SourcePsiActualField S v))
    (hC : C • correctedMinimalModel S v M = correctedMinimalModel S v N) :
    Nonempty (ActualMinimalModelUniquenessWitness S v) :=
  ⟨actualMinimalModelUniquenessWitness S v M N hΔM hΔN C hC⟩

theorem actualMinimalModel_uniqueness_witness_package
    (M N : SourcePsiIntegralModelData S v)
    (hΔM : correctedMinimalModelHasNonzeroDiscriminant S v M)
    (hΔN : correctedMinimalModelHasNonzeroDiscriminant S v N)
    (C : WeierstrassCurve.VariableChange (SourcePsiActualField S v))
    (hC : C • correctedMinimalModel S v M = correctedMinimalModel S v N) :
    (∃ W : ActualMinimalModelUniquenessWitness S v,
        W.source = M ∧ W.target = N ∧
          W.change • correctedMinimalModel S v M =
            correctedMinimalModel S v N ∧
          Valued.v (W.change.u : SourcePsiActualField S v) = 1) ∧
      ActualMinimalModelUniquenessStatement S v M N :=
  by
  let W := actualMinimalModelUniquenessWitness S v M N hΔM hΔN C hC
  refine ⟨⟨W, rfl, rfl, W.change_eq, W.unit_scaling⟩, ?_⟩
  exact actualMinimalModel_uniqueness_of_change S v M N hΔM hΔN C hC
end LeanFormal.IUT.SourcePsiMinimalModelUniquenessFinal
