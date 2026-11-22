import LeanFormal.IUT.ABCBridge.Geometry.LegendreParameterIsomorphisms
import LeanFormal.IUT.ABCBridge.Geometry.LegendreQuadraticParameterFields

/-!
# A fixed bounded-degree field realizing a Legendre invariant fiber

The extension in this file is the actual intermediate field
`LegendreQuadraticParameterFields.legendreParameterField K parameter` inside
`AlgebraicClosure K`. Its constructed roots of `-1`, `parameter`, and
`1 - parameter` supply the units needed for the native Weierstrass changes.

The field depends only on the source parameter. All admissible target
parameters with the same invariant use this one field. Its relative degree is
at most eight, or at most four when the base field already contains a square
root of `-1`. No assertion about descent of these changes to the base field is
made, and no Galois-extension hypothesis is needed.
-/

namespace LeanFormal.IUT

open LegendreQuadraticParameterFields

section ConcreteParameterField

variable (K : Type*) [Field K] [CharZero K]

/-- The three roots are supplied by the constructed intermediate field, rather
than assumed as additional inputs to the comparison theorem. -/
theorem exists_legendreVariableChange_over_parameterField
    (parameter transformedParameter : K)
    (parameter_admissible : IsLegendreParameter parameter)
    (transformed_admissible : IsLegendreParameter transformedParameter)
    (same_invariant : legendreJParameter transformedParameter = legendreJParameter parameter) :
    ∃ change : WeierstrassCurve.VariableChange (legendreParameterField K parameter),
      change • (legendreWeierstrassCurve parameter).baseChange
          (legendreParameterField K parameter) =
        (legendreWeierstrassCurve transformedParameter).baseChange
          (legendreParameterField K parameter) := by
  apply exists_legendreVariableChange_after_baseChange
    parameter_admissible transformed_admissible
    (legendreNegOneUnit K parameter)
    (legendreParameterUnit K parameter parameter_admissible.1)
    (legendreComplementUnit K parameter parameter_admissible.2)
  · change (legendreSqrtNegOne K parameter) ^ 2 = -1
    exact legendreSqrtNegOne_sq K parameter
  · change (legendreSqrtParameter K parameter) ^ 2 =
      algebraMap K (legendreParameterField K parameter) parameter
    exact legendreSqrtParameter_sq K parameter
  · change (legendreSqrtComplement K parameter) ^ 2 =
      1 - algebraMap K (legendreParameterField K parameter) parameter
    exact legendreSqrtComplement_sq K parameter
  · exact same_invariant

/-- A selected native change in the fixed concrete extension for each target
in the invariant fiber. The existence proof uses the exact six-factor fiber
classification and the concrete changes constructed from its three roots. -/
noncomputable def legendreParameterFieldVariableChange
    (parameter transformedParameter : K)
    (parameter_admissible : IsLegendreParameter parameter)
    (transformed_admissible : IsLegendreParameter transformedParameter)
    (same_invariant : legendreJParameter transformedParameter = legendreJParameter parameter) :
    WeierstrassCurve.VariableChange (legendreParameterField K parameter) :=
  Classical.choose (exists_legendreVariableChange_over_parameterField K
    parameter transformedParameter parameter_admissible transformed_admissible same_invariant)

theorem legendreParameterFieldVariableChange_smul
    (parameter transformedParameter : K)
    (parameter_admissible : IsLegendreParameter parameter)
    (transformed_admissible : IsLegendreParameter transformedParameter)
    (same_invariant : legendreJParameter transformedParameter = legendreJParameter parameter) :
    legendreParameterFieldVariableChange K parameter transformedParameter
        parameter_admissible transformed_admissible same_invariant •
        (legendreWeierstrassCurve parameter).baseChange
          (legendreParameterField K parameter) =
      (legendreWeierstrassCurve transformedParameter).baseChange
        (legendreParameterField K parameter) :=
  Classical.choose_spec (exists_legendreVariableChange_over_parameterField K
    parameter transformedParameter parameter_admissible transformed_admissible same_invariant)

theorem legendreParameterFieldVariableChange_inverse_smul
    (parameter transformedParameter : K)
    (parameter_admissible : IsLegendreParameter parameter)
    (transformed_admissible : IsLegendreParameter transformedParameter)
    (same_invariant : legendreJParameter transformedParameter = legendreJParameter parameter) :
    (legendreParameterFieldVariableChange K parameter transformedParameter
        parameter_admissible transformed_admissible same_invariant)⁻¹ •
        (legendreWeierstrassCurve transformedParameter).baseChange
          (legendreParameterField K parameter) =
      (legendreWeierstrassCurve parameter).baseChange
        (legendreParameterField K parameter) := by
  rw [← legendreParameterFieldVariableChange_smul K parameter transformedParameter
    parameter_admissible transformed_admissible same_invariant, inv_smul_smul]

/-- The selected actual change remains valid after any further scalar map out
of the concrete common field. This uses the native map of variable changes. -/
theorem legendreParameterFieldVariableChange_map
    {S : Type*} [CommRing S]
    (parameter transformedParameter : K)
    (parameter_admissible : IsLegendreParameter parameter)
    (transformed_admissible : IsLegendreParameter transformedParameter)
    (same_invariant : legendreJParameter transformedParameter = legendreJParameter parameter)
    (scalarMap : legendreParameterField K parameter →+* S) :
    (legendreParameterFieldVariableChange K parameter transformedParameter
        parameter_admissible transformed_admissible same_invariant).map scalarMap •
        ((legendreWeierstrassCurve parameter).baseChange
          (legendreParameterField K parameter)).map scalarMap =
      ((legendreWeierstrassCurve transformedParameter).baseChange
        (legendreParameterField K parameter)).map scalarMap := by
  rw [WeierstrassCurve.map_variableChange,
    legendreParameterFieldVariableChange_smul K parameter transformedParameter
      parameter_admissible transformed_admissible same_invariant]

/-- Uniformity over the whole ground-field fiber: the extension stays fixed
while the target parameter and the selected reversible change vary. -/
theorem legendreParameterField_uniform_curve_changes
    (parameter : K) (parameter_admissible : IsLegendreParameter parameter) :
    ∀ transformedParameter : K, IsLegendreParameter transformedParameter →
      legendreJParameter transformedParameter = legendreJParameter parameter →
      ∃ change : WeierstrassCurve.VariableChange (legendreParameterField K parameter),
        change • (legendreWeierstrassCurve parameter).baseChange
            (legendreParameterField K parameter) =
          (legendreWeierstrassCurve transformedParameter).baseChange
            (legendreParameterField K parameter) ∧
        change⁻¹ • (legendreWeierstrassCurve transformedParameter).baseChange
            (legendreParameterField K parameter) =
          (legendreWeierstrassCurve parameter).baseChange
            (legendreParameterField K parameter) := by
  intro transformedParameter transformed_admissible same_invariant
  exact ⟨legendreParameterFieldVariableChange K parameter transformedParameter
      parameter_admissible transformed_admissible same_invariant,
    legendreParameterFieldVariableChange_smul K parameter transformedParameter
      parameter_admissible transformed_admissible same_invariant,
    legendreParameterFieldVariableChange_inverse_smul K parameter transformedParameter
      parameter_admissible transformed_admissible same_invariant⟩

/-- A single actual extension of relative degree at most eight realizes every
admissible ground-field target in the invariant fiber. -/
theorem legendreParameterField_degree_eight_realizes_fiber
    (parameter : K) (parameter_admissible : IsLegendreParameter parameter) :
    Module.finrank K (legendreParameterField K parameter) ≤ 8 ∧
      ∀ transformedParameter : K, IsLegendreParameter transformedParameter →
        legendreJParameter transformedParameter = legendreJParameter parameter →
        ∃ change : WeierstrassCurve.VariableChange (legendreParameterField K parameter),
          change • (legendreWeierstrassCurve parameter).baseChange
              (legendreParameterField K parameter) =
            (legendreWeierstrassCurve transformedParameter).baseChange
              (legendreParameterField K parameter) := by
  constructor
  · exact legendreParameterField_finrank_le_eight K parameter
  · intro transformedParameter transformed_admissible same_invariant
    exact exists_legendreVariableChange_over_parameterField K parameter transformedParameter
      parameter_admissible transformed_admissible same_invariant

/-- When the base field already contains a square root of `-1`, the same
concrete field realizes the whole fiber with relative degree at most four. -/
theorem legendreParameterField_degree_four_realizes_fiber
    (parameter : K) (parameter_admissible : IsLegendreParameter parameter)
    (base_has_sqrt_neg_one : ∃ imaginaryRoot : K, imaginaryRoot ^ 2 = -1) :
    Module.finrank K (legendreParameterField K parameter) ≤ 4 ∧
      ∀ transformedParameter : K, IsLegendreParameter transformedParameter →
        legendreJParameter transformedParameter = legendreJParameter parameter →
        ∃ change : WeierstrassCurve.VariableChange (legendreParameterField K parameter),
          change • (legendreWeierstrassCurve parameter).baseChange
              (legendreParameterField K parameter) =
            (legendreWeierstrassCurve transformedParameter).baseChange
              (legendreParameterField K parameter) := by
  constructor
  · exact legendreParameterField_finrank_le_four K parameter base_has_sqrt_neg_one
  · intro transformedParameter transformed_admissible same_invariant
    exact exists_legendreVariableChange_over_parameterField K parameter transformedParameter
      parameter_admissible transformed_admissible same_invariant

end ConcreteParameterField

section CompleteFiberInParameterField

variable (K : Type*) [Field K] [CharZero K]

/-- The conclusion also covers any admissible target already in the common
field, without assuming it was initially presented as a base-field image. -/
theorem exists_legendreVariableChange_to_parameterField_fiber
    (parameter : K) (parameter_admissible : IsLegendreParameter parameter)
    (transformedParameter : legendreParameterField K parameter)
    (transformed_admissible : IsLegendreParameter transformedParameter)
    (same_invariant : legendreJParameter transformedParameter =
      legendreJParameter (algebraMap K (legendreParameterField K parameter) parameter)) :
    ∃ change : WeierstrassCurve.VariableChange (legendreParameterField K parameter),
      change • (legendreWeierstrassCurve parameter).baseChange
          (legendreParameterField K parameter) =
        legendreWeierstrassCurve transformedParameter := by
  have mapped_admissible := isLegendreParameter_map
    (algebraMap K (legendreParameterField K parameter)) parameter_admissible
  have imaginaryUnit_square : (↑(legendreNegOneUnit K parameter) :
      legendreParameterField K parameter) ^ 2 = -1 := by
    change (legendreSqrtNegOne K parameter) ^ 2 = -1
    exact legendreSqrtNegOne_sq K parameter
  have parameterUnit_square : (↑(legendreParameterUnit K parameter parameter_admissible.1) :
      legendreParameterField K parameter) ^ 2 =
      algebraMap K (legendreParameterField K parameter) parameter := by
    change (legendreSqrtParameter K parameter) ^ 2 =
      algebraMap K (legendreParameterField K parameter) parameter
    exact legendreSqrtParameter_sq K parameter
  have complementUnit_square : (↑(legendreComplementUnit K parameter parameter_admissible.2) :
      legendreParameterField K parameter) ^ 2 =
      1 - algebraMap K (legendreParameterField K parameter) parameter := by
    change (legendreSqrtComplement K parameter) ^ 2 =
      1 - algebraMap K (legendreParameterField K parameter) parameter
    exact legendreSqrtComplement_sq K parameter
  obtain ⟨change, change_equation⟩ := exists_legendreVariableChange_of_same_invariant
    mapped_admissible transformed_admissible
    (legendreNegOneUnit K parameter)
    (legendreParameterUnit K parameter parameter_admissible.1)
    (legendreComplementUnit K parameter parameter_admissible.2)
    imaginaryUnit_square parameterUnit_square complementUnit_square same_invariant
  refine ⟨change, ?_⟩
  simpa only [legendreWeierstrassCurve_baseChange] using change_equation

/-- The actual degree-eight field handles its entire admissible invariant
fiber, not only a separately chosen finite list of targets. -/
theorem legendreParameterField_degree_eight_realizes_entire_fiber
    (parameter : K) (parameter_admissible : IsLegendreParameter parameter) :
    Module.finrank K (legendreParameterField K parameter) ≤ 8 ∧
      ∀ transformedParameter : legendreParameterField K parameter,
        IsLegendreParameter transformedParameter →
        legendreJParameter transformedParameter =
          legendreJParameter (algebraMap K (legendreParameterField K parameter) parameter) →
        ∃ change : WeierstrassCurve.VariableChange (legendreParameterField K parameter),
          change • (legendreWeierstrassCurve parameter).baseChange
              (legendreParameterField K parameter) =
            legendreWeierstrassCurve transformedParameter :=
  ⟨legendreParameterField_finrank_le_eight K parameter,
    exists_legendreVariableChange_to_parameterField_fiber K parameter parameter_admissible⟩

/-- The corresponding full-fiber result under the improved degree-four bound. -/
theorem legendreParameterField_degree_four_realizes_entire_fiber
    (parameter : K) (parameter_admissible : IsLegendreParameter parameter)
    (base_has_sqrt_neg_one : ∃ imaginaryRoot : K, imaginaryRoot ^ 2 = -1) :
    Module.finrank K (legendreParameterField K parameter) ≤ 4 ∧
      ∀ transformedParameter : legendreParameterField K parameter,
        IsLegendreParameter transformedParameter →
        legendreJParameter transformedParameter =
          legendreJParameter (algebraMap K (legendreParameterField K parameter) parameter) →
        ∃ change : WeierstrassCurve.VariableChange (legendreParameterField K parameter),
          change • (legendreWeierstrassCurve parameter).baseChange
              (legendreParameterField K parameter) =
            legendreWeierstrassCurve transformedParameter :=
  ⟨legendreParameterField_finrank_le_four K parameter base_has_sqrt_neg_one,
    exists_legendreVariableChange_to_parameterField_fiber K parameter parameter_admissible⟩

end CompleteFiberInParameterField

section AlgebraicClosureFiber

variable (K : Type*) [Field K] [CharZero K]

/-- Once an admissible parameter is defined over the base field, its whole
Legendre-invariant fiber in any characteristic-zero field extension consists
of the images of its six base-field transforms. -/
theorem legendreInvariantFiber_descends_along_fieldMap
    {L : Type*} [Field L] [CharZero L] (fieldMap : K →+* L)
    (parameter : K) (parameter_admissible : IsLegendreParameter parameter)
    (transformedParameter : L) (transformed_admissible : IsLegendreParameter transformedParameter)
    (same_invariant : legendreJParameter transformedParameter =
      legendreJParameter (fieldMap parameter)) :
    ∃ groundParameter : K, IsLegendreParameter groundParameter ∧
      legendreJParameter groundParameter = legendreJParameter parameter ∧
      fieldMap groundParameter = transformedParameter := by
  have mapped_admissible := isLegendreParameter_map fieldMap parameter_admissible
  rcases (legendreJParameter_eq_iff_six_transforms mapped_admissible transformed_admissible).mp
    same_invariant with same | complement | reciprocal | reciprocal_complement |
      quotient | shifted_quotient
  · exact ⟨parameter, parameter_admissible, rfl, same.symm⟩
  · refine ⟨1 - parameter, isLegendreParameter_one_sub parameter_admissible,
      legendreJParameter_one_sub parameter_admissible, ?_⟩
    simpa using complement.symm
  · refine ⟨1 / parameter, isLegendreParameter_one_div parameter_admissible,
      legendreJParameter_one_div parameter_admissible, ?_⟩
    simpa using reciprocal.symm
  · refine ⟨1 / (1 - parameter), isLegendreParameter_one_div_one_sub parameter_admissible,
      legendreJParameter_one_div_one_sub parameter_admissible, ?_⟩
    simpa using reciprocal_complement.symm
  · refine ⟨parameter / (parameter - 1), isLegendreParameter_div_sub_one parameter_admissible,
      legendreJParameter_div_sub_one parameter_admissible, ?_⟩
    simpa using quotient.symm
  · refine ⟨(parameter - 1) / parameter, isLegendreParameter_sub_one_div parameter_admissible,
      legendreJParameter_sub_one_div parameter_admissible, ?_⟩
    simpa using shifted_quotient.symm

/-- Every admissible same-invariant parameter in the algebraic closure has
a representative in the one constructed common field, where an actual native
curve change is defined. The representative is not an extra chosen extension. -/
theorem legendreParameterField_realizes_algebraicClosure_fiber
    (parameter : K) (parameter_admissible : IsLegendreParameter parameter) :
    ∀ transformedParameter : AlgebraicClosure K,
      IsLegendreParameter transformedParameter →
      legendreJParameter transformedParameter =
        legendreJParameter (algebraMap K (AlgebraicClosure K) parameter) →
      ∃ fieldParameter : legendreParameterField K parameter,
        algebraMap (legendreParameterField K parameter) (AlgebraicClosure K) fieldParameter =
          transformedParameter ∧
        ∃ change : WeierstrassCurve.VariableChange (legendreParameterField K parameter),
          change • (legendreWeierstrassCurve parameter).baseChange
              (legendreParameterField K parameter) =
            legendreWeierstrassCurve fieldParameter := by
  intro transformedParameter transformed_admissible same_invariant
  obtain ⟨groundParameter, ground_admissible, ground_invariant, ground_image⟩ :=
    legendreInvariantFiber_descends_along_fieldMap K
      (algebraMap K (AlgebraicClosure K)) parameter parameter_admissible
      transformedParameter transformed_admissible same_invariant
  refine ⟨algebraMap K (legendreParameterField K parameter) groundParameter, ?_, ?_⟩
  · change algebraMap K (AlgebraicClosure K) groundParameter = transformedParameter
    exact ground_image
  · obtain ⟨change, change_equation⟩ := exists_legendreVariableChange_over_parameterField
      K parameter groundParameter parameter_admissible ground_admissible ground_invariant
    refine ⟨change, ?_⟩
    simpa only [legendreWeierstrassCurve_baseChange] using change_equation

/-- One relative-degree-at-most-eight field realizes the entire admissible
algebraic-closure fiber, with no field depending on the target parameter. -/
theorem legendreParameterField_degree_eight_realizes_algebraicClosure_fiber
    (parameter : K) (parameter_admissible : IsLegendreParameter parameter) :
    Module.finrank K (legendreParameterField K parameter) ≤ 8 ∧
      ∀ transformedParameter : AlgebraicClosure K,
        IsLegendreParameter transformedParameter →
        legendreJParameter transformedParameter =
          legendreJParameter (algebraMap K (AlgebraicClosure K) parameter) →
        ∃ fieldParameter : legendreParameterField K parameter,
          algebraMap (legendreParameterField K parameter) (AlgebraicClosure K) fieldParameter =
            transformedParameter ∧
          ∃ change : WeierstrassCurve.VariableChange (legendreParameterField K parameter),
            change • (legendreWeierstrassCurve parameter).baseChange
                (legendreParameterField K parameter) =
              legendreWeierstrassCurve fieldParameter :=
  ⟨legendreParameterField_finrank_le_eight K parameter,
    legendreParameterField_realizes_algebraicClosure_fiber K parameter parameter_admissible⟩

/-- The same entire algebraic-closure fiber is realized with relative degree
at most four if the base field already contains a square root of `-1`. -/
theorem legendreParameterField_degree_four_realizes_algebraicClosure_fiber
    (parameter : K) (parameter_admissible : IsLegendreParameter parameter)
    (base_has_sqrt_neg_one : ∃ imaginaryRoot : K, imaginaryRoot ^ 2 = -1) :
    Module.finrank K (legendreParameterField K parameter) ≤ 4 ∧
      ∀ transformedParameter : AlgebraicClosure K,
        IsLegendreParameter transformedParameter →
        legendreJParameter transformedParameter =
          legendreJParameter (algebraMap K (AlgebraicClosure K) parameter) →
        ∃ fieldParameter : legendreParameterField K parameter,
          algebraMap (legendreParameterField K parameter) (AlgebraicClosure K) fieldParameter =
            transformedParameter ∧
          ∃ change : WeierstrassCurve.VariableChange (legendreParameterField K parameter),
            change • (legendreWeierstrassCurve parameter).baseChange
                (legendreParameterField K parameter) =
              legendreWeierstrassCurve fieldParameter :=
  ⟨legendreParameterField_finrank_le_four K parameter base_has_sqrt_neg_one,
    legendreParameterField_realizes_algebraicClosure_fiber K parameter parameter_admissible⟩

end AlgebraicClosureFiber

section NumberFieldDegreeBounds

variable (K : Type*) [Field K] [CharZero K] [NumberField K]

/-- For a number-field base, the concrete common field is itself a number
field, with absolute degree bounded by eight times the base degree, and it
simultaneously realizes all the stated actual curve changes. -/
theorem legendreParameterField_numberField_degree_bound_realizes_fiber
    (parameter : K) (parameter_admissible : IsLegendreParameter parameter) :
    NumberField (legendreParameterField K parameter) ∧
      Module.finrank ℚ (legendreParameterField K parameter) ≤ Module.finrank ℚ K * 8 ∧
      ∀ transformedParameter : K, IsLegendreParameter transformedParameter →
        legendreJParameter transformedParameter = legendreJParameter parameter →
        ∃ change : WeierstrassCurve.VariableChange (legendreParameterField K parameter),
          change • (legendreWeierstrassCurve parameter).baseChange
              (legendreParameterField K parameter) =
            (legendreWeierstrassCurve transformedParameter).baseChange
              (legendreParameterField K parameter) := by
  refine ⟨inferInstance, legendreParameterField_absolute_finrank_le K parameter, ?_⟩
  intro transformedParameter transformed_admissible same_invariant
  exact exists_legendreVariableChange_over_parameterField K parameter transformedParameter
    parameter_admissible transformed_admissible same_invariant

/-- The absolute degree bound improves to four times the base degree when
the base number field already contains a square root of `-1`. -/
theorem legendreParameterField_numberField_degree_four_realizes_fiber
    (parameter : K) (parameter_admissible : IsLegendreParameter parameter)
    (base_has_sqrt_neg_one : ∃ imaginaryRoot : K, imaginaryRoot ^ 2 = -1) :
    NumberField (legendreParameterField K parameter) ∧
      Module.finrank ℚ (legendreParameterField K parameter) ≤ Module.finrank ℚ K * 4 ∧
      ∀ transformedParameter : K, IsLegendreParameter transformedParameter →
        legendreJParameter transformedParameter = legendreJParameter parameter →
        ∃ change : WeierstrassCurve.VariableChange (legendreParameterField K parameter),
          change • (legendreWeierstrassCurve parameter).baseChange
              (legendreParameterField K parameter) =
            (legendreWeierstrassCurve transformedParameter).baseChange
              (legendreParameterField K parameter) := by
  refine ⟨inferInstance, legendreParameterField_absolute_finrank_le_of_sqrt_neg_one
    K parameter base_has_sqrt_neg_one, ?_⟩
  intro transformedParameter transformed_admissible same_invariant
  exact exists_legendreVariableChange_over_parameterField K parameter transformedParameter
    parameter_admissible transformed_admissible same_invariant

end NumberFieldDegreeBounds

end LeanFormal.IUT
