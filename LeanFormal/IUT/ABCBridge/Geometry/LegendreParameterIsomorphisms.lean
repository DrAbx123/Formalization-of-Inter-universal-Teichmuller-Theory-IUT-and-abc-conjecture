import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import LeanFormal.IUT.ABCBridge.Geometry.LegendreWeierstrassCurve
import LeanFormal.IUT.ABCBridge.Geometry.LegendreParameterSymmetry

/-!
# Actual variable changes between Legendre parameters

The native Mathlib variable-change group acts on actual Weierstrass equations.
Here its parameter `u` is a unit, so every change is invertible. A statement
`C • W = W'` records the curve obtained after substituting the old coordinates
`(u^2 * X + r, u^3 * Y + u^2 * s * X + t)` into `W`.

The complement change requires a square root of `-1`, and the reciprocal
change requires a square root of the parameter. A single field with roots of
`-1`, `lambda`, and `1 - lambda` realizes the complete six-transform orbit.
No assertion that equal invariants imply an isomorphism over the original
ground field is made.
-/

namespace LeanFormal.IUT

section VariableChangeDefinitions

variable {R : Type*} [CommRing R]

/-- Substitution with old coordinates `(i^2 * X + 1, i^3 * Y)`. -/
def legendreComplementVariableChange (imaginaryUnit : Rˣ) :
    WeierstrassCurve.VariableChange R :=
  ⟨imaginaryUnit, 1, 0, 0⟩

/-- Substitution with old coordinates `(u^2 * X, u^3 * Y)`. -/
def legendreReciprocalVariableChange (parameterRoot : Rˣ) :
    WeierstrassCurve.VariableChange R :=
  ⟨parameterRoot, 0, 0, 0⟩

/-- Complement followed by reciprocal, in the native left-action order. -/
def legendreReciprocalComplementVariableChange
    (imaginaryUnit complementRoot : Rˣ) : WeierstrassCurve.VariableChange R :=
  legendreReciprocalVariableChange complementRoot *
    legendreComplementVariableChange imaginaryUnit

/-- Complement, reciprocal, then complement. -/
def legendreQuotientVariableChange
    (imaginaryUnit complementRoot : Rˣ) : WeierstrassCurve.VariableChange R :=
  legendreComplementVariableChange imaginaryUnit *
    legendreReciprocalComplementVariableChange imaginaryUnit complementRoot

/-- Reciprocal followed by complement. -/
def legendreShiftedQuotientVariableChange
    (imaginaryUnit parameterRoot : Rˣ) : WeierstrassCurve.VariableChange R :=
  legendreComplementVariableChange imaginaryUnit *
    legendreReciprocalVariableChange parameterRoot

end VariableChangeDefinitions

section ParameterTransport

variable {K L : Type*} [Field K] [Field L]

/-- A field homomorphism preserves the admissible Legendre parameter domain. -/
theorem isLegendreParameter_map (fieldMap : K →+* L) {parameter : K}
    (admissible : IsLegendreParameter parameter) :
    IsLegendreParameter (fieldMap parameter) := by
  constructor
  · intro mapped_zero
    apply admissible.1
    apply fieldMap.injective
    simpa using mapped_zero
  · intro mapped_one
    apply admissible.2
    apply fieldMap.injective
    simpa using mapped_one

/-- The explicit rational invariant commutes with field homomorphisms. -/
theorem legendreJParameter_map (fieldMap : K →+* L) (parameter : K) :
    legendreJParameter (fieldMap parameter) = fieldMap (legendreJParameter parameter) := by
  simp [legendreJParameter, map_ofNat]

end ParameterTransport

section ActualCurveChanges

variable {K : Type*} [Field K]

/-- With `i^2 = -1`, the native substitution sends the equation at `lambda`
to the equation at `1 - lambda`. Nonsingularity is not needed for this identity
of actual Weierstrass equations. -/
theorem legendreComplementVariableChange_smul (parameter : K) (imaginaryUnit : Kˣ)
    (imaginaryUnit_square : (imaginaryUnit : K) ^ 2 = -1) :
    legendreComplementVariableChange imaginaryUnit • legendreWeierstrassCurve parameter =
      legendreWeierstrassCurve (1 - parameter) := by
  have inverse_square : (↑(imaginaryUnit⁻¹) : K) ^ 2 = -1 := by
    have inverse_relation := pow_mul_pow_eq_one 2 imaginaryUnit.inv_mul
    rw [imaginaryUnit_square] at inverse_relation
    linear_combination -inverse_relation
  have inverse_fourth : (↑(imaginaryUnit⁻¹) : K) ^ 4 = 1 := by
    calc
      (↑(imaginaryUnit⁻¹) : K) ^ 4 = ((↑(imaginaryUnit⁻¹) : K) ^ 2) ^ 2 := by ring
      _ = 1 := by rw [inverse_square]; ring
  ext <;>
    simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆, legendreComplementVariableChange,
      legendreWeierstrassCurve_a₁, legendreWeierstrassCurve_a₂, legendreWeierstrassCurve_a₃,
      legendreWeierstrassCurve_a₄, legendreWeierstrassCurve_a₆, inverse_square, inverse_fourth] <;>
    ring

/-- With `u^2 = lambda`, the native substitution sends the equation at `lambda`
to the equation at `1 / lambda`. The unit hypothesis supplies `lambda != 0`. -/
theorem legendreReciprocalVariableChange_smul (parameter : K) (parameterRoot : Kˣ)
    (parameterRoot_square : (parameterRoot : K) ^ 2 = parameter) :
    legendreReciprocalVariableChange parameterRoot • legendreWeierstrassCurve parameter =
      legendreWeierstrassCurve (1 / parameter) := by
  have parameter_ne_zero : parameter ≠ 0 := by
    rw [← parameterRoot_square]
    exact pow_ne_zero 2 parameterRoot.ne_zero
  have inverse_square : (↑(parameterRoot⁻¹) : K) ^ 2 = 1 / parameter := by
    apply (eq_div_iff parameter_ne_zero).mpr
    simpa only [parameterRoot_square] using pow_mul_pow_eq_one 2 parameterRoot.inv_mul
  have inverse_fourth : (↑(parameterRoot⁻¹) : K) ^ 4 = (1 / parameter) ^ 2 := by
    calc
      (↑(parameterRoot⁻¹) : K) ^ 4 = ((↑(parameterRoot⁻¹) : K) ^ 2) ^ 2 := by ring
      _ = (1 / parameter) ^ 2 := by rw [inverse_square]
  ext <;>
    simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆, legendreReciprocalVariableChange,
      legendreWeierstrassCurve_a₁, legendreWeierstrassCurve_a₂, legendreWeierstrassCurve_a₃,
      legendreWeierstrassCurve_a₄, legendreWeierstrassCurve_a₆, inverse_square, inverse_fourth] <;>
    field_simp [parameter_ne_zero] <;>
    ring

/-- The inverse native change recovers the original equation. -/
theorem legendreVariableChange_inverse {parameter transformedParameter : K}
    (change : WeierstrassCurve.VariableChange K)
    (change_equation : change • legendreWeierstrassCurve parameter =
      legendreWeierstrassCurve transformedParameter) :
    change⁻¹ • legendreWeierstrassCurve transformedParameter =
      legendreWeierstrassCurve parameter := by
  rw [← change_equation, inv_smul_smul]

theorem legendreComplementVariableChange_inverse_smul
    (parameter : K) (imaginaryUnit : Kˣ)
    (imaginaryUnit_square : (imaginaryUnit : K) ^ 2 = -1) :
    (legendreComplementVariableChange imaginaryUnit)⁻¹ •
        legendreWeierstrassCurve (1 - parameter) = legendreWeierstrassCurve parameter :=
  legendreVariableChange_inverse _
    (legendreComplementVariableChange_smul parameter imaginaryUnit imaginaryUnit_square)

theorem legendreReciprocalVariableChange_inverse_smul
    (parameter : K) (parameterRoot : Kˣ)
    (parameterRoot_square : (parameterRoot : K) ^ 2 = parameter) :
    (legendreReciprocalVariableChange parameterRoot)⁻¹ •
        legendreWeierstrassCurve (1 / parameter) = legendreWeierstrassCurve parameter :=
  legendreVariableChange_inverse _
    (legendreReciprocalVariableChange_smul parameter parameterRoot parameterRoot_square)

theorem legendreReciprocalComplementVariableChange_smul
    (parameter : K) (imaginaryUnit complementRoot : Kˣ)
    (imaginaryUnit_square : (imaginaryUnit : K) ^ 2 = -1)
    (complementRoot_square : (complementRoot : K) ^ 2 = 1 - parameter) :
    legendreReciprocalComplementVariableChange imaginaryUnit complementRoot •
        legendreWeierstrassCurve parameter =
      legendreWeierstrassCurve (1 / (1 - parameter)) := by
  rw [legendreReciprocalComplementVariableChange, mul_smul,
    legendreComplementVariableChange_smul parameter imaginaryUnit imaginaryUnit_square]
  exact legendreReciprocalVariableChange_smul (1 - parameter)
    complementRoot complementRoot_square

theorem legendreQuotientVariableChange_smul
    {parameter : K} (parameter_ne_one : parameter ≠ 1)
    (imaginaryUnit complementRoot : Kˣ)
    (imaginaryUnit_square : (imaginaryUnit : K) ^ 2 = -1)
    (complementRoot_square : (complementRoot : K) ^ 2 = 1 - parameter) :
    legendreQuotientVariableChange imaginaryUnit complementRoot •
        legendreWeierstrassCurve parameter =
      legendreWeierstrassCurve (parameter / (parameter - 1)) := by
  rw [legendreQuotientVariableChange, mul_smul,
    legendreReciprocalComplementVariableChange_smul parameter imaginaryUnit complementRoot
      imaginaryUnit_square complementRoot_square,
    legendreComplementVariableChange_smul (1 / (1 - parameter))
      imaginaryUnit imaginaryUnit_square]
  congr 1
  field_simp [sub_ne_zero.mpr parameter_ne_one,
    sub_ne_zero.mpr (Ne.symm parameter_ne_one)]
  <;> ring

theorem legendreShiftedQuotientVariableChange_smul
    {parameter : K} (parameter_ne_zero : parameter ≠ 0)
    (imaginaryUnit parameterRoot : Kˣ)
    (imaginaryUnit_square : (imaginaryUnit : K) ^ 2 = -1)
    (parameterRoot_square : (parameterRoot : K) ^ 2 = parameter) :
    legendreShiftedQuotientVariableChange imaginaryUnit parameterRoot •
        legendreWeierstrassCurve parameter =
      legendreWeierstrassCurve ((parameter - 1) / parameter) := by
  rw [legendreShiftedQuotientVariableChange, mul_smul,
    legendreReciprocalVariableChange_smul parameter parameterRoot parameterRoot_square,
    legendreComplementVariableChange_smul (1 / parameter) imaginaryUnit imaginaryUnit_square]
  congr 1
  field_simp [parameter_ne_zero]
  <;> ring

end ActualCurveChanges

section CompleteAdmissibleOrbit

variable {K : Type*} [Field K] [CharZero K]

/-- All six admissible parameter transforms are related by actual native changes
when the stated three square roots lie in the ground field. -/
theorem exists_legendreVariableChange_of_mem_transforms
    {parameter transformedParameter : K}
    (parameter_admissible : IsLegendreParameter parameter)
    (imaginaryUnit parameterRoot complementRoot : Kˣ)
    (imaginaryUnit_square : (imaginaryUnit : K) ^ 2 = -1)
    (parameterRoot_square : (parameterRoot : K) ^ 2 = parameter)
    (complementRoot_square : (complementRoot : K) ^ 2 = 1 - parameter)
    (membership : transformedParameter ∈ legendreParameterTransforms parameter) :
    ∃ change : WeierstrassCurve.VariableChange K,
      change • legendreWeierstrassCurve parameter =
        legendreWeierstrassCurve transformedParameter := by
  rcases (mem_legendreParameterTransforms parameter transformedParameter).mp membership with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, one_smul _ _⟩
  · exact ⟨legendreComplementVariableChange imaginaryUnit,
      legendreComplementVariableChange_smul parameter imaginaryUnit imaginaryUnit_square⟩
  · exact ⟨legendreReciprocalVariableChange parameterRoot,
      legendreReciprocalVariableChange_smul parameter parameterRoot parameterRoot_square⟩
  · exact ⟨legendreReciprocalComplementVariableChange imaginaryUnit complementRoot,
      legendreReciprocalComplementVariableChange_smul parameter imaginaryUnit complementRoot
        imaginaryUnit_square complementRoot_square⟩
  · exact ⟨legendreQuotientVariableChange imaginaryUnit complementRoot,
      legendreQuotientVariableChange_smul parameter_admissible.2 imaginaryUnit complementRoot
        imaginaryUnit_square complementRoot_square⟩
  · exact ⟨legendreShiftedQuotientVariableChange imaginaryUnit parameterRoot,
      legendreShiftedQuotientVariableChange_smul parameter_admissible.1 imaginaryUnit parameterRoot
        imaginaryUnit_square parameterRoot_square⟩

/-- Equal parameter invariants yield an actual invertible change only under the
explicit square-root hypotheses; no descent to a smaller field is asserted. -/
theorem exists_legendreVariableChange_of_same_invariant
    {parameter transformedParameter : K}
    (parameter_admissible : IsLegendreParameter parameter)
    (transformed_admissible : IsLegendreParameter transformedParameter)
    (imaginaryUnit parameterRoot complementRoot : Kˣ)
    (imaginaryUnit_square : (imaginaryUnit : K) ^ 2 = -1)
    (parameterRoot_square : (parameterRoot : K) ^ 2 = parameter)
    (complementRoot_square : (complementRoot : K) ^ 2 = 1 - parameter)
    (same_invariant : legendreJParameter transformedParameter = legendreJParameter parameter) :
    ∃ change : WeierstrassCurve.VariableChange K,
      change • legendreWeierstrassCurve parameter =
        legendreWeierstrassCurve transformedParameter :=
  exists_legendreVariableChange_of_mem_transforms parameter_admissible
    imaginaryUnit parameterRoot complementRoot imaginaryUnit_square parameterRoot_square
    complementRoot_square
    ((legendreJParameter_eq_iff_mem_transforms parameter_admissible transformed_admissible).mp
      same_invariant)

/-- Both directions of the actual curve transformation, with the same native object. -/
theorem exists_reversible_legendreVariableChange_of_same_invariant
    {parameter transformedParameter : K}
    (parameter_admissible : IsLegendreParameter parameter)
    (transformed_admissible : IsLegendreParameter transformedParameter)
    (imaginaryUnit parameterRoot complementRoot : Kˣ)
    (imaginaryUnit_square : (imaginaryUnit : K) ^ 2 = -1)
    (parameterRoot_square : (parameterRoot : K) ^ 2 = parameter)
    (complementRoot_square : (complementRoot : K) ^ 2 = 1 - parameter)
    (same_invariant : legendreJParameter transformedParameter = legendreJParameter parameter) :
    ∃ change : WeierstrassCurve.VariableChange K,
      change • legendreWeierstrassCurve parameter = legendreWeierstrassCurve transformedParameter ∧
        change⁻¹ • legendreWeierstrassCurve transformedParameter =
          legendreWeierstrassCurve parameter := by
  obtain ⟨change, change_equation⟩ := exists_legendreVariableChange_of_same_invariant
    parameter_admissible transformed_admissible imaginaryUnit parameterRoot complementRoot
    imaginaryUnit_square parameterRoot_square complementRoot_square same_invariant
  exact ⟨change, change_equation, legendreVariableChange_inverse change change_equation⟩

/-- Element-valued square roots are promoted to native units using admissibility. -/
theorem exists_legendreVariableChange_of_square_roots
    {parameter transformedParameter : K}
    (parameter_admissible : IsLegendreParameter parameter)
    (transformed_admissible : IsLegendreParameter transformedParameter)
    (imaginaryRoot parameterRoot complementRoot : K)
    (imaginaryRoot_square : imaginaryRoot ^ 2 = -1)
    (parameterRoot_square : parameterRoot ^ 2 = parameter)
    (complementRoot_square : complementRoot ^ 2 = 1 - parameter)
    (same_invariant : legendreJParameter transformedParameter = legendreJParameter parameter) :
    ∃ change : WeierstrassCurve.VariableChange K,
      change • legendreWeierstrassCurve parameter =
        legendreWeierstrassCurve transformedParameter := by
  have imaginaryRoot_ne_zero : imaginaryRoot ≠ 0 := by
    intro root_zero
    rw [root_zero] at imaginaryRoot_square
    norm_num at imaginaryRoot_square
  have parameterRoot_ne_zero : parameterRoot ≠ 0 := by
    intro root_zero
    apply parameter_admissible.1
    rw [← parameterRoot_square, root_zero]
    simp
  have complementRoot_ne_zero : complementRoot ≠ 0 := by
    intro root_zero
    apply (isLegendreParameter_one_sub parameter_admissible).1
    rw [← complementRoot_square, root_zero]
    simp
  exact exists_legendreVariableChange_of_same_invariant parameter_admissible transformed_admissible
    (Units.mk0 imaginaryRoot imaginaryRoot_ne_zero)
    (Units.mk0 parameterRoot parameterRoot_ne_zero)
    (Units.mk0 complementRoot complementRoot_ne_zero)
    imaginaryRoot_square parameterRoot_square complementRoot_square same_invariant

end CompleteAdmissibleOrbit

section ExtensionTransport

variable {K L : Type*} [Field K] [Field L] [CharZero K] [CharZero L]

/-- The actual mapped Legendre equations become related over a field containing
the stated roots of the mapped parameter. Extension existence is not assumed
implicitly or encoded as an unproved structure field. -/
theorem exists_legendreVariableChange_after_fieldMap
    (fieldMap : K →+* L) {parameter transformedParameter : K}
    (parameter_admissible : IsLegendreParameter parameter)
    (transformed_admissible : IsLegendreParameter transformedParameter)
    (imaginaryUnit parameterRoot complementRoot : Lˣ)
    (imaginaryUnit_square : (imaginaryUnit : L) ^ 2 = -1)
    (parameterRoot_square : (parameterRoot : L) ^ 2 = fieldMap parameter)
    (complementRoot_square : (complementRoot : L) ^ 2 = 1 - fieldMap parameter)
    (same_invariant : legendreJParameter transformedParameter = legendreJParameter parameter) :
    ∃ change : WeierstrassCurve.VariableChange L,
      change • (legendreWeierstrassCurve parameter).map fieldMap =
        (legendreWeierstrassCurve transformedParameter).map fieldMap := by
  have mapped_invariant :
      legendreJParameter (fieldMap transformedParameter) =
        legendreJParameter (fieldMap parameter) := by
    rw [legendreJParameter_map, legendreJParameter_map]
    exact congrArg fieldMap same_invariant
  obtain ⟨change, change_equation⟩ := exists_legendreVariableChange_of_same_invariant
    (isLegendreParameter_map fieldMap parameter_admissible)
    (isLegendreParameter_map fieldMap transformed_admissible)
    imaginaryUnit parameterRoot complementRoot imaginaryUnit_square
    parameterRoot_square complementRoot_square mapped_invariant
  refine ⟨change, ?_⟩
  simpa only [legendreWeierstrassCurve_map] using change_equation

/-- The field-map result in the native algebra base-change notation. -/
theorem exists_legendreVariableChange_after_baseChange
    [Algebra K L] {parameter transformedParameter : K}
    (parameter_admissible : IsLegendreParameter parameter)
    (transformed_admissible : IsLegendreParameter transformedParameter)
    (imaginaryUnit parameterRoot complementRoot : Lˣ)
    (imaginaryUnit_square : (imaginaryUnit : L) ^ 2 = -1)
    (parameterRoot_square : (parameterRoot : L) ^ 2 = algebraMap K L parameter)
    (complementRoot_square : (complementRoot : L) ^ 2 = 1 - algebraMap K L parameter)
    (same_invariant : legendreJParameter transformedParameter = legendreJParameter parameter) :
    ∃ change : WeierstrassCurve.VariableChange L,
      change • (legendreWeierstrassCurve parameter).baseChange L =
        (legendreWeierstrassCurve transformedParameter).baseChange L := by
  obtain ⟨change, change_equation⟩ := exists_legendreVariableChange_after_fieldMap
    (algebraMap K L) parameter_admissible transformed_admissible
    imaginaryUnit parameterRoot complementRoot imaginaryUnit_square
    parameterRoot_square complementRoot_square same_invariant
  refine ⟨change, ?_⟩
  simpa only [legendreWeierstrassCurve_map, legendreWeierstrassCurve_baseChange]
    using change_equation

end ExtensionTransport

end LeanFormal.IUT
