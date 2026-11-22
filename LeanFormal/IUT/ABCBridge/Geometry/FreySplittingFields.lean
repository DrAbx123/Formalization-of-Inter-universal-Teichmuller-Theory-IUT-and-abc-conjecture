import LeanFormal.IUT.ABCBridge.Geometry.LegendreQuadraticParameterFields
import LeanFormal.IUT.ABCBridge.Geometry.QuadraticTwistArithmetic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.NumberTheory.NumberField.Basic

/-!
# A common finite field for the Frey and Legendre square roots

The field constructed here is the actual supremum of two intermediate fields
of the same algebraic closure.  Its elements, inclusions, roots and degree
bounds are constructions, rather than fields of an assumed existence record.

For an ABC triple `a+b=c`, the Legendre parameter is `a/c`.  The existing
Legendre field supplies roots `i²=-1`, `u²=a/c`, `v²=1-a/c`; the scaling field
supplies `s²=-c`.  Their images in the common field give roots of `a,b,c` as
`i*u*s`, `i*v*s`, and `i*s`.

Consumer: actual Frey split reduction and Legendre changes of coordinates.
No Galois, IUT admissibility, or Tate uniformization conclusion is asserted.
Status: CANDIDATE, including the imported new producer, pending batch validation.
-/

namespace LeanFormal.IUT

open LegendreQuadraticParameterFields

universe u

section CommonField

variable (K : Type u) [Field K] [NumberField K] (a c : ℕ)

/-- One common actual field containing the Legendre and Frey scaling fields. -/
noncomputable def freySplittingField : IntermediateField K (AlgebraicClosure K) :=
  legendreParameterField K ((a : K) / (c : K)) ⊔ freyScalingField K (c : ℤ)

noncomputable instance freySplittingField_finiteDimensional :
    FiniteDimensional K (freySplittingField K a c) := by
  change FiniteDimensional K
    ↥(legendreParameterField K ((a : K) / (c : K)) ⊔ freyScalingField K (c : ℤ))
  infer_instance

noncomputable instance freySplittingField_numberField :
    NumberField (freySplittingField K a c) := by
  letI := FiniteDimensional.trans ℚ K (freySplittingField K a c)
  exact ⟨⟩

/-- The degree is bounded over the original number field, not only over an unspecified base. -/
theorem freySplittingField_finrank_le_sixteen :
    Module.finrank K (freySplittingField K a c) ≤ 16 := by
  calc
    Module.finrank K (freySplittingField K a c) ≤
        Module.finrank K (legendreParameterField K ((a : K) / (c : K))) *
          Module.finrank K (freyScalingField K (c : ℤ)) :=
      IntermediateField.finrank_sup_le _ _
    _ ≤ 8 * 2 := Nat.mul_le_mul
      (legendreParameterField_finrank_le_eight K ((a : K) / (c : K)))
      (freyScalingField_finrank_le_two K (c : ℤ))
    _ = 16 := rfl

theorem freySplittingField_finrank_le_eight
    (hnegOne : ∃ i : K, i ^ 2 = -1) :
    Module.finrank K (freySplittingField K a c) ≤ 8 := by
  calc
    Module.finrank K (freySplittingField K a c) ≤
        Module.finrank K (legendreParameterField K ((a : K) / (c : K))) *
          Module.finrank K (freyScalingField K (c : ℤ)) :=
      IntermediateField.finrank_sup_le _ _
    _ ≤ 4 * 2 := Nat.mul_le_mul
      (legendreParameterField_finrank_le_four K ((a : K) / (c : K)) hnegOne)
      (freyScalingField_finrank_le_two K (c : ℤ))
    _ = 8 := rfl

theorem freySplittingField_absolute_finrank_le :
    Module.finrank ℚ (freySplittingField K a c) ≤ 16 * Module.finrank ℚ K := by
  rw [← Module.finrank_mul_finrank ℚ K (freySplittingField K a c)]
  calc
    Module.finrank ℚ K * Module.finrank K (freySplittingField K a c) ≤
        Module.finrank ℚ K * 16 :=
      Nat.mul_le_mul_left _ (freySplittingField_finrank_le_sixteen K a c)
    _ = 16 * Module.finrank ℚ K := Nat.mul_comm _ _

/-- The actual inclusion from the Legendre parameter field into the common field. -/
noncomputable def freyLegendreParameterInclusion :
    legendreParameterField K ((a : K) / (c : K)) →ₐ[K] freySplittingField K a c :=
  IntermediateField.inclusion le_sup_left

/-- The actual inclusion from the scaling field into the common field. -/
noncomputable def freyScalingInclusion :
    freyScalingField K (c : ℤ) →ₐ[K] freySplittingField K a c :=
  IntermediateField.inclusion le_sup_right

noncomputable def freySplittingSqrtNegOne : freySplittingField K a c :=
  freyLegendreParameterInclusion K a c
    (legendreSqrtNegOne K ((a : K) / (c : K)))

noncomputable def freySplittingParameterRoot : freySplittingField K a c :=
  freyLegendreParameterInclusion K a c
    (legendreSqrtParameter K ((a : K) / (c : K)))

noncomputable def freySplittingComplementRoot : freySplittingField K a c :=
  freyLegendreParameterInclusion K a c
    (legendreSqrtComplement K ((a : K) / (c : K)))

noncomputable def freySplittingScalingRoot : freySplittingField K a c :=
  freyScalingInclusion K a c (freyScalingRoot K (c : ℤ))

@[simp] theorem freySplittingSqrtNegOne_sq :
    freySplittingSqrtNegOne K a c ^ 2 = -1 := by
  unfold freySplittingSqrtNegOne
  rw [← map_pow, legendreSqrtNegOne_sq]
  simp

@[simp] theorem freySplittingParameterRoot_sq :
    freySplittingParameterRoot K a c ^ 2 =
      (a : freySplittingField K a c) / (c : freySplittingField K a c) := by
  unfold freySplittingParameterRoot
  rw [← map_pow, legendreSqrtParameter_sq, AlgHom.commutes]
  simp

@[simp] theorem freySplittingComplementRoot_sq :
    freySplittingComplementRoot K a c ^ 2 =
      1 - (a : freySplittingField K a c) / (c : freySplittingField K a c) := by
  unfold freySplittingComplementRoot
  rw [← map_pow, legendreSqrtComplement_sq]
  simp only [map_sub, map_one, AlgHom.commutes]
  simp

@[simp] theorem freySplittingScalingRoot_sq :
    freySplittingScalingRoot K a c ^ 2 = -(c : freySplittingField K a c) := by
  unfold freySplittingScalingRoot
  rw [← map_pow, freyScalingRoot_sq]
  simp

noncomputable def freySplittingSqrtLeft : freySplittingField K a c :=
  freySplittingSqrtNegOne K a c * freySplittingParameterRoot K a c *
    freySplittingScalingRoot K a c

noncomputable def freySplittingSqrtRight : freySplittingField K a c :=
  freySplittingSqrtNegOne K a c * freySplittingComplementRoot K a c *
    freySplittingScalingRoot K a c

noncomputable def freySplittingSqrtSum : freySplittingField K a c :=
  freySplittingSqrtNegOne K a c * freySplittingScalingRoot K a c

@[simp] theorem freySplittingSqrtSum_sq :
    freySplittingSqrtSum K a c ^ 2 = (c : freySplittingField K a c) := by
  rw [freySplittingSqrtSum, mul_pow, freySplittingSqrtNegOne_sq,
    freySplittingScalingRoot_sq]
  ring

theorem freySplittingSqrtNegOne_ne_zero : freySplittingSqrtNegOne K a c ≠ 0 := by
  intro hzero
  have hsquare := freySplittingSqrtNegOne_sq K a c
  simp [hzero] at hsquare

noncomputable def freySplittingNegOneUnit : (freySplittingField K a c)ˣ :=
  Units.mk0 (freySplittingSqrtNegOne K a c) (freySplittingSqrtNegOne_ne_zero K a c)

@[simp] theorem freySplittingNegOneUnit_sq :
    (freySplittingNegOneUnit K a c : freySplittingField K a c) ^ 2 = -1 :=
  freySplittingSqrtNegOne_sq K a c

end CommonField

section ABCRoots

variable (K : Type u) [Field K] [NumberField K]
variable {a b c : ℕ} (h : IsABCTriple a b c)
include h

theorem freySplittingSum_natCast_ne_zero : (c : freySplittingField K a c) ≠ 0 := by
  have hpositive := (isABCTriple_iff_positivePrimitiveAdditiveTriple a b c).mp h
  apply Nat.cast_ne_zero.mpr
  exact Nat.ne_of_gt (hpositive.2.2.1 ▸ Nat.add_pos_left hpositive.1 b)

theorem freySplittingSqrtLeft_sq :
    freySplittingSqrtLeft K a c ^ 2 = (a : freySplittingField K a c) := by
  have hc := freySplittingSum_natCast_ne_zero K h
  rw [freySplittingSqrtLeft, mul_pow, mul_pow, freySplittingSqrtNegOne_sq,
    freySplittingParameterRoot_sq, freySplittingScalingRoot_sq]
  field_simp [hc] <;> ring

theorem freySplittingComplement_eq_right_div_sum :
    1 - (a : freySplittingField K a c) / (c : freySplittingField K a c) =
      (b : freySplittingField K a c) / (c : freySplittingField K a c) := by
  have hpositive := (isABCTriple_iff_positivePrimitiveAdditiveTriple a b c).mp h
  have hadd : (a : freySplittingField K a c) + (b : freySplittingField K a c) =
      (c : freySplittingField K a c) := by
    exact_mod_cast hpositive.2.2.1
  have hab : (a : freySplittingField K a c) + (b : freySplittingField K a c) ≠ 0 := by
    rw [hadd]
    exact freySplittingSum_natCast_ne_zero K h
  rw [← hadd]
  field_simp [hab] <;> ring

theorem freySplittingSqrtRight_sq :
    freySplittingSqrtRight K a c ^ 2 = (b : freySplittingField K a c) := by
  have hc := freySplittingSum_natCast_ne_zero K h
  rw [freySplittingSqrtRight, mul_pow, mul_pow, freySplittingSqrtNegOne_sq,
    freySplittingComplementRoot_sq, freySplittingScalingRoot_sq,
    freySplittingComplement_eq_right_div_sum K h]
  field_simp [hc] <;> ring

theorem freySplittingSqrtLeft_ne_zero : freySplittingSqrtLeft K a c ≠ 0 := by
  have hpositive := (isABCTriple_iff_positivePrimitiveAdditiveTriple a b c).mp h
  have ha : (a : freySplittingField K a c) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hpositive.1)
  intro hzero
  apply ha
  rw [← freySplittingSqrtLeft_sq K h, hzero]
  simp

theorem freySplittingSqrtRight_ne_zero : freySplittingSqrtRight K a c ≠ 0 := by
  have hpositive := (isABCTriple_iff_positivePrimitiveAdditiveTriple a b c).mp h
  have hb : (b : freySplittingField K a c) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hpositive.2.1)
  intro hzero
  apply hb
  rw [← freySplittingSqrtRight_sq K h, hzero]
  simp

theorem freySplittingSqrtSum_ne_zero : freySplittingSqrtSum K a c ≠ 0 := by
  intro hzero
  apply freySplittingSum_natCast_ne_zero K h
  rw [← freySplittingSqrtSum_sq, hzero]
  simp

theorem freySplittingScalingRoot_ne_zero : freySplittingScalingRoot K a c ≠ 0 := by
  have hproduct := freySplittingSqrtSum_ne_zero K h
  change freySplittingSqrtNegOne K a c * freySplittingScalingRoot K a c ≠ 0 at hproduct
  exact (mul_ne_zero_iff.mp hproduct).2

theorem freySplittingParameterRoot_ne_zero : freySplittingParameterRoot K a c ≠ 0 := by
  have hproduct := freySplittingSqrtLeft_ne_zero K h
  change freySplittingSqrtNegOne K a c * freySplittingParameterRoot K a c *
    freySplittingScalingRoot K a c ≠ 0 at hproduct
  exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hproduct).1).2

theorem freySplittingComplementRoot_ne_zero : freySplittingComplementRoot K a c ≠ 0 := by
  have hproduct := freySplittingSqrtRight_ne_zero K h
  change freySplittingSqrtNegOne K a c * freySplittingComplementRoot K a c *
    freySplittingScalingRoot K a c ≠ 0 at hproduct
  exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hproduct).1).2

/-- All four required square roots live in this one explicitly constructed field. -/
theorem freySplittingField_contains_abc_roots :
    ∃ i x y z : freySplittingField K a c,
      i ^ 2 = -1 ∧ x ^ 2 = (a : freySplittingField K a c) ∧
      y ^ 2 = (b : freySplittingField K a c) ∧ z ^ 2 = (c : freySplittingField K a c) ∧
      i ≠ 0 ∧ x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 := by
  exact ⟨freySplittingSqrtNegOne K a c, freySplittingSqrtLeft K a c,
    freySplittingSqrtRight K a c, freySplittingSqrtSum K a c,
    freySplittingSqrtNegOne_sq K a c, freySplittingSqrtLeft_sq K h,
    freySplittingSqrtRight_sq K h, freySplittingSqrtSum_sq K a c,
    freySplittingSqrtNegOne_ne_zero K a c, freySplittingSqrtLeft_ne_zero K h,
    freySplittingSqrtRight_ne_zero K h, freySplittingSqrtSum_ne_zero K h⟩

noncomputable def freySplittingLeftUnit : (freySplittingField K a c)ˣ :=
  Units.mk0 (freySplittingSqrtLeft K a c) (freySplittingSqrtLeft_ne_zero K h)

noncomputable def freySplittingRightUnit : (freySplittingField K a c)ˣ :=
  Units.mk0 (freySplittingSqrtRight K a c) (freySplittingSqrtRight_ne_zero K h)

noncomputable def freySplittingSumUnit : (freySplittingField K a c)ˣ :=
  Units.mk0 (freySplittingSqrtSum K a c) (freySplittingSqrtSum_ne_zero K h)

/-- This unit is the required square root of `-c` for the actual Legendre scaling. -/
noncomputable def freySplittingScalingUnit : (freySplittingField K a c)ˣ :=
  Units.mk0 (freySplittingScalingRoot K a c) (freySplittingScalingRoot_ne_zero K h)

noncomputable def freySplittingParameterUnit : (freySplittingField K a c)ˣ :=
  Units.mk0 (freySplittingParameterRoot K a c) (freySplittingParameterRoot_ne_zero K h)

noncomputable def freySplittingComplementUnit : (freySplittingField K a c)ˣ :=
  Units.mk0 (freySplittingComplementRoot K a c) (freySplittingComplementRoot_ne_zero K h)

@[simp] theorem freySplittingLeftUnit_sq :
    (freySplittingLeftUnit K h : freySplittingField K a c) ^ 2 = (a : freySplittingField K a c) :=
  freySplittingSqrtLeft_sq K h

@[simp] theorem freySplittingRightUnit_sq :
    (freySplittingRightUnit K h : freySplittingField K a c) ^ 2 = (b : freySplittingField K a c) :=
  freySplittingSqrtRight_sq K h

@[simp] theorem freySplittingSumUnit_sq :
    (freySplittingSumUnit K h : freySplittingField K a c) ^ 2 = (c : freySplittingField K a c) :=
  freySplittingSqrtSum_sq K a c

@[simp] theorem freySplittingScalingUnit_sq :
    (freySplittingScalingUnit K h : freySplittingField K a c) ^ 2 = -(c : freySplittingField K a c) :=
  freySplittingScalingRoot_sq K a c

@[simp] theorem freySplittingParameterUnit_sq :
    (freySplittingParameterUnit K h : freySplittingField K a c) ^ 2 =
      (a : freySplittingField K a c) / (c : freySplittingField K a c) :=
  freySplittingParameterRoot_sq K a c

@[simp] theorem freySplittingComplementUnit_sq :
    (freySplittingComplementUnit K h : freySplittingField K a c) ^ 2 =
      (b : freySplittingField K a c) / (c : freySplittingField K a c) := by
  change freySplittingComplementRoot K a c ^ 2 = _
  rw [freySplittingComplementRoot_sq, freySplittingComplement_eq_right_div_sum K h]

end ABCRoots

section ActualCurveInTheCommonField

variable (K : Type u) [Field K] [NumberField K]

/-- The actual integral Frey model base changed into the common finite field. -/
noncomputable def freySplittingCurve (a b c : ℕ) :
    WeierstrassCurve (freySplittingField K a c) :=
  (integralFreyWeierstrassCurve a b).map (algebraMap ℤ (freySplittingField K a c))

@[simp] theorem freySplittingCurve_eq (a b c : ℕ) :
    freySplittingCurve K a b c =
      freyWeierstrassCurve (a : freySplittingField K a c) (b : freySplittingField K a c) := by
  exact integralFreyWeierstrassCurve_map a b (algebraMap ℤ (freySplittingField K a c))

/-- The same curve is the exact base change of the rational Frey model. -/
theorem freySplittingCurve_eq_rational_map (a b c : ℕ) :
    (rationalFreyWeierstrassCurve a b).map (algebraMap ℚ (freySplittingField K a c)) =
      freySplittingCurve K a b c := by
  rw [rationalFreyWeierstrassCurve_map, freySplittingCurve_eq]

theorem freySplittingCurve_isElliptic {a b c : ℕ} (h : IsABCTriple a b c) :
    (freySplittingCurve K a b c).IsElliptic := by
  rw [freySplittingCurve_eq]
  exact freyWeierstrassCurve_isElliptic_of_isABCTriple h

theorem freySplittingCurve_discriminant {a b c : ℕ} (h : IsABCTriple a b c) :
    (freySplittingCurve K a b c).Δ =
      16 * (a : freySplittingField K a c) ^ 2 * (b : freySplittingField K a c) ^ 2 *
        (c : freySplittingField K a c) ^ 2 := by
  exact integralFreyWeierstrassCurve_map_discriminant_of_isABCTriple h
    (algebraMap ℤ (freySplittingField K a c))

/-- The constructed scaling unit removes the `-c` twist by the actual variable-change action. -/
theorem freySplittingCurve_scaling_variableChange {a b c : ℕ} (h : IsABCTriple a b c) :
    quadraticTwistRootVariableChange (freySplittingScalingUnit K h) •
      zeroOddWeierstrassQuadraticTwist (freySplittingCurve K a b c)
        (-(c : freySplittingField K a c))
        (by simp [freySplittingCurve_eq]) (by simp [freySplittingCurve_eq]) =
      freySplittingCurve K a b c := by
  apply quadraticTwistRootVariableChange_smul
  exact freySplittingScalingUnit_sq K h

end ActualCurveInTheCommonField

end LeanFormal.IUT
