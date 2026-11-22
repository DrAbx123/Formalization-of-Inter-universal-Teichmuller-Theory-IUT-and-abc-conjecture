import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompactHullScaling
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume

/-! # Unit scaling of the canonical unit reference

For a unit `u` of the arithmetic tensor block, the set `u • O` is an open
compact image of the open compact canonical unit reference `O` under the
finite-dimensional linear homeomorphism `x ↦ u * x`.  Hence it has positive
finite Haar mass. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.UnitSmulCanonicalUnitReferenceActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
open scoped Pointwise

universe uK uI uV

variable {p : Nat} [Fact p.Prime]
variable {K : Type uK} [Field K] [NumberField K]
variable {ι : Type uI} [Fintype ι]
variable {V : ι -> Type uV} [∀ i, Fintype (V i)]
variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : ι) -> V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (μ : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure μ]

abbrev X := ArithmeticTensorTupleBlock places tuple

local instance : SMul (X places tuple) (X places tuple) :=
  ⟨fun a b => a * b⟩

/-- Multiplication by a unit as a Qp-linear equivalence. -/
noncomputable def unitMulLinearEquiv (u : (X places tuple)ˣ) :
    X places tuple ≃ₗ[ℚ_[p]] X places tuple where
  toFun := fun x => (u : X places tuple) * x
  invFun := fun x => (↑(u⁻¹) : X places tuple) * x
  map_add' := by
    intro x y
    simp [mul_add]
  map_smul' := by
    intro c x
    simp [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm]
  left_inv := by
    intro x
    simp [← mul_assoc]
  right_inv := by
    intro x
    simp [← mul_assoc]

theorem unitMulLinearEquiv_apply
    (u : (X places tuple)ˣ) (x : X places tuple) :
    unitMulLinearEquiv (p := p) places tuple u x = (u : X places tuple) * x := rfl

theorem unitMulLinearEquiv_symm_apply
    (u : (X places tuple)ˣ) (x : X places tuple) :
    (unitMulLinearEquiv (p := p) places tuple u).symm x =
      (↑(u⁻¹) : X places tuple) * x := rfl

/-- The canonical unit reference scaled by a unit is open. -/
theorem isOpen_unit_smul_canonicalUnitReference
    (u : (X places tuple)ˣ) :
    IsOpen ((u : X places tuple) •
      arithmeticTupleCanonicalUnitReference places tuple) := by
  let e := (unitMulLinearEquiv (p := p) places tuple u).toContinuousLinearEquiv
  have hset : ((u : X places tuple) •
      arithmeticTupleCanonicalUnitReference places tuple) =
      e '' arithmeticTupleCanonicalUnitReference places tuple := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, (unitMulLinearEquiv_apply (p := p) places tuple u y).symm⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, unitMulLinearEquiv_apply (p := p) places tuple u y⟩
  rw [hset]
  exact e.toHomeomorph.isOpenMap _
    (isOpen_arithmeticTupleCanonicalUnitReference places tuple)

/-- The canonical unit reference scaled by a unit is compact. -/
theorem isCompact_unit_smul_canonicalUnitReference
    (u : (X places tuple)ˣ) :
    IsCompact ((u : X places tuple) •
      arithmeticTupleCanonicalUnitReference places tuple) := by
  let e := (unitMulLinearEquiv (p := p) places tuple u).toContinuousLinearEquiv
  have hset : ((u : X places tuple) •
      arithmeticTupleCanonicalUnitReference places tuple) =
      e '' arithmeticTupleCanonicalUnitReference places tuple := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, (unitMulLinearEquiv_apply (p := p) places tuple u y).symm⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, unitMulLinearEquiv_apply (p := p) places tuple u y⟩
  rw [hset]
  exact (isCompact_arithmeticTupleCanonicalRegions places tuple).2.image e.continuous

/-- The unit-scaled canonical unit reference has positive finite Haar mass. -/
theorem measure_unit_smul_canonicalUnitReference_pos_lt_top
    (u : (X places tuple)ˣ) :
    0 < μ ((u : X places tuple) •
        arithmeticTupleCanonicalUnitReference places tuple) ∧
      μ ((u : X places tuple) •
        arithmeticTupleCanonicalUnitReference places tuple) < ⊤ := by
  have hopen := isOpen_unit_smul_canonicalUnitReference (p := p) places tuple u
  have hcompact := isCompact_unit_smul_canonicalUnitReference (p := p) places tuple u
  constructor
  · apply hopen.measure_pos μ
    refine ⟨0, ?_⟩
    refine ⟨0, ?_, ?_⟩
    · simpa using (zero_mem_arithmeticTupleCanonicalUnitReference places tuple)
    · simp [smul_eq_mul]
  · exact hcompact.measure_lt_top

end LeanFormal.IUT.XiFPaper.UnitSmulCanonicalUnitReferenceActual

end
