/- U-R C2 (P) generic pure-generator lemmas (kurt), default heartbeats.

The pure generator of a value-group scaling datum is a unit of the tensor block;
hence its translate of the canonical unit reference is open, has positive and
finite Haar mass.  Stated generically over the actual places/tuple so that the
concrete K-side/F-side adapters only instantiate.

NO set_option maxHeartbeats here (Lead ruling (ii): generic abstraction, default
budget).
-/
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompactHullScaling
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped Pointwise

namespace LeanFormal.IUT.NumberFieldFinitePlace

open MeasureTheory
open LeanFormal.IUT.LocalFieldLogarithm

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w} [∀ i, Fintype (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]

/-- The pure generator of a scaling datum is a unit of the tensor block. -/
theorem isUnit_pureGenerator {c : ι → ℝ}
    (data : ArithmeticTuplePureFractionalScalingData places tuple c) :
    IsUnit (arithmeticTupleFractionalPureGenerator places tuple data.localGenerator) :=
  ⟨arithmeticTupleFractionalGeneratorUnit places tuple data,
    arithmeticTupleFractionalGeneratorUnit_coe places tuple data⟩

/-- The pure generator is the coercion of the generator unit. -/
theorem pureGenerator_eq_coe_unit {c : ι → ℝ}
    (data : ArithmeticTuplePureFractionalScalingData places tuple c) :
    arithmeticTupleFractionalPureGenerator places tuple data.localGenerator =
      (↑(arithmeticTupleFractionalGeneratorUnit places tuple data) :
        ArithmeticTensorTupleBlock places tuple) :=
  (arithmeticTupleFractionalGeneratorUnit_coe places tuple data).symm

/-- The pure-generator translate is open: it is the image of the open unit
reference under left multiplication by a block unit. -/
theorem isOpen_smul_pureGenerator {c : ι → ℝ}
    (data : ArithmeticTuplePureFractionalScalingData places tuple c) :
    IsOpen (arithmeticTupleFractionalPureGenerator places tuple data.localGenerator •
      arithmeticTupleCanonicalUnitReference places tuple) := by
  rw [pureGenerator_eq_coe_unit places tuple data]
  let u : (ArithmeticTensorTupleBlock places tuple)ˣ :=
    arithmeticTupleFractionalGeneratorUnit places tuple data
  let e : ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
      ArithmeticTensorTupleBlock places tuple :=
    u.mulLeftLinearEquiv ℚ_[p] (ArithmeticTensorTupleBlock places tuple)
  have hmap : (↑u : ArithmeticTensorTupleBlock places tuple) •
      arithmeticTupleCanonicalUnitReference places tuple =
      e '' arithmeticTupleCanonicalUnitReference places tuple := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  rw [hmap]
  exact e.toContinuousLinearEquiv.toHomeomorph.isOpenMap _
    (isOpen_arithmeticTupleCanonicalUnitReference places tuple)

/-- The pure-generator translate has positive Haar mass. -/
theorem measure_pos_smul_pureGenerator {c : ι → ℝ}
    (data : ArithmeticTuplePureFractionalScalingData places tuple c)
    (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [Measure.IsAddHaarMeasure μ] :
    0 < μ (arithmeticTupleFractionalPureGenerator places tuple data.localGenerator •
      arithmeticTupleCanonicalUnitReference places tuple) := by
  rw [pureGenerator_eq_coe_unit places tuple data]
  let u : (ArithmeticTensorTupleBlock places tuple)ˣ :=
    arithmeticTupleFractionalGeneratorUnit places tuple data
  let e : ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
      ArithmeticTensorTupleBlock places tuple :=
    u.mulLeftLinearEquiv ℚ_[p] (ArithmeticTensorTupleBlock places tuple)
  have hmap : (↑u : ArithmeticTensorTupleBlock places tuple) •
      arithmeticTupleCanonicalUnitReference places tuple =
      e '' arithmeticTupleCanonicalUnitReference places tuple := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  rw [hmap]
  exact (e.toContinuousLinearEquiv.toHomeomorph.isOpenMap _
      (isOpen_arithmeticTupleCanonicalUnitReference places tuple)).measure_pos μ
    ⟨e 0, ⟨0, zero_mem_arithmeticTupleCanonicalUnitReference places tuple, rfl⟩⟩


/-- The pure-generator translate is compact (image of the compact unit reference). -/
theorem isCompact_smul_pureGenerator {c : ι → ℝ}
    (data : ArithmeticTuplePureFractionalScalingData places tuple c) :
    IsCompact (arithmeticTupleFractionalPureGenerator places tuple data.localGenerator •
      arithmeticTupleCanonicalUnitReference places tuple) := by
  rw [pureGenerator_eq_coe_unit places tuple data]
  let u : (ArithmeticTensorTupleBlock places tuple)ˣ :=
    arithmeticTupleFractionalGeneratorUnit places tuple data
  let e : ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
      ArithmeticTensorTupleBlock places tuple :=
    u.mulLeftLinearEquiv ℚ_[p] (ArithmeticTensorTupleBlock places tuple)
  have hmap : (↑u : ArithmeticTensorTupleBlock places tuple) •
      arithmeticTupleCanonicalUnitReference places tuple =
      e '' arithmeticTupleCanonicalUnitReference places tuple := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  rw [hmap]
  exact (isCompact_arithmeticTupleCanonicalRegions places tuple).2.image
    e.toContinuousLinearEquiv.continuous

/-- The pure-generator translate has finite Haar mass. -/
theorem measure_lt_top_smul_pureGenerator {c : ι → ℝ}
    (data : ArithmeticTuplePureFractionalScalingData places tuple c)
    (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [Measure.IsAddHaarMeasure μ] :
    μ (arithmeticTupleFractionalPureGenerator places tuple data.localGenerator •
      arithmeticTupleCanonicalUnitReference places tuple) < ⊤ :=
  (isCompact_smul_pureGenerator places tuple data).measure_lt_top

#print axioms isCompact_smul_pureGenerator
#print axioms measure_lt_top_smul_pureGenerator



#print axioms isUnit_pureGenerator
#print axioms isOpen_smul_pureGenerator
#print axioms measure_pos_smul_pureGenerator
#print axioms isCompact_smul_pureGenerator
#print axioms measure_lt_top_smul_pureGenerator

end LeanFormal.IUT.NumberFieldFinitePlace
end
