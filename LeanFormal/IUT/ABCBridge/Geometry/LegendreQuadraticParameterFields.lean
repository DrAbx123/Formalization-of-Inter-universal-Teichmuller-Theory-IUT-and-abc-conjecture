import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Tactic

/-!
# Actual quadratic fields for Legendre parameter changes

The fields in this file are actual intermediate fields of `AlgebraicClosure K`.
A chosen square root generates an extension of degree at most two, including
extensions of degree one when the radicand is already a square in `K`.

The compositum of the extensions for `-1`, `λ`, and `1 - λ` contains the three
roots needed by Legendre coordinate changes. Its degree over `K` is at most
eight, and at most four if `-1` is already a square in `K`. For number-field
bases the resulting fields carry actual `NumberField` instances.

These constructions supply scaling elements for later curve isomorphisms;
they do not assert that equal j-invariants imply an isomorphism over `K`.
-/

noncomputable section

namespace LeanFormal.IUT.LegendreQuadraticParameterFields

open Polynomial IntermediateField
open scoped IntermediateField

variable (K : Type*) [Field K]

/-- A square root in the actual algebraic closure of the base field. -/
def algebraicSquareRoot (d : K) : AlgebraicClosure K :=
  Classical.choose
    (IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) d)
      (by decide : 0 < (2 : ℕ)))

@[simp]
theorem algebraicSquareRoot_sq (d : K) :
    algebraicSquareRoot K d ^ 2 = algebraMap K (AlgebraicClosure K) d :=
  Classical.choose_spec
    (IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) d)
      (by decide : 0 < (2 : ℕ)))

/-- The chosen square root is a root of the actual quadratic polynomial. -/
theorem algebraicSquareRoot_aeval (d : K) :
    aeval (algebraicSquareRoot K d) (X ^ 2 - C d) = 0 := by
  simp only [map_sub, map_pow, aeval_X, aeval_C]
  exact sub_eq_zero.mpr (algebraicSquareRoot_sq K d)

/-- Integrality is witnessed by `X² - d`, not by a promised field property. -/
theorem algebraicSquareRoot_isIntegral (d : K) :
    IsIntegral K (algebraicSquareRoot K d) :=
  ⟨X ^ 2 - C d, monic_X_pow_sub_C d (by decide), algebraicSquareRoot_aeval K d⟩

/-- The simple field obtained by adjoining a chosen square root of `d`. -/
def squareRootField (d : K) : IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.adjoin K {algebraicSquareRoot K d}

instance squareRootField_finiteDimensional (d : K) :
    FiniteDimensional K (squareRootField K d) :=
  IntermediateField.adjoin.finiteDimensional (algebraicSquareRoot_isIntegral K d)

/-- The actual root element in its simple extension. -/
def squareRoot (d : K) : squareRootField K d :=
  ⟨algebraicSquareRoot K d,
    IntermediateField.mem_adjoin_simple_self K (algebraicSquareRoot K d)⟩

@[simp]
theorem squareRoot_sq (d : K) :
    squareRoot K d ^ 2 = algebraMap K (squareRootField K d) d := by
  apply Subtype.ext
  exact algebraicSquareRoot_sq K d

private theorem ne_zero_of_square_eq_algebraMap
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    {u : E} {d : F} (square_eq : u ^ 2 = algebraMap F E d)
    (radicand_ne_zero : d ≠ 0) : u ≠ 0 := by
  intro root_zero
  have mapped_zero : algebraMap F E d = algebraMap F E 0 := by
    simpa [root_zero] using square_eq.symm
  exact radicand_ne_zero ((algebraMap F E).injective mapped_zero)

/-- Nonzero radicands give invertible scaling elements in the field. -/
theorem squareRoot_ne_zero (d : K) (radicand_ne_zero : d ≠ 0) :
    squareRoot K d ≠ 0 :=
  ne_zero_of_square_eq_algebraMap (squareRoot_sq K d) radicand_ne_zero

/-- The minimal-polynomial argument bounds the simple extension degree by two. -/
theorem squareRootField_finrank_le_two (d : K) :
    Module.finrank K (squareRootField K d) ≤ 2 := by
  change Module.finrank K K⟮algebraicSquareRoot K d⟯ ≤ 2
  rw [IntermediateField.adjoin.finrank (algebraicSquareRoot_isIntegral K d)]
  calc
    (minpoly K (algebraicSquareRoot K d)).natDegree ≤ (X ^ 2 - C d).natDegree :=
      Polynomial.natDegree_le_of_dvd
        (minpoly.dvd K (algebraicSquareRoot K d) (algebraicSquareRoot_aeval K d))
        (monic_X_pow_sub_C d (by decide : (2 : ℕ) ≠ 0)).ne_zero
    _ = 2 := Polynomial.natDegree_X_pow_sub_C

/-- If `d` is a square in `K`, every square root of its image lies in the
base-field image: the two possible roots differ by sign. -/
theorem algebraicSquareRoot_mem_bot_of_isSquare
    (d : K) (square_in_base : ∃ a : K, a ^ 2 = d) :
    algebraicSquareRoot K d ∈ (⊥ : IntermediateField K (AlgebraicClosure K)) := by
  obtain ⟨a, square_eq⟩ := square_in_base
  have equal_squares : algebraicSquareRoot K d ^ 2 =
      (algebraMap K (AlgebraicClosure K) a) ^ 2 := by
    rw [algebraicSquareRoot_sq, ← map_pow, square_eq]
  have product_zero :
      (algebraicSquareRoot K d - algebraMap K (AlgebraicClosure K) a) *
        (algebraicSquareRoot K d + algebraMap K (AlgebraicClosure K) a) = 0 := by
    calc
      _ = algebraicSquareRoot K d ^ 2 -
          (algebraMap K (AlgebraicClosure K) a) ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr equal_squares
  apply IntermediateField.mem_bot.mpr
  rcases mul_eq_zero.mp product_zero with difference_zero | sum_zero
  · exact ⟨a, (sub_eq_zero.mp difference_zero).symm⟩
  · refine ⟨-a, ?_⟩
    rw [map_neg]
    exact (eq_neg_of_add_eq_zero_left sum_zero).symm

/-- Existing squares give the actual bottom intermediate field. -/
theorem squareRootField_eq_bot_of_isSquare
    (d : K) (square_in_base : ∃ a : K, a ^ 2 = d) :
    squareRootField K d = ⊥ := by
  apply IntermediateField.adjoin_eq_bot_iff.mpr
  intro x member
  have element_eq : x = algebraicSquareRoot K d := Set.mem_singleton_iff.mp member
  rw [element_eq]
  exact algebraicSquareRoot_mem_bot_of_isSquare K d square_in_base

/-- The degree is one, rather than two, when the radicand is already a square. -/
theorem squareRootField_finrank_eq_one_of_isSquare
    (d : K) (square_in_base : ∃ a : K, a ^ 2 = d) :
    Module.finrank K (squareRootField K d) = 1 := by
  rw [squareRootField_eq_bot_of_isSquare K d square_in_base]
  exact IntermediateField.finrank_bot

/-- The three simple extensions used in Legendre parameter changes, inside
one fixed algebraic closure. -/
def legendreParameterField (lam : K) : IntermediateField K (AlgebraicClosure K) :=
  (squareRootField K (-1) ⊔ squareRootField K lam) ⊔
    squareRootField K (1 - lam)

instance legendreParameterField_finiteDimensional (lam : K) :
    FiniteDimensional K (legendreParameterField K lam) := by
  unfold legendreParameterField
  infer_instance

/-- Inclusion of the field containing a square root of minus one. -/
theorem squareRootNegOneField_le_legendreParameterField (lam : K) :
    squareRootField K (-1) ≤ legendreParameterField K lam :=
  le_sup_left.trans le_sup_left

/-- Inclusion of the field containing a square root of the Legendre parameter. -/
theorem squareRootParameterField_le_legendreParameterField (lam : K) :
    squareRootField K lam ≤ legendreParameterField K lam :=
  le_sup_right.trans le_sup_left

/-- Inclusion of the field containing a square root of the complementary parameter. -/
theorem squareRootComplementField_le_legendreParameterField (lam : K) :
    squareRootField K (1 - lam) ≤ legendreParameterField K lam :=
  le_sup_right

/-- A square root of minus one in the common Legendre parameter field. -/
def legendreSqrtNegOne (lam : K) : legendreParameterField K lam :=
  ⟨algebraicSquareRoot K (-1),
    squareRootNegOneField_le_legendreParameterField K lam
      (IntermediateField.mem_adjoin_simple_self K (algebraicSquareRoot K (-1)))⟩

/-- A square root of the Legendre parameter in the common field. -/
def legendreSqrtParameter (lam : K) : legendreParameterField K lam :=
  ⟨algebraicSquareRoot K lam,
    squareRootParameterField_le_legendreParameterField K lam
      (IntermediateField.mem_adjoin_simple_self K (algebraicSquareRoot K lam))⟩

/-- A square root of the complementary parameter in the common field. -/
def legendreSqrtComplement (lam : K) : legendreParameterField K lam :=
  ⟨algebraicSquareRoot K (1 - lam),
    squareRootComplementField_le_legendreParameterField K lam
      (IntermediateField.mem_adjoin_simple_self K (algebraicSquareRoot K (1 - lam)))⟩

@[simp]
theorem legendreSqrtNegOne_sq (lam : K) :
    legendreSqrtNegOne K lam ^ 2 = -1 := by
  apply Subtype.ext
  change algebraicSquareRoot K (-1) ^ 2 = (-1 : AlgebraicClosure K)
  simpa only [map_neg, map_one] using algebraicSquareRoot_sq K (-1)

@[simp]
theorem legendreSqrtParameter_sq (lam : K) :
    legendreSqrtParameter K lam ^ 2 = algebraMap K (legendreParameterField K lam) lam := by
  apply Subtype.ext
  exact algebraicSquareRoot_sq K lam

@[simp]
theorem legendreSqrtComplement_sq (lam : K) :
    legendreSqrtComplement K lam ^ 2 =
      1 - algebraMap K (legendreParameterField K lam) lam := by
  apply Subtype.ext
  change algebraicSquareRoot K (1 - lam) ^ 2 =
    1 - algebraMap K (AlgebraicClosure K) lam
  simpa only [map_sub, map_one] using algebraicSquareRoot_sq K (1 - lam)

/-- The minus-one root is always nonzero. -/
theorem legendreSqrtNegOne_ne_zero (lam : K) :
    legendreSqrtNegOne K lam ≠ 0 := by
  apply ne_zero_of_square_eq_algebraMap (d := (-1 : K))
  · simpa only [map_neg, map_one] using legendreSqrtNegOne_sq K lam
  · exact neg_ne_zero.mpr one_ne_zero

/-- The parameter root is nonzero under the actual excluded-value hypothesis. -/
theorem legendreSqrtParameter_ne_zero (lam : K) (parameter_ne_zero : lam ≠ 0) :
    legendreSqrtParameter K lam ≠ 0 :=
  ne_zero_of_square_eq_algebraMap (legendreSqrtParameter_sq K lam) parameter_ne_zero

/-- The complementary root is nonzero when the parameter is not one. -/
theorem legendreSqrtComplement_ne_zero (lam : K) (parameter_ne_one : lam ≠ 1) :
    legendreSqrtComplement K lam ≠ 0 := by
  apply ne_zero_of_square_eq_algebraMap (d := 1 - lam)
  · simpa only [map_sub, map_one] using legendreSqrtComplement_sq K lam
  · exact sub_ne_zero.mpr (Ne.symm parameter_ne_one)

/-- The unit scaling by a square root of minus one, as used by coordinate
changes of Weierstrass equations. -/
def legendreNegOneUnit (lam : K) : (legendreParameterField K lam)ˣ :=
  Units.mk0 (legendreSqrtNegOne K lam) (legendreSqrtNegOne_ne_zero K lam)

/-- The unit scaling by a square root of the nonzero parameter. -/
def legendreParameterUnit (lam : K) (parameter_ne_zero : lam ≠ 0) :
    (legendreParameterField K lam)ˣ :=
  Units.mk0 (legendreSqrtParameter K lam)
    (legendreSqrtParameter_ne_zero K lam parameter_ne_zero)

/-- The unit scaling by a square root of the nonzero complementary parameter. -/
def legendreComplementUnit (lam : K) (parameter_ne_one : lam ≠ 1) :
    (legendreParameterField K lam)ˣ :=
  Units.mk0 (legendreSqrtComplement K lam)
    (legendreSqrtComplement_ne_zero K lam parameter_ne_one)

/-- Three quadratic generators give an extension of degree at most eight. -/
theorem legendreParameterField_finrank_le_eight (lam : K) :
    Module.finrank K (legendreParameterField K lam) ≤ 8 := by
  calc
    Module.finrank K (legendreParameterField K lam) ≤
        Module.finrank K ↑(squareRootField K (-1) ⊔ squareRootField K lam) *
          Module.finrank K (squareRootField K (1 - lam)) :=
      IntermediateField.finrank_sup_le _ _
    _ ≤ (Module.finrank K (squareRootField K (-1)) *
          Module.finrank K (squareRootField K lam)) *
          Module.finrank K (squareRootField K (1 - lam)) :=
      Nat.mul_le_mul_right _ (IntermediateField.finrank_sup_le _ _)
    _ ≤ (2 * 2) * 2 :=
      Nat.mul_le_mul
        (Nat.mul_le_mul (squareRootField_finrank_le_two K (-1))
          (squareRootField_finrank_le_two K lam))
        (squareRootField_finrank_le_two K (1 - lam))
    _ = 8 := by decide

/-- If minus one is already a square, the same field needs at most two
nontrivial quadratic adjunctions. -/
theorem legendreParameterField_finrank_le_four
    (lam : K) (sqrt_neg_one_in_base : ∃ i : K, i ^ 2 = -1) :
    Module.finrank K (legendreParameterField K lam) ≤ 4 := by
  unfold legendreParameterField
  rw [squareRootField_eq_bot_of_isSquare K (-1) sqrt_neg_one_in_base, bot_sup_eq]
  exact (IntermediateField.finrank_sup_le _ _).trans
    (by
      simpa using Nat.mul_le_mul (squareRootField_finrank_le_two K lam)
        (squareRootField_finrank_le_two K (1 - lam)))

section NumberFields

variable [NumberField K]

/-- A simple square-root extension of a number field is a number field. -/
instance squareRootField_numberField (d : K) : NumberField (squareRootField K d) := by
  letI : FiniteDimensional ℚ (squareRootField K d) :=
    FiniteDimensional.trans ℚ K (squareRootField K d)
  exact NumberField.mk

/-- The common field for the Legendre coordinate scalings is a number field. -/
instance legendreParameterField_numberField (lam : K) :
    NumberField (legendreParameterField K lam) := by
  letI : FiniteDimensional ℚ (legendreParameterField K lam) :=
    FiniteDimensional.trans ℚ K (legendreParameterField K lam)
  exact NumberField.mk

/-- The absolute degree of the common parameter field is bounded explicitly. -/
theorem legendreParameterField_absolute_finrank_le
    (lam : K) : Module.finrank ℚ (legendreParameterField K lam) ≤
      Module.finrank ℚ K * 8 := by
  rw [← Module.finrank_mul_finrank ℚ K (legendreParameterField K lam)]
  exact Nat.mul_le_mul_left _ (legendreParameterField_finrank_le_eight K lam)

/-- The improved absolute-degree bound when the base contains a square root
of minus one. -/
theorem legendreParameterField_absolute_finrank_le_of_sqrt_neg_one
    (lam : K) (sqrt_neg_one_in_base : ∃ i : K, i ^ 2 = -1) :
    Module.finrank ℚ (legendreParameterField K lam) ≤ Module.finrank ℚ K * 4 := by
  rw [← Module.finrank_mul_finrank ℚ K (legendreParameterField K lam)]
  exact Nat.mul_le_mul_left _
    (legendreParameterField_finrank_le_four K lam sqrt_neg_one_in_base)

/-- The actual field needed for the Frey scaling equation `u² = -c`. -/
def freyScalingField (c : ℤ) : IntermediateField K (AlgebraicClosure K) :=
  squareRootField K (-(c : K))

instance freyScalingField_finiteDimensional (c : ℤ) :
    FiniteDimensional K (freyScalingField K c) :=
  squareRootField_finiteDimensional K (-(c : K))

instance freyScalingField_numberField (c : ℤ) : NumberField (freyScalingField K c) :=
  squareRootField_numberField K (-(c : K))

/-- The chosen scaling element belongs to the actual finite extension. -/
def freyScalingRoot (c : ℤ) : freyScalingField K c :=
  squareRoot K (-(c : K))

@[simp]
theorem freyScalingRoot_sq (c : ℤ) :
    freyScalingRoot K c ^ 2 = -(c : freyScalingField K c) := by
  apply Subtype.ext
  change algebraicSquareRoot K (-(c : K)) ^ 2 = -(c : AlgebraicClosure K)
  simpa only [map_neg, map_intCast] using algebraicSquareRoot_sq K (-(c : K))

/-- Nonzero integer `c` supplies a nonzero Frey scaling element; this uses
characteristic zero of the number field explicitly through the integer cast. -/
theorem freyScalingRoot_ne_zero (c : ℤ) (coefficient_ne_zero : c ≠ 0) :
    freyScalingRoot K c ≠ 0 := by
  apply squareRoot_ne_zero K (-(c : K))
  apply neg_ne_zero.mpr
  exact_mod_cast coefficient_ne_zero

/-- The actual invertible coordinate scale for the Frey variable change. -/
def freyScalingUnit (c : ℤ) (coefficient_ne_zero : c ≠ 0) :
    (freyScalingField K c)ˣ :=
  Units.mk0 (freyScalingRoot K c) (freyScalingRoot_ne_zero K c coefficient_ne_zero)

set_option linter.unusedSectionVars false

/-- Frey scaling requires extension degree at most two. -/
theorem freyScalingField_finrank_le_two (c : ℤ) :
    Module.finrank K (freyScalingField K c) ≤ 2 :=
  squareRootField_finrank_le_two K (-(c : K))

/-- If the Frey scaling factor already has a square root in the base field,
this construction has degree one. -/
theorem freyScalingField_finrank_eq_one
    (c : ℤ) (scaling_in_base : ∃ u : K, u ^ 2 = -(c : K)) :
    Module.finrank K (freyScalingField K c) = 1 :=
  squareRootField_finrank_eq_one_of_isSquare K (-(c : K)) scaling_in_base

end NumberFields

end LeanFormal.IUT.LegendreQuadraticParameterFields
