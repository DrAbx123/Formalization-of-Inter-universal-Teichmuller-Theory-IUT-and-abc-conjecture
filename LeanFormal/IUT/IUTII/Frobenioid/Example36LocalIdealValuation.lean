import LeanFormal.IUT.IUTII.Frobenioid.Example36LocalValueData
import LeanFormal.IUT.IUTII.Frobenioid.FinitePlaceFractionalIdealUnitQuotient
import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# The local ideal-value bridge at an actual finite place (IUT III, Example 3.6)

This module proves, at an actual finite place, that the value-group model of
Example 3.6 is faithfully realized by the fractional ideals of the local
completion.

Setup: `R` is a Dedekind domain, `K` its fraction field, and
`v : HeightOneSpectrum R` a height-one prime.  The local field is the actual
`v`-adic completion `v.adicCompletion K` of `K` (Mathlib
`IsDedekindDomain.HeightOneSpectrum.adicCompletion`), whose valuation
`Valued.v` takes values in `ℤᵐ⁰ = WithZero (Multiplicative ℤ)`.

## Two signs of the same integer valuation

Mathlib's adic value of a uniformizer is `WithZero.exp (-1)`, i.e. the
valuation value is `exp(-ν)` where `ν` is the classical additive valuation.
The units of the completion therefore carry two descriptions of the same
integer:

* `completionValuationAdd`, the logarithm form
  `Multiplicative.toAdd (WithZero.unzero (Valued.v x))`: this is exactly
  `WithZero.log (Valued.v x)`, and it is the additive integer valuation
  directly obtained from Mathlib's valuation.  Mathematically it is `-ν`.
  It is a monoid homomorphism into `Multiplicative ℤ`.
* `completionValuationExponent`, the classical exponent
  `ν = -completionValuationAdd`.  This is the coordinate in which the integral
  elements are nonnegative, i.e. the `integerNonnegCone` of
  `Example36LocalValueData.lean` is the correct cone, and it matches the
  Layer-1 finite rational model `rationalFiniteLocalData` whose principal map
  is `padicValRat`.  It is again a monoid homomorphism into
  `Multiplicative ℤ`.

Both are additive integer valuations; they differ by the sign that converts
"order-reversing value" to "order-preserving exponent".  The lemmas below are
stated for both, so that consumers can use either convention without redoing
the arithmetic.

## Main results

* `completionPrincipalIdeal_le_iff_valuationAdd_le`: for units `x y` of the
  completion, the actual fractional-ideal inclusion `(x) ≤ (y)` holds exactly
  when `completionValuationAdd x ≤ completionValuationAdd y`.  The exponent
  form is `completionPrincipalIdeal_le_iff_valuationExponent_ge`:
  `(x) ≤ (y) ↔ exponent y ≤ exponent x`.
* `completionPrincipalIdeal_mul_pow_le_iff_valuationExponent`: the
  positive-degree local morphism condition of Example 3.6,
  `(f) * (x)^n ≤ (y)`, holds exactly when
  `0 ≤ exponent f + n * exponent x - exponent y`.  Its log-value form is
  `completionPrincipalIdeal_mul_pow_le_iff_valuationAdd`:
  `valuationAdd f + n * valuationAdd x - valuationAdd y ≤ 0`.
* `completionLocalValueData`: the unified `LocalValueData` of
  `Example36LocalValueData.lean` at the completion, with value group `ℤ`,
  integral cone `integerNonnegCone`, and principal map the exponent monoid
  homomorphism.
* `completionLocalInclusion_iff_principalIdeal_mul_pow_le`: for this actual
  data, the abstract `localInclusion` condition is equivalent to the actual
  local ideal inclusion `(f) * (x)^n ≤ (y)`, i.e. the value model is faithful
  at this finite place.
* `completionValuationExponent_eq_zero_iff_mem_integralUnits`: the kernel of
  the exponent is exactly the integral units of the completion, and
  `completionValuationExponent_surjective` shows the value group is all of
  `ℤ`.
* `completionValuationAdd_coe` / `completionValuationExponent_coe`: on units
  coming from `Kˣ`, the completion valuation agrees with the global adic
  valuation `v.valuation K`.

All statements are about a single finite place.  Nothing here constructs the
global ideal-family category, archimedean places, Frobenioids, or Hodge
theaters; the global layer consumes these lemmas place by place.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open IsDedekindDomain
open LeanFormal.IUT.FinitePlaceFractionalIdealUnitQuotient
open LeanFormal.IUT.LocalFractionalIdealUnitQuotient
open scoped WithZero
open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K]
  [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

/-! ## 1. The additive integer valuation on the completion units -/

/-- The completion valuation of a unit of `v.adicCompletion K` is nonzero.

This is the field-level form of `Valuation.ne_zero_iff`: a unit of the local
field is nonzero, so its valuation is not zero. -/
theorem completionValuation_ne_zero (x : (v.adicCompletion K)ˣ) :
    Valued.v (x : v.adicCompletion K) ≠ 0 :=
  (Valuation.ne_zero_iff (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)).2
    (Units.ne_zero x)

/-- The additive integer valuation on the units of the `v`-adic completion,
i.e. the logarithm form of the local value-group coordinate of Example 3.6 at
the finite place `v`.

The value `Valued.v x` lies in `ℤᵐ⁰`; for a unit it is nonzero, so
`WithZero.unzero` produces an element of `Multiplicative ℤ`, and
`Multiplicative.toAdd` reads off the integer exponent. -/
def completionValuationAdd (x : (v.adicCompletion K)ˣ) : ℤ :=
  Multiplicative.toAdd (WithZero.unzero (completionValuation_ne_zero v x))

/-- The additive integer valuation is the logarithm of the completion
valuation value (`WithZero.log` is the junkless-at-zero inverse of
`WithZero.exp`; on nonzero values it is exactly `unzero` followed by
`Multiplicative.toAdd`). -/
theorem completionValuationAdd_eq_log (x : (v.adicCompletion K)ˣ) :
    completionValuationAdd v x =
      WithZero.log (Valued.v (x : v.adicCompletion K)) := by
  apply WithZero.exp_inj.mp
  rw [WithZero.exp_log (completionValuation_ne_zero v x)]
  exact WithZero.coe_unzero (completionValuation_ne_zero v x)

/-- The additive integer valuation of the unit `1` is `0`. -/
@[simp]
theorem completionValuationAdd_one :
    completionValuationAdd v (1 : (v.adicCompletion K)ˣ) = 0 := by
  rw [completionValuationAdd_eq_log]
  simp

/-- The additive integer valuation is additive on products of units. -/
theorem completionValuationAdd_mul (x y : (v.adicCompletion K)ˣ) :
    completionValuationAdd v (x * y) =
      completionValuationAdd v x + completionValuationAdd v y := by
  rw [completionValuationAdd_eq_log, completionValuationAdd_eq_log,
    completionValuationAdd_eq_log]
  rw [Units.val_mul, map_mul,
    WithZero.log_mul (completionValuation_ne_zero v x)
      (completionValuation_ne_zero v y)]

/-- The additive integer valuation of a natural power is the natural multiple
of the valuation. -/
theorem completionValuationAdd_pow (x : (v.adicCompletion K)ˣ) (n : ℕ) :
    completionValuationAdd v (x ^ n) = (n : ℤ) * completionValuationAdd v x := by
  rw [completionValuationAdd_eq_log, completionValuationAdd_eq_log]
  rw [Units.val_pow_eq_pow_val, map_pow, WithZero.log_pow]
  exact nsmul_eq_mul n (WithZero.log (Valued.v (x : v.adicCompletion K)))

/-- The additive integer valuation as a monoid homomorphism from the unit
group of the completion to the additive group `ℤ` in multiplicative
notation.  This is the local principal map `δ_v` of Example 3.6 in the
logarithm form of the value group `Gamma_v = ℤ`. -/
def completionValuationMonoidHom :
    (v.adicCompletion K)ˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (completionValuationAdd v x)
  map_one' := by
    change Multiplicative.ofAdd (completionValuationAdd v 1) = 1
    rw [completionValuationAdd_one, ofAdd_zero]
  map_mul' := by
    intro x y
    change Multiplicative.ofAdd (completionValuationAdd v (x * y)) =
      Multiplicative.ofAdd (completionValuationAdd v x) *
        Multiplicative.ofAdd (completionValuationAdd v y)
    rw [completionValuationAdd_mul, ofAdd_add]

/-- The monoid homomorphism underlying the additive integer valuation, applied
to a unit. -/
@[simp]
theorem completionValuationMonoidHom_apply (x : (v.adicCompletion K)ˣ) :
    completionValuationMonoidHom v x =
      Multiplicative.ofAdd (completionValuationAdd v x) :=
  rfl

/-! ## 2. The classical exponent (the value-model coordinate)

The classical additive valuation `ν` of the completion is the negative of the
logarithm form: for a uniformizer `π`, Mathlib's value is `exp(-1)`, whose
logarithm is `-1`, while the classical valuation is `+1`.  The integral
elements are exactly those with `Valued.v x ≤ 1`, i.e. `ν x ≥ 0`; this is the
coordinate used by `integerNonnegCone` in the Layer-1 finite rational model. -/

/-- The classical additive integer valuation `ν` of a unit of the completion,
i.e. the negative of the logarithm form `completionValuationAdd`.

It is positive on a uniformizer and nonnegative exactly on the integral
elements, so it is the coordinate of the value-group model of Example 3.6
fitted to the integral cone `integerNonnegCone`. -/
def completionValuationExponent (x : (v.adicCompletion K)ˣ) : ℤ :=
  -completionValuationAdd v x

/-- The exponent is the negative of the logarithm form. -/
theorem completionValuationExponent_eq_neg (x : (v.adicCompletion K)ˣ) :
    completionValuationExponent v x = -completionValuationAdd v x :=
  rfl

/-- The exponent is the negative of the logarithm of the completion valuation
value. -/
theorem completionValuationExponent_eq_neg_log (x : (v.adicCompletion K)ˣ) :
    completionValuationExponent v x =
      -WithZero.log (Valued.v (x : v.adicCompletion K)) := by
  rw [completionValuationExponent_eq_neg, completionValuationAdd_eq_log]

/-- The logarithm of a nonzero completion value is the negative of the
exponent (the inverse of `completionValuationExponent_eq_neg_log`). -/
theorem neg_log_eq_completionValuationExponent (x : (v.adicCompletion K)ˣ) :
    -WithZero.log (Valued.v (x : v.adicCompletion K)) =
      completionValuationExponent v x :=
  (completionValuationExponent_eq_neg_log v x).symm

/-- The exponent of the unit `1` is `0`. -/
@[simp]
theorem completionValuationExponent_one :
    completionValuationExponent v (1 : (v.adicCompletion K)ˣ) = 0 := by
  simp [completionValuationExponent]

/-- The exponent is additive on products of units. -/
theorem completionValuationExponent_mul (x y : (v.adicCompletion K)ˣ) :
    completionValuationExponent v (x * y) =
      completionValuationExponent v x + completionValuationExponent v y := by
  rw [completionValuationExponent_eq_neg, completionValuationAdd_mul,
    completionValuationExponent_eq_neg, completionValuationExponent_eq_neg]
  ring

/-- The exponent of a natural power is the natural multiple of the exponent. -/
theorem completionValuationExponent_pow (x : (v.adicCompletion K)ˣ) (n : ℕ) :
    completionValuationExponent v (x ^ n) =
      (n : ℤ) * completionValuationExponent v x := by
  rw [completionValuationExponent_eq_neg, completionValuationAdd_pow,
    completionValuationExponent_eq_neg]
  ring

/-- The exponent of an inverse is the negative of the exponent. -/
theorem completionValuationExponent_inv (x : (v.adicCompletion K)ˣ) :
    completionValuationExponent v x⁻¹ = -completionValuationExponent v x := by
  have hmul := completionValuationExponent_mul v x⁻¹ x
  rw [inv_mul_cancel, completionValuationExponent_one] at hmul
  linarith

/-- The exponent of a quotient is the difference of the exponents. -/
theorem completionValuationExponent_div (x y : (v.adicCompletion K)ˣ) :
    completionValuationExponent v (x / y) =
      completionValuationExponent v x - completionValuationExponent v y := by
  rw [div_eq_mul_inv, completionValuationExponent_mul, completionValuationExponent_inv]
  ring

/-- The classical exponent as a monoid homomorphism from the unit group of the
completion to the additive group `ℤ` in multiplicative notation.  This is the
local principal map `δ_v` of Example 3.6 in the value coordinate that matches
the integral cone `integerNonnegCone`. -/
def completionValuationExponentMonoidHom :
    (v.adicCompletion K)ˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (completionValuationExponent v x)
  map_one' := by
    change Multiplicative.ofAdd (completionValuationExponent v 1) = 1
    rw [completionValuationExponent_one, ofAdd_zero]
  map_mul' := by
    intro x y
    change Multiplicative.ofAdd (completionValuationExponent v (x * y)) =
      Multiplicative.ofAdd (completionValuationExponent v x) *
        Multiplicative.ofAdd (completionValuationExponent v y)
    rw [completionValuationExponent_mul, ofAdd_add]

/-- The monoid homomorphism underlying the classical exponent, applied to a
unit. -/
@[simp]
theorem completionValuationExponentMonoidHom_apply (x : (v.adicCompletion K)ˣ) :
    completionValuationExponentMonoidHom v x =
      Multiplicative.ofAdd (completionValuationExponent v x) :=
  rfl

/-! ## 3. Faithfulness: actual ideal inclusion iff value inequality -/

/-- Membership in the range of the structure map of the local integer ring is
exactly the integrality bound `Valued.v z ≤ 1` on the completion valuation
(the range is the local ring of integers as a subset). -/
theorem mem_algebraMap_range_iff_valuation_le_one (z : v.adicCompletion K) :
    z ∈ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)).range ↔
      Valued.v z ≤ 1 := by
  constructor
  · rintro ⟨r, rfl⟩
    exact r.property
  · intro hz
    exact ⟨⟨z, hz⟩, rfl⟩

/-- **The value model is faithful at the finite place (logarithm form).**  For
units `x` and `y` of the `v`-adic completion, the actual fractional-ideal
inclusion `(x) ≤ (y)` holds exactly when the additive integer valuations
satisfy `completionValuationAdd x ≤ completionValuationAdd y`.

The ideal side is the already-proved local dictionary
`completionPrincipalIdeal_le_iff_valuation` (ideal inclusion iff
`Valued.v (x / y) ≤ 1`); the remaining step is the order translation
`Valued.v x ≤ Valued.v y ⟺ log-value x ≤ log-value y`, via
`WithZero.exp_le_exp` on the nonzero valuation values. -/
theorem completionPrincipalIdeal_le_iff_valuationAdd_le
    (x y : (v.adicCompletion K)ˣ) :
    (toPrincipalIdeal (v.adicCompletionIntegers K) (v.adicCompletion K) x :
        FractionalIdeal (v.adicCompletionIntegers K)⁰ (v.adicCompletion K)) ≤
      (toPrincipalIdeal (v.adicCompletionIntegers K) (v.adicCompletion K) y :
        FractionalIdeal (v.adicCompletionIntegers K)⁰ (v.adicCompletion K)) ↔
      completionValuationAdd v x ≤ completionValuationAdd v y := by
  rw [completionPrincipalIdeal_le_iff_valuation]
  rw [Valuation.map_div]
  have hy_pos : 0 < Valued.v (y : v.adicCompletion K) := by
    rw [← WithZero.coe_unzero (completionValuation_ne_zero v y)]
    exact WithZero.zero_lt_coe _
  rw [div_le_one₀ hy_pos]
  rw [← WithZero.exp_log (completionValuation_ne_zero v x),
    ← WithZero.exp_log (completionValuation_ne_zero v y), WithZero.exp_le_exp]
  rw [completionValuationAdd_eq_log, completionValuationAdd_eq_log]

/-- **The value model is faithful at the finite place (exponent form).**  For
units `x` and `y` of the completion, the actual fractional-ideal inclusion
`(x) ≤ (y)` holds exactly when the classical exponents satisfy
`exponent y ≤ exponent x` (the order reversal is the sign between the two
conventions). -/
theorem completionPrincipalIdeal_le_iff_valuationExponent_ge
    (x y : (v.adicCompletion K)ˣ) :
    (toPrincipalIdeal (v.adicCompletionIntegers K) (v.adicCompletion K) x :
        FractionalIdeal (v.adicCompletionIntegers K)⁰ (v.adicCompletion K)) ≤
      (toPrincipalIdeal (v.adicCompletionIntegers K) (v.adicCompletion K) y :
        FractionalIdeal (v.adicCompletionIntegers K)⁰ (v.adicCompletion K)) ↔
      completionValuationExponent v y ≤ completionValuationExponent v x := by
  rw [completionPrincipalIdeal_le_iff_valuationAdd_le]
  rw [completionValuationExponent_eq_neg, completionValuationExponent_eq_neg]
  constructor <;> intro h <;> linarith

/-! ## 4. The positive-degree local morphism condition -/

/-- The integrality bound `Valued.v x ≤ 1` of a unit is exactly the
nonnegativity of its classical exponent.  This is the bridge between Mathlib's
multiplicative value group and the integer cone. -/
theorem valuation_le_one_iff_zero_le_exponent (x : (v.adicCompletion K)ˣ) :
    Valued.v (x : v.adicCompletion K) ≤ 1 ↔
      0 ≤ completionValuationExponent v x := by
  have hx := completionValuation_ne_zero v x
  rw [← WithZero.exp_log hx, ← WithZero.exp_zero, WithZero.exp_le_exp]
  rw [completionValuationExponent_eq_neg, completionValuationAdd_eq_log]
  constructor <;> intro h <;> linarith

/-- **The local morphism condition of Example 3.6 in exponent form.**  For
units `f, x, y` of the completion and `n : ℕ`, the actual ideal inclusion
`(f) * (x)^n ≤ (y)` holds exactly when
`0 ≤ exponent f + n * exponent x - exponent y`.

This is the local condition consumed by the global ideal-family Hom
conditions: the principal part `f`, the `n`-th power of the source value,
and the target value are compared through the integer valuation. -/
theorem completionPrincipalIdeal_mul_pow_le_iff_valuationExponent
    (f x y : (v.adicCompletion K)ˣ) (n : ℕ) :
    (toPrincipalIdeal (v.adicCompletionIntegers K) (v.adicCompletion K) f :
        FractionalIdeal (v.adicCompletionIntegers K)⁰ (v.adicCompletion K)) *
        ((toPrincipalIdeal (v.adicCompletionIntegers K) (v.adicCompletion K) x :
          FractionalIdeal (v.adicCompletionIntegers K)⁰ (v.adicCompletion K)) ^ n) ≤
      (toPrincipalIdeal (v.adicCompletionIntegers K) (v.adicCompletion K) y :
        FractionalIdeal (v.adicCompletionIntegers K)⁰ (v.adicCompletion K)) ↔
      0 ≤ completionValuationExponent v f + (n : ℤ) * completionValuationExponent v x -
        completionValuationExponent v y := by
  have hleft :
      (toPrincipalIdeal (v.adicCompletionIntegers K) (v.adicCompletion K) f :
          FractionalIdeal (v.adicCompletionIntegers K)⁰ (v.adicCompletion K)) *
          ((toPrincipalIdeal (v.adicCompletionIntegers K) (v.adicCompletion K) x :
            FractionalIdeal (v.adicCompletionIntegers K)⁰ (v.adicCompletion K)) ^ n) =
        (toPrincipalIdeal (v.adicCompletionIntegers K) (v.adicCompletion K)
            (f * x ^ n) :
          FractionalIdeal (v.adicCompletionIntegers K)⁰ (v.adicCompletion K)) := by
    rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, map_mul, map_pow]
  rw [hleft]
  rw [principalIdeal_le_iff_div_mem_integralImage,
    mem_algebraMap_range_iff_valuation_le_one]
  have hval :
      Valued.v (((f * x ^ n : (v.adicCompletion K)ˣ) : v.adicCompletion K) /
          (y : v.adicCompletion K)) =
        Valued.v (f : v.adicCompletion K) *
            (Valued.v (x : v.adicCompletion K)) ^ n /
          Valued.v (y : v.adicCompletion K) := by
    rw [Valuation.map_div, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
  rw [hval]
  have hy_pos : 0 < Valued.v (y : v.adicCompletion K) := by
    rw [← WithZero.coe_unzero (completionValuation_ne_zero v y)]
    exact WithZero.zero_lt_coe _
  rw [div_le_one₀ hy_pos]
  have hprod_ne :
      Valued.v (f : v.adicCompletion K) *
          (Valued.v (x : v.adicCompletion K)) ^ n ≠ 0 :=
    mul_ne_zero (completionValuation_ne_zero v f)
      (pow_ne_zero n (completionValuation_ne_zero v x))
  rw [← WithZero.exp_log hprod_ne,
    ← WithZero.exp_log (completionValuation_ne_zero v y), WithZero.exp_le_exp]
  rw [WithZero.log_mul (completionValuation_ne_zero v f)
      (pow_ne_zero n (completionValuation_ne_zero v x)),
    WithZero.log_pow]
  rw [completionValuationExponent_eq_neg, completionValuationExponent_eq_neg,
    completionValuationExponent_eq_neg]
  rw [completionValuationAdd_eq_log, completionValuationAdd_eq_log,
    completionValuationAdd_eq_log]
  rw [nsmul_eq_mul]
  constructor <;> intro h <;> linarith

/-- **The local morphism condition of Example 3.6 in logarithm form.**  For
units `f, x, y` of the completion and `n : ℕ`, the actual ideal inclusion
`(f) * (x)^n ≤ (y)` holds exactly when
`valuationAdd f + n * valuationAdd x - valuationAdd y ≤ 0`.

This is the sign conjugate of
`completionPrincipalIdeal_mul_pow_le_iff_valuationExponent`, stated for
consumers working with the logarithm form of Mathlib's valuation. -/
theorem completionPrincipalIdeal_mul_pow_le_iff_valuationAdd
    (f x y : (v.adicCompletion K)ˣ) (n : ℕ) :
    (toPrincipalIdeal (v.adicCompletionIntegers K) (v.adicCompletion K) f :
        FractionalIdeal (v.adicCompletionIntegers K)⁰ (v.adicCompletion K)) *
        ((toPrincipalIdeal (v.adicCompletionIntegers K) (v.adicCompletion K) x :
          FractionalIdeal (v.adicCompletionIntegers K)⁰ (v.adicCompletion K)) ^ n) ≤
      (toPrincipalIdeal (v.adicCompletionIntegers K) (v.adicCompletion K) y :
        FractionalIdeal (v.adicCompletionIntegers K)⁰ (v.adicCompletion K)) ↔
      completionValuationAdd v f + (n : ℤ) * completionValuationAdd v x -
        completionValuationAdd v y ≤ 0 := by
  rw [completionPrincipalIdeal_mul_pow_le_iff_valuationExponent]
  rw [completionValuationExponent_eq_neg, completionValuationExponent_eq_neg,
    completionValuationExponent_eq_neg]
  constructor <;> intro h <;> linarith

/-! ## 5. The value data at the completion reproduces the actual criterion -/

/-- The Layer-1 unified local value data at the actual finite place: value
group `Gamma_v = ℤ`, integral cone the nonnegative integers, and local
principal map the classical integer valuation of the completion. -/
def completionLocalValueData :
    LocalValueData (v.adicCompletion K) ℤ where
  cone := integerNonnegCone
  cone_sharp := by
    intro a ha ha'
    rw [mem_integerNonnegCone] at ha ha'
    omega
  delta := completionValuationExponentMonoidHom v

/-- The additive principal map of the completion value data is the classical
integer valuation. -/
@[simp]
theorem completionLocalValueData_deltaAdd (x : (v.adicCompletion K)ˣ) :
    (completionLocalValueData v).deltaAdd x = completionValuationExponent v x := by
  simp [LocalValueData.deltaAdd, completionLocalValueData,
    completionValuationExponentMonoidHom]

/-- **The value model is faithful at the finite place, in local-inclusion
form.**  For the actual local value data at the completion, the abstract
`localInclusion` condition of Example 3.6,
`exponent f + n * exponent x - exponent y ∈ integerNonnegCone`, is equivalent
to the actual fractional-ideal inclusion `(f) * (x)^n ≤ (y)`. -/
theorem completionLocalInclusion_iff_principalIdeal_mul_pow_le
    (n : ℕ) (f x y : (v.adicCompletion K)ˣ) :
    (completionLocalValueData v).localInclusion n f
        (completionValuationExponent v x) (completionValuationExponent v y) ↔
      (toPrincipalIdeal (v.adicCompletionIntegers K) (v.adicCompletion K) f :
          FractionalIdeal (v.adicCompletionIntegers K)⁰ (v.adicCompletion K)) *
          ((toPrincipalIdeal (v.adicCompletionIntegers K) (v.adicCompletion K) x :
            FractionalIdeal (v.adicCompletionIntegers K)⁰ (v.adicCompletion K)) ^ n) ≤
        (toPrincipalIdeal (v.adicCompletionIntegers K) (v.adicCompletion K) y :
          FractionalIdeal (v.adicCompletionIntegers K)⁰ (v.adicCompletion K)) := by
  rw [completionPrincipalIdeal_mul_pow_le_iff_valuationExponent]
  unfold LocalValueData.localInclusion
  rw [completionLocalValueData_deltaAdd]
  change completionValuationExponent v f + n • completionValuationExponent v x -
      completionValuationExponent v y ∈ integerNonnegCone ↔
    0 ≤ completionValuationExponent v f + (n : ℤ) * completionValuationExponent v x -
      completionValuationExponent v y
  rw [mem_integerNonnegCone, nsmul_eq_mul]

/-! ## 6. Kernel, surjectivity, and compatibility with the global valuation -/

/-- The kernel of the classical exponent is exactly the group of integral
units of the completion: a unit has exponent zero iff its completion value is
one. -/
theorem completionValuationExponent_eq_zero_iff_mem_integralUnits
    (x : (v.adicCompletion K)ˣ) :
    completionValuationExponent v x = 0 ↔
      x ∈ (v.adicCompletionIntegers K).units := by
  have hx := completionValuation_ne_zero v x
  have hlog : completionValuationExponent v x = 0 ↔
      WithZero.log (Valued.v (x : v.adicCompletion K)) = 0 := by
    rw [completionValuationExponent_eq_neg_log]
    constructor <;> intro h <;> linarith
  rw [hlog, ← WithZero.exp_eq_one, WithZero.exp_log hx]
  exact (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one).symm

/-- The classical exponent is surjective onto `ℤ`: every integer is the
value coordinate of some unit of the completion.  This uses the surjectivity of
Mathlib's completion valuation and the logarithmic coordinate. -/
theorem completionValuationExponent_surjective :
    Function.Surjective (completionValuationExponent (K := K) v) := by
  intro n
  obtain ⟨z, hz⟩ :=
    HeightOneSpectrum.valuedAdicCompletion_surjective (K := K) v (WithZero.exp (-n))
  have hz0 : z ≠ 0 := by
    refine (Valuation.ne_zero_iff (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)).1 ?_
    rw [hz]
    exact WithZero.exp_ne_zero
  refine ⟨Units.mk0 z hz0, ?_⟩
  rw [completionValuationExponent_eq_neg_log, Units.val_mk0, hz,
    WithZero.log_exp]
  ring

/-- On units coming from `Kˣ`, the logarithm-form completion valuation is the
logarithm of the global `v`-adic valuation `v.valuation K`. -/
theorem completionValuationAdd_coe (x : Kˣ) :
    completionValuationAdd v
        (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom x) =
      WithZero.log (v.valuation K (x : K)) := by
  rw [completionValuationAdd_eq_log]
  congr 1
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (x : K)

/-- On units coming from `Kˣ`, the classical exponent of the completion is
the negative of the logarithm of the global `v`-adic valuation
`v.valuation K`. -/
theorem completionValuationExponent_coe (x : Kˣ) :
    completionValuationExponent v
        (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom x) =
      -WithZero.log (v.valuation K (x : K)) := by
  rw [completionValuationExponent_eq_neg, completionValuationAdd_coe]

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
