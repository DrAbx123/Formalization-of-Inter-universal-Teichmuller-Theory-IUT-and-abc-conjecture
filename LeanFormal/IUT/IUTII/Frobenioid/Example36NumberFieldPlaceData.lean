import LeanFormal.IUT.IUTII.Frobenioid.Example36GlobalPlaceData
import Mathlib.RingTheory.DedekindDomain.Factorization

set_option linter.unusedSectionVars false

/-!
# The actual number-field place data of IUT III, Example 3.6

This is the arithmetic Layer-2 instantiation of the place-indexed local value data
frozen in `Example36GlobalPlaceData`.  At every finite place of a number field
`F` it uses the genuine `v`-adic valuation
`IsDedekindDomain.HeightOneSpectrum.valuation F v : Valuation F (WithZero (Multiplicative ℤ))`
of Mathlib, and at every archimedean place it uses the genuine absolute value
`w : NumberField.InfinitePlace F`, with additive coordinate `-log (w x)`.

Main contents:

* `finitePlaceValueExponent`: the additive `v`-adic exponent of a global unit,
  obtained from the nonzero `v`-adic valuation by `WithZero.unzero` followed by
  `Multiplicative.toAdd` (this is `WithZero.log`);
* `numberFieldFiniteLocalValueData`: a `LocalValueData F ℤ` with value group `ℤ`,
  integral cone `ℕ` (`integerNonnegCone`), and the `v`-adic exponent as local
  principal map;
* `archimedeanPlaceValue` and `numberFieldInfiniteLocalValueData`: the same at an
  archimedean place, with value group `ℝ`, integral cone `[0, ∞)`
  (`realNonnegCone`), and local principal map `-log (w x)`;
* `numberFieldGlobalPlaceData`: the packaged `GlobalPlaceData F`;
* `numberFieldGlobalPlaceData_hasFiniteSupport`: the arithmetic finite-support
  theorem: a global unit has nonzero `v`-adic exponent at only finitely many
  finite places (proved from the Dedekind fractional-ideal factorization API);
* `principalDivisorFinite` and `principalDivisorInfinite`: the finite-support
  principal divisor and the archimedean principal function of a global unit,
  with their evaluation and additivity laws.

Boundary: this module constructs only the arithmetic local value data and the
principal divisors that the global ideal-family of Example 3.6 consumes.  It does
not construct the global ideal-family category (that is
`Example36GlobalIdealFamily`), a Hodge theater, a prime strip, or any source
identification of an IUT output object.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open IsDedekindDomain NumberField
open scoped NumberField nonZeroDivisors

variable {F : Type*} [Field F] [NumberField F]

/-! ## 1. The finite-place `v`-adic exponent of a global unit -/

/-- The `v`-adic valuation of a global unit at a finite place is nonzero.

This is what allows the multiplicative valuation value in `ℤᵐ⁰` to be
unwrapped to an additive integer exponent. -/
theorem finitePlaceValuation_ne_zero (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    v.valuation F (f : F) ≠ 0 := by
  rw [Valuation.ne_zero_iff]
  exact Units.ne_zero f

/-- The additive `v`-adic exponent of a global unit `f` at the finite place `v`.

This is the classical valuation exponent `ν_v(f)`, i.e. the additive form of the
inverse of the genuine arithmetic valuation `v.valuation F (f : F) :
WithZero (Multiplicative ℤ)`.  Since `f ≠ 0` the value is nonzero; applying
`WithZero.unzero` and `Multiplicative.toAdd` gives the negative of `ν_v(f)`, so
the definition uses `-WithZero.log`.  With this sign, `f` is integral at `v`
(i.e. `f ∈ 𝓞_v`) exactly when `ν_v(f) ≥ 0`, matching the local ideal dictionary
of `Example36LocalIdealValuation`. -/
def finitePlaceValueExponent (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) : ℤ :=
  -WithZero.log (v.valuation F (f : F))

/-- For a nonzero value in the multiplicative additive value group, the logarithm
`WithZero.log` is the additive form of the unzero'd multiplicative element.  This is
the general bridge between the abstract logarithm API and the explicit construction
`WithZero.unzero` followed by `Multiplicative.toAdd`. -/
theorem withZero_log_eq_unzero_toAdd {M : Type*} [AddMonoid M]
    {x : WithZero (Multiplicative M)} (hx : x ≠ 0) :
    WithZero.log x = Multiplicative.toAdd (WithZero.unzero hx) := by
  apply WithZero.exp_injective
  rw [WithZero.exp_log hx, WithZero.exp_eq_coe_ofAdd, ofAdd_toAdd,
    WithZero.coe_unzero hx]

/-- The defining unwrapping of the finite-place exponent through
`WithZero.unzero` and `Multiplicative.toAdd`, with the sign of the classical
valuation exponent. -/
theorem finitePlaceValueExponent_eq_unzero_toAdd (v : HeightOneSpectrum (𝓞 F))
    (f : Fˣ) :
    finitePlaceValueExponent v f =
      -Multiplicative.toAdd (WithZero.unzero (finitePlaceValuation_ne_zero v f)) := by
  rw [finitePlaceValueExponent, withZero_log_eq_unzero_toAdd]

@[simp]
theorem finitePlaceValueExponent_one (v : HeightOneSpectrum (𝓞 F)) :
    finitePlaceValueExponent v (1 : Fˣ) = 0 := by
  simp [finitePlaceValueExponent]

/-- The finite-place exponent is additive: this is the local multiplicativity of
the `v`-adic valuation transported to the additive value group `ℤ`. -/
theorem finitePlaceValueExponent_mul (v : HeightOneSpectrum (𝓞 F)) (f g : Fˣ) :
    finitePlaceValueExponent v (f * g) =
      finitePlaceValueExponent v f + finitePlaceValueExponent v g := by
  unfold finitePlaceValueExponent
  rw [Units.val_mul, Valuation.map_mul,
    WithZero.log_mul (finitePlaceValuation_ne_zero v f) (finitePlaceValuation_ne_zero v g)]
  ring

/-- The local principal map at a finite place, as a homomorphism from the global
multiplicative group to the multiplicative additive value group. -/
def finitePlaceValueMonoidHom (v : HeightOneSpectrum (𝓞 F)) :
    Fˣ →* Multiplicative ℤ where
  toFun f := Multiplicative.ofAdd (finitePlaceValueExponent v f)
  map_one' := by
    rw [finitePlaceValueExponent_one]
    rfl
  map_mul' f g := by
    rw [finitePlaceValueExponent_mul]
    rfl

/-- The local value data of IUT III, Example 3.6 at a finite place of a number
field: value group `ℤ`, integral cone the nonnegative integers, and local
principal map the `v`-adic exponent. -/
def numberFieldFiniteLocalValueData (v : HeightOneSpectrum (𝓞 F)) :
    LocalValueData F ℤ where
  cone := integerNonnegCone
  cone_sharp := by
    intro a ha ha'
    have h1 : 0 ≤ a := ha
    have h2 : 0 ≤ -a := ha'
    omega
  delta := finitePlaceValueMonoidHom v

@[simp]
theorem numberFieldFiniteLocalValueData_deltaAdd (v : HeightOneSpectrum (𝓞 F))
    (f : Fˣ) :
    (numberFieldFiniteLocalValueData v).deltaAdd f = finitePlaceValueExponent v f := by
  simp [numberFieldFiniteLocalValueData, LocalValueData.deltaAdd, finitePlaceValueMonoidHom]

/-- The local inclusion condition at a finite place is exactly the valuation
inequality `ν_v(f) + n a₁ - a₂ ≥ 0` of the handoff (chapter 1, B4). -/
theorem numberFieldFiniteLocalInclusion_iff (v : HeightOneSpectrum (𝓞 F))
    (n : ℕ) (f : Fˣ) (a1 a2 : ℤ) :
    (numberFieldFiniteLocalValueData v).localInclusion n f a1 a2 ↔
      finitePlaceValueExponent v f + n * a1 - a2 ≥ 0 := by
  unfold LocalValueData.localInclusion
  rw [numberFieldFiniteLocalValueData_deltaAdd]
  have hcone : (numberFieldFiniteLocalValueData v).cone = integerNonnegCone := rfl
  rw [hcone, mem_integerNonnegCone, nsmul_eq_mul]

/-! ## 2. The archimedean local value data -/

/-- The additive archimedean coordinate `-log (w f)` of a global unit at the
archimedean place `w`. -/
def archimedeanPlaceValue (w : NumberField.InfinitePlace F) (f : Fˣ) : ℝ :=
  -Real.log (w (f : F))

/-- The archimedean absolute value of a global unit is positive. -/
theorem infinitePlaceValue_pos (w : NumberField.InfinitePlace F) (f : Fˣ) :
    0 < w (f : F) :=
  NumberField.InfinitePlace.pos_iff.mpr (Units.ne_zero f)

@[simp]
theorem archimedeanPlaceValue_one (w : NumberField.InfinitePlace F) :
    archimedeanPlaceValue w (1 : Fˣ) = 0 := by
  simp [archimedeanPlaceValue]

/-- The archimedean coordinate is additive: `log` of a product is the sum of
the logarithms because the absolute value is multiplicative and nonzero. -/
theorem archimedeanPlaceValue_mul (w : NumberField.InfinitePlace F) (f g : Fˣ) :
    archimedeanPlaceValue w (f * g) =
      archimedeanPlaceValue w f + archimedeanPlaceValue w g := by
  unfold archimedeanPlaceValue
  rw [Units.val_mul, map_mul,
    Real.log_mul (ne_of_gt (infinitePlaceValue_pos w f))
      (ne_of_gt (infinitePlaceValue_pos w g))]
  ring

/-- The local principal map at an archimedean place, as a homomorphism from the
global multiplicative group to the multiplicative additive value group. -/
def archimedeanPlaceValueMonoidHom (w : NumberField.InfinitePlace F) :
    Fˣ →* Multiplicative ℝ where
  toFun f := Multiplicative.ofAdd (archimedeanPlaceValue w f)
  map_one' := by
    rw [archimedeanPlaceValue_one]
    rfl
  map_mul' f g := by
    rw [archimedeanPlaceValue_mul]
    rfl

/-- The local value data of IUT III, Example 3.6 at an archimedean place of a
number field: value group `ℝ`, integral cone the nonnegative reals, and local
principal map `-log (w x)`. -/
def numberFieldInfiniteLocalValueData (w : NumberField.InfinitePlace F) :
    LocalValueData F ℝ where
  cone := realNonnegCone
  cone_sharp := by
    intro a ha ha'
    have h1 : 0 ≤ a := ha
    have h2 : 0 ≤ -a := ha'
    linarith
  delta := archimedeanPlaceValueMonoidHom w

@[simp]
theorem numberFieldInfiniteLocalValueData_deltaAdd (w : NumberField.InfinitePlace F)
    (f : Fˣ) :
    (numberFieldInfiniteLocalValueData w).deltaAdd f = archimedeanPlaceValue w f := by
  simp [numberFieldInfiniteLocalValueData, LocalValueData.deltaAdd,
    archimedeanPlaceValueMonoidHom]

/-- The local inclusion condition at an archimedean place is the inequality
`-log (w f) + n a₁ - a₂ ≥ 0` of the handoff. -/
theorem numberFieldInfiniteLocalInclusion_iff (w : NumberField.InfinitePlace F)
    (n : ℕ) (f : Fˣ) (a1 a2 : ℝ) :
    (numberFieldInfiniteLocalValueData w).localInclusion n f a1 a2 ↔
      archimedeanPlaceValue w f + n * a1 - a2 ≥ 0 := by
  unfold LocalValueData.localInclusion
  rw [numberFieldInfiniteLocalValueData_deltaAdd]
  have hcone : (numberFieldInfiniteLocalValueData w).cone = realNonnegCone := rfl
  rw [hcone, mem_realNonnegCone, nsmul_eq_mul]

/-! ## 3. The packaged global place data -/

/-- The actual number-field place data of IUT III, Example 3.6: the finite-place
data from the genuine `v`-adic valuations and the archimedean data from the
genuine infinite-place absolute values. -/
def numberFieldGlobalPlaceData : GlobalPlaceData F where
  finiteValue := numberFieldFiniteLocalValueData
  infiniteValue := numberFieldInfiniteLocalValueData

@[simp]
theorem numberFieldGlobalPlaceData_finiteDelta (f : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    numberFieldGlobalPlaceData.finiteDelta f v = finitePlaceValueExponent v f := by
  simp [GlobalPlaceData.finiteDelta, numberFieldGlobalPlaceData]

@[simp]
theorem numberFieldGlobalPlaceData_infiniteDelta (f : Fˣ)
    (w : NumberField.InfinitePlace F) :
    numberFieldGlobalPlaceData.infiniteDelta f w = -Real.log (w (f : F)) := by
  simp [GlobalPlaceData.infiniteDelta, numberFieldGlobalPlaceData, archimedeanPlaceValue]

/-! ## 4. Finite support of the finite-place exponent -/

/-- The `v`-adic valuation of a nonzero integral element, written through the
multiplicity of `v` in the principal ideal `(r)`.  This is the definition of
`intValuation` unfolded. -/
theorem intValuation_eq_exp_neg_count (v : HeightOneSpectrum (𝓞 F)) {r : 𝓞 F}
    (hr : r ≠ 0) :
    v.intValuation r =
      WithZero.exp (-((Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span {r})).factors : ℤ)) :=
  v.intValuation_if_neg hr

/-- The logarithm of the `v`-adic valuation of a nonzero integral element is the
negative `v`-adic multiplicity of its principal ideal. -/
theorem log_intValuation_eq_neg_count (v : HeightOneSpectrum (𝓞 F)) {r : 𝓞 F}
    (hr : r ≠ 0) :
    WithZero.log (v.intValuation r) =
      -((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r})).factors : ℤ) := by
  rw [v.intValuation_if_neg hr, WithZero.log_exp]

/-- The `v`-adic valuation on the fraction field of a quotient of two integral
elements is the quotient of the two integral valuations. -/
theorem valuation_of_div_eq (v : HeightOneSpectrum (𝓞 F)) (a b : 𝓞 F) :
    v.valuation F ((algebraMap (𝓞 F) F a) / (algebraMap (𝓞 F) F b)) =
      v.intValuation a / v.intValuation b := by
  rw [Valuation.map_div, v.valuation_of_algebraMap, v.valuation_of_algebraMap]

/-- The finite-place exponent of a global unit computed from a fraction `a / b`
of integral elements: `ν_v(f) = val_v(b) - val_v(a)`, where `val_v(r)` is the
`v`-adic multiplicity of the principal ideal `(r)`.  This is the count/valuation
bridge that reduces the finite-support statement to ideal factorization. -/
theorem finitePlaceValueExponent_eq_count_sub (v : HeightOneSpectrum (𝓞 F))
    (f : Fˣ) (a b : 𝓞 F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hdiv : (algebraMap (𝓞 F) F a) / (algebraMap (𝓞 F) F b) = (f : F)) :
    finitePlaceValueExponent v f =
      ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors : ℤ)
        - ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {b})).factors : ℤ) := by
  unfold finitePlaceValueExponent
  rw [← hdiv, valuation_of_div_eq]
  rw [WithZero.log_div (v.intValuation_ne_zero a ha) (v.intValuation_ne_zero b hb)]
  rw [log_intValuation_eq_neg_count v hb, log_intValuation_eq_neg_count v ha]
  ring

/-- A global unit has nonzero `v`-adic exponent at only finitely many finite
places.  This is the arithmetic finite-support theorem behind the principal
divisor: the exponent equals `val_v(b) - val_v(a)` for a fraction `a / b` of
integral elements, and the support of either count is contained in the finite
set of prime divisors of the corresponding principal ideal. -/
theorem numberFieldFiniteSupport (f : Fˣ) :
    {v : HeightOneSpectrum (𝓞 F) | finitePlaceValueExponent v f ≠ 0}.Finite := by
  classical
  obtain ⟨a, b, hb, hdiv⟩ := IsFractionRing.div_surjective (𝓞 F) (f : F)
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hdiv
    exact Units.ne_zero f hdiv.symm
  have hb_ne : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hspan_a : Ideal.span {a} ≠ 0 := by
    rw [Ideal.zero_eq_bot]
    exact (Ideal.span_singleton_eq_bot.not.mpr ha)
  have hspan_b : Ideal.span {b} ≠ 0 := by
    rw [Ideal.zero_eq_bot]
    exact (Ideal.span_singleton_eq_bot.not.mpr hb_ne)
  have hsub : {v : HeightOneSpectrum (𝓞 F) | finitePlaceValueExponent v f ≠ 0} ⊆
      {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ Ideal.span {a}} ∪
        {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ Ideal.span {b}} := by
    intro v hv
    have hv' : finitePlaceValueExponent v f ≠ 0 := hv
    have hcount := finitePlaceValueExponent_eq_count_sub v f a b ha hb_ne hdiv
    rw [hcount] at hv'
    have hor : ((Associates.mk v.asIdeal).count
          (Associates.mk (Ideal.span {a})).factors) ≠ 0 ∨
        ((Associates.mk v.asIdeal).count
          (Associates.mk (Ideal.span {b})).factors) ≠ 0 := by
      by_contra h
      push Not at h
      exact hv' (by rw [h.1, h.2]; ring)
    rw [Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq]
    rcases hor with hca | hcb
    · left
      refine (v.intValuation_lt_one_iff_dvd a).mp ?_
      rw [v.intValuation_if_neg ha, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      have hpos : 0 < (Associates.mk v.asIdeal).count
          (Associates.mk (Ideal.span {a})).factors := Nat.pos_of_ne_zero hca
      omega
    · right
      refine (v.intValuation_lt_one_iff_dvd b).mp ?_
      rw [v.intValuation_if_neg hb_ne, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      have hpos : 0 < (Associates.mk v.asIdeal).count
          (Associates.mk (Ideal.span {b})).factors := Nat.pos_of_ne_zero hcb
      omega
  exact ((Ideal.finite_factors (I := Ideal.span {a}) hspan_a).union
    (Ideal.finite_factors (I := Ideal.span {b}) hspan_b)).subset hsub

/-- The actual number-field global place data has finite support: the finite
places with nonzero `v`-adic exponent of a global unit form a finite set. -/
theorem numberFieldGlobalPlaceData_hasFiniteSupport :
    (numberFieldGlobalPlaceData (F := F)).HasFiniteSupport := by
  intro f
  simpa [GlobalPlaceData.HasFiniteSupport] using
    (numberFieldFiniteSupport (F := F) f)

/-! ## 5. The principal divisors of a global unit -/

/-- The finite-support principal divisor of a global unit: the function
`v ↦ ν_v(f)` on the finite places, packaged as a finitely supported function.
The finiteness of its support is `numberFieldFiniteSupport`. -/
def principalDivisorFinite (f : Fˣ) : HeightOneSpectrum (𝓞 F) →₀ ℤ :=
  Finsupp.onFinset (numberFieldFiniteSupport f).toFinset
    (fun v => finitePlaceValueExponent v f)
    (fun _ hv => (numberFieldFiniteSupport f).mem_toFinset.mpr hv)

/-- Evaluation of the finite principal divisor is the `v`-adic exponent. -/
@[simp]
theorem principalDivisorFinite_apply (f : Fˣ) (v : HeightOneSpectrum (𝓞 F)) :
    principalDivisorFinite f v = finitePlaceValueExponent v f :=
  Finsupp.onFinset_apply

/-- The support of the finite principal divisor is exactly the finite set of
places at which the `v`-adic exponent is nonzero. -/
theorem principalDivisorFinite_mem_support_iff (f : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    v ∈ (principalDivisorFinite f).support ↔ finitePlaceValueExponent v f ≠ 0 := by
  rw [Finsupp.mem_support_iff, principalDivisorFinite_apply]

@[simp]
theorem principalDivisorFinite_one : principalDivisorFinite (1 : Fˣ) = 0 := by
  ext v
  simp

/-- The finite principal divisor is additive in the global unit: this is the
multiplicativity of the `v`-adic valuation, transported to the Finsupp monoid.
This is the additivity law used by the global ideal-family of Example 3.6. -/
theorem principalDivisorFinite_mul (f g : Fˣ) :
    principalDivisorFinite (f * g) = principalDivisorFinite f + principalDivisorFinite g := by
  ext v
  rw [principalDivisorFinite_apply, Finsupp.add_apply, principalDivisorFinite_apply,
    principalDivisorFinite_apply, finitePlaceValueExponent_mul]

/-- The finite principal divisor agrees with the finite coordinate of the
global place data. -/
theorem principalDivisorFinite_apply_eq_finiteDelta (f : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    principalDivisorFinite f v = (numberFieldGlobalPlaceData (F := F)).finiteDelta f v := by
  rw [principalDivisorFinite_apply, numberFieldGlobalPlaceData_finiteDelta]

/-- The archimedean principal function of a global unit: `w ↦ -log (w f)`. -/
def principalDivisorInfinite (f : Fˣ) : NumberField.InfinitePlace F → ℝ :=
  fun w => archimedeanPlaceValue w f

@[simp]
theorem principalDivisorInfinite_apply (f : Fˣ) (w : NumberField.InfinitePlace F) :
    principalDivisorInfinite f w = -Real.log (w (f : F)) := rfl

/-- The archimedean principal function is additive in the global unit, since the
archimedean absolute value is multiplicative. -/
theorem principalDivisorInfinite_mul (f g : Fˣ) :
    principalDivisorInfinite (f * g) =
      principalDivisorInfinite f + principalDivisorInfinite g := by
  funext w
  exact archimedeanPlaceValue_mul w f g

/-- The archimedean principal function agrees with the archimedean coordinate of
the global place data. -/
theorem principalDivisorInfinite_apply_eq_infiniteDelta (f : Fˣ)
    (w : NumberField.InfinitePlace F) :
    principalDivisorInfinite f w =
      (numberFieldGlobalPlaceData (F := F)).infiniteDelta f w := by
  rw [principalDivisorInfinite_apply, numberFieldGlobalPlaceData_infiniteDelta]

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
