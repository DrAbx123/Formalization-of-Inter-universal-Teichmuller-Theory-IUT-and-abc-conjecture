import LeanFormal.IUT.IUTII.Frobenioid.Example36NumberFieldPlaceCompletionBridge
import LeanFormal.IUT.IUTII.Frobenioid.Example36GlobalIdealFamilyActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceModelDivisor
import LeanFormal.IUT.IUTII.Frobenioid.Example36ValueMapKernels

set_option linter.unusedSectionVars false

/-!
# End-to-end sign consistency for the corrected finite-place exponent

Regression and consumer file for the **sign of the finite-place value
coordinate** of IUT III, Example 3.6.

The corrected convention of the tree is the *classical valuation exponent*
`nu_v(f)`: integral elements (units of `O_v`) have `nu_v(f) >= 0`, and for a
fraction `f = a / b` of integral elements the exponent is
`count_v(a) - count_v(b)`.  This is the sign in which

* the local integral cone of the finite value data is `N`,
* the global finite coordinate `D.finiteDelta f v` is `nu_v(f)`,
* the backend principal divisor has finite coordinates `nu_v(f)`, and
* the local completion exponent `completionValuationExponent` of the embedded
  unit equals `nu_v(f)`.

The file records the full consumer chain of this sign and a rejection
regression: a unit with negative classical exponent is *not* integral at the
standard object.  The old sign (the negative of the classical exponent, i.e.
the logarithmic value `WithZero.log` of Mathlib's adic value) would have made
the standard-object condition accept such a unit; the regression at the end of
the file states precisely that the removed pattern is the false inclusion
`(1/2) Z_2 subset Z_2`.

## Contents

1. `embeddedCompletionUnit`, the completion chain
   `finiteDelta = nu_v = completionValuationExponent`, the relation between the
   logarithmic convention `completionValuationAdd = -nu_v` and the classical
   exponent, and the `count(a) - count(b)` formula (plus its existence form).
2. The backend principal divisor: `principalDivisorExplicit` finite
   coordinates are the corrected exponent, its archimedean coordinates are
   `-log (w f)`, and the additive backend `SourceModelBackend.principalDivisorExplicit`
   restricts to the same explicit divisor; the value map of
   `Example36ValueMapKernels` is the same coordinate.
3. The arithmetic divisor `d(J) = -delta(J)` and the effective cone: an
   effective family (nonpositive `delta`-coordinates) has `d(J)` nonnegative
   in the explicit coordinates, hence its Grothendieck divisor class lies in
   the range of the effective cone; the balance identity is restated with the
   corrected exponent.
4. The rejection regression: at the standard finite object the local
   inclusion condition is exactly `0 <= nu_v(f)`; a negative corrected
   exponent is rejected; any morphism of global ideal families with standard
   source and target coordinates has nonnegative multiplier exponent; the
   legacy (negated) standard test is exhibited as accepting exactly the units
   the corrected test rejects.

## Boundary

This is a sign-consistency/regression fragment only.  No concrete number-field
example (`F = Q`, `v = (2)`, `f = 1/2`) is claimed here because the
`HeightOneSpectrum` instance and the corresponding computation are not
developed in this file; the statements are uniform in `F` and `v`.  No
theta-pilot, q-pilot, Tate, Hodge-theater or source-identification claim is
made.  The legacy predicate exists only to state the regression; no
declaration of the coherent layer uses the old sign.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open IsDedekindDomain NumberField
open scoped NumberField

universe u

variable {F : Type u} [Field F] [NumberField F]

/-! ## 1. The corrected exponent and the completion chain -/

/-- The image of a global unit in the actual `v`-adic completion. -/
def embeddedCompletionUnit (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    (v.adicCompletion F)ˣ :=
  Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom f

/-- The corrected finite exponent is, by definition, the negative logarithm of
Mathlib's adic valuation value (so that it is the classical exponent). -/
theorem finitePlaceValueExponent_eq_neg_log (v : HeightOneSpectrum (𝓞 F))
    (f : Fˣ) :
    finitePlaceValueExponent v f = -WithZero.log (v.valuation F (f : F)) :=
  rfl

/-- **Sign bridge between the two Mathlib conventions.**  The logarithmic
additive value `completionValuationAdd` (the `WithZero.log` of the completion
value) is the negative of the corrected classical exponent. -/
theorem completionValuationAdd_embedded_eq_neg_exponent
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    completionValuationAdd v (embeddedCompletionUnit v f) =
      -finitePlaceValueExponent v f := by
  change completionValuationAdd v
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom f) =
    -finitePlaceValueExponent v f
  rw [completionValuationAdd_coe, finitePlaceValueExponent_eq_neg_log]
  ring

/-- **Corrected exponent equals the local completion exponent.** -/
theorem finitePlaceValueExponent_eq_completionValuationExponent
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    finitePlaceValueExponent v f =
      completionValuationExponent v (embeddedCompletionUnit v f) := by
  rw [← numberFieldGlobalPlaceData_finiteDelta,
    numberFieldGlobalPlaceData_finiteDelta_eq_completionValuationExponent]
  rfl

/-- The global finite coordinate of the actual number-field place data is the
corrected classical exponent. -/
theorem numberField_finiteDelta_eq_finitePlaceValueExponent
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    (numberFieldGlobalPlaceData (F := F)).finiteDelta f v =
      finitePlaceValueExponent v f :=
  numberFieldGlobalPlaceData_finiteDelta f v

/-- The packaged finite local value data has principal map the corrected
exponent. -/
theorem numberFieldFiniteLocalValueData_deltaAdd_eq_classicalExponent
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    (numberFieldFiniteLocalValueData v).deltaAdd f = finitePlaceValueExponent v f :=
  numberFieldFiniteLocalValueData_deltaAdd v f

/-- Consumer restatement of the global/completion bridge: the finite
coordinate of the global place data is the completion exponent of the embedded
unit. -/
theorem numberField_finiteDelta_eq_completionValuationExponent
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    (numberFieldGlobalPlaceData (F := F)).finiteDelta f v =
      completionValuationExponent v (embeddedCompletionUnit v f) := by
  rw [numberFieldGlobalPlaceData_finiteDelta_eq_completionValuationExponent]
  rfl

/-- Consumer restatement: the packaged finite local principal map is the
completion exponent of the embedded unit. -/
theorem numberFieldFiniteLocalValueData_deltaAdd_eq_completionValuationExponent
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    (numberFieldFiniteLocalValueData v).deltaAdd f =
      completionValuationExponent v (embeddedCompletionUnit v f) := by
  rw [numberFieldFiniteLocalValueData_deltaAdd,
    finitePlaceValueExponent_eq_completionValuationExponent]

/-- **The `count(a) - count(b)` formula** for the corrected exponent, in the
consumer form: for a fraction `f = a / b` of integral elements,
`nu_v(f) = count_v(a) - count_v(b)`. -/
theorem classicalExponent_count_formula (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ)
    (a b : 𝓞 F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hdiv : (algebraMap (𝓞 F) F a) / (algebraMap (𝓞 F) F b) = (f : F)) :
    finitePlaceValueExponent v f =
      ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors : ℤ) -
        ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {b})).factors : ℤ) :=
  finitePlaceValueExponent_eq_count_sub v f a b ha hb hdiv

/-- Existence form of the count formula: every global unit has a fraction
representation `a / b` of integral elements for which the corrected exponent is
the count difference. -/
theorem exists_fraction_count_formula (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    ∃ a b : 𝓞 F, b ∈ nonZeroDivisors (𝓞 F) ∧
      (algebraMap (𝓞 F) F a) / (algebraMap (𝓞 F) F b) = (f : F) ∧
      finitePlaceValueExponent v f =
        ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors : ℤ) -
          ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {b})).factors : ℤ) := by
  obtain ⟨a, b, hb, hdiv⟩ := IsFractionRing.div_surjective (𝓞 F) (f : F)
  have hb_ne : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hdiv
    exact Units.ne_zero f hdiv.symm
  exact ⟨a, b, hb, hdiv, classicalExponent_count_formula v f a b ha hb_ne hdiv⟩

/-- **End-to-end corrected-sign agreement** at a finite place: the global finite
coordinate, the packaged local principal map, the global/local completion bridge
and the local completion value data all present the same corrected exponent. -/
theorem correctedSign_endToEnd (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    (numberFieldGlobalPlaceData (F := F)).finiteDelta f v =
        finitePlaceValueExponent v f ∧
      finitePlaceValueExponent v f =
        completionValuationExponent v (embeddedCompletionUnit v f) ∧
      (numberFieldFiniteLocalValueData v).deltaAdd f =
        completionValuationExponent v (embeddedCompletionUnit v f) ∧
      completionValuationAdd v (embeddedCompletionUnit v f) =
        -finitePlaceValueExponent v f :=
  ⟨numberField_finiteDelta_eq_finitePlaceValueExponent v f,
    finitePlaceValueExponent_eq_completionValuationExponent v f,
    numberFieldFiniteLocalValueData_deltaAdd_eq_completionValuationExponent v f,
    completionValuationAdd_embedded_eq_neg_exponent v f⟩

/-! ## 2. The backend principal-divisor coordinates -/

/-- The finite coordinate of the explicit backend principal divisor is the
corrected classical exponent. -/
theorem principalDivisorExplicit_finite_apply_eq_classicalExponent
    (f : Fˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (principalDivisorExplicit (F := F) f).1 v = finitePlaceValueExponent v f := by
  change (principalDivisorFinite f) v = finitePlaceValueExponent v f
  exact principalDivisorFinite_apply f v

/-- The archimedean coordinate of the explicit backend principal divisor is
`-log` of the archimedean absolute value. -/
theorem principalDivisorExplicit_infinite_apply_eq_neg_log
    (f : Fˣ) (w : NumberField.InfinitePlace F) :
    (principalDivisorExplicit (F := F) f).2 w = -Real.log (w (f : F)) := by
  change principalDivisorInfinite f w = -Real.log (w (f : F))
  exact principalDivisorInfinite_apply f w

/-- The finite coordinate of the number-field principal-divisor family is the
corrected classical exponent. -/
theorem sourceModelPrincipalDivisor_finite_apply_eq_classicalExponent
    (f : Fˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (sourceModelPrincipalDivisor (numberFieldGlobalPlaceData (F := F))
        numberFieldGlobalPlaceData_hasFiniteSupport f).finite v =
      finitePlaceValueExponent v f := by
  rw [sourceModelPrincipalDivisor_finite_apply, numberFieldGlobalPlaceData_finiteDelta]

/-- The archimedean coordinate of the number-field principal-divisor family is
`-log` of the archimedean absolute value. -/
theorem sourceModelPrincipalDivisor_infinite_apply_eq_neg_log
    (f : Fˣ) (w : NumberField.InfinitePlace F) :
    (sourceModelPrincipalDivisor (numberFieldGlobalPlaceData (F := F))
        numberFieldGlobalPlaceData_hasFiniteSupport f).infinite w =
      -Real.log (w (f : F)) := by
  rw [sourceModelPrincipalDivisor_infinite_apply, numberFieldGlobalPlaceData_infiniteDelta]

/-- The additive backend principal-divisor map, evaluated on `Additive.ofMul f`,
is the explicit principal divisor of `f`. -/
theorem backend_principalDivisorExplicit_apply (f : Fˣ) :
    SourceModelBackend.principalDivisorExplicit (Additive.ofMul f) =
      principalDivisorExplicit (F := F) f := by
  change (principalDivisorFinite (Additive.toMul (Additive.ofMul f)),
      fun w => principalDivisorInfinite (Additive.toMul (Additive.ofMul f)) w) =
    principalDivisorExplicit (F := F) f
  rw [toMul_ofMul]
  rfl

/-- The finite coordinate of the additive backend principal-divisor map is the
corrected classical exponent. -/
theorem backend_principalDivisorExplicit_fst_eq_classicalExponent
    (f : Fˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (SourceModelBackend.principalDivisorExplicit (Additive.ofMul f)).1 v =
      finitePlaceValueExponent v f := by
  rw [backend_principalDivisorExplicit_apply]
  exact principalDivisorExplicit_finite_apply_eq_classicalExponent f v

/-- The archimedean coordinate of the additive backend principal-divisor map is
`-log` of the archimedean absolute value. -/
theorem backend_principalDivisorExplicit_snd_eq_neg_log
    (f : Fˣ) (w : NumberField.InfinitePlace F) :
    (SourceModelBackend.principalDivisorExplicit (Additive.ofMul f)).2 w =
      -Real.log (w (f : F)) := by
  rw [backend_principalDivisorExplicit_apply]
  exact principalDivisorExplicit_infinite_apply_eq_neg_log f w

/-- The actual-number-field value map of `Example36ValueMapKernels` is the
backend explicit principal-divisor finite coordinate. -/
theorem finiteValueMap_eq_backend_principalDivisorExplicit_fst
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    finiteValueMap (numberFieldGlobalPlaceData (F := F)) v f =
      ((principalDivisorExplicit (F := F) f).1 v : ℝ) :=
  finiteValueMap_eq_principalDivisorExplicit_fst v f

/-- The actual-number-field value map is the corrected classical exponent, cast
to `Real`. -/
theorem finiteValueMap_eq_classicalExponent_cast
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    finiteValueMap (numberFieldGlobalPlaceData (F := F)) v f =
      (finitePlaceValueExponent v f : ℝ) :=
  finiteValueMap_numberField v f

/-- **Backend-coordinate agreement** of the corrected sign at a finite and an
archimedean place. -/
theorem backendCoordinates_endToEnd (f : Fˣ) (v : HeightOneSpectrum (𝓞 F))
    (w : NumberField.InfinitePlace F) :
    (principalDivisorExplicit (F := F) f).1 v = finitePlaceValueExponent v f ∧
      (sourceModelPrincipalDivisor (numberFieldGlobalPlaceData (F := F))
          numberFieldGlobalPlaceData_hasFiniteSupport f).finite v =
        finitePlaceValueExponent v f ∧
      (SourceModelBackend.principalDivisorExplicit (Additive.ofMul f)).1 v =
        finitePlaceValueExponent v f ∧
      (principalDivisorExplicit (F := F) f).2 w = -Real.log (w (f : F)) ∧
      ((principalDivisorExplicit (F := F) f).1 v : ℝ) =
        finiteValueMap (numberFieldGlobalPlaceData (F := F)) v f :=
  ⟨principalDivisorExplicit_finite_apply_eq_classicalExponent f v,
    sourceModelPrincipalDivisor_finite_apply_eq_classicalExponent f v,
    backend_principalDivisorExplicit_fst_eq_classicalExponent f v,
    principalDivisorExplicit_infinite_apply_eq_neg_log f w,
    (finiteValueMap_eq_backend_principalDivisorExplicit_fst v f).symm⟩

/-! ## 3. The arithmetic divisor `d(J) = -delta(J)` and the effective cone -/

/-- A global ideal family is *effective* in the frozen `d = -delta` convention
when its `delta`-coordinates are nonpositive at every place, so that
`d(J) = -delta(J)` is a nonnegative explicit divisor. -/
def IsEffectiveFamily (J : GlobalIdealFamily F) : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 F), J.finite v ≤ 0) ∧
    ∀ w : NumberField.InfinitePlace F, J.infinite w ≤ 0

/-- The nonnegativity of the explicit arithmetic divisor `d(J) = -delta(J)` is
exactly effectivity of the family. -/
theorem explicitNonneg_arithmeticDivisorExplicit_iff (J : GlobalIdealFamily F) :
    SourceModelBackend.explicitNonneg (arithmeticDivisorExplicit J) ↔
      IsEffectiveFamily J := by
  constructor
  · intro h
    refine ⟨fun v => ?_, fun w => ?_⟩
    · have hv := h.1 v
      change (0 : ℤ) ≤ (-J.finite) v at hv
      rw [Finsupp.neg_apply] at hv
      omega
    · have hw := h.2 w
      change (0 : ℝ) ≤ -J.infinite w at hw
      linarith
  · intro h
    refine ⟨fun v => ?_, fun w => ?_⟩
    · change (0 : ℤ) ≤ (-J.finite) v
      rw [Finsupp.neg_apply]
      have hv := h.1 v
      omega
    · change (0 : ℝ) ≤ -J.infinite w
      have hw := h.2 w
      linarith

/-- The comparison map sends the Grothendieck divisor class of an ideal family
to its explicit arithmetic divisor `d(J) = -delta(J)`. -/
theorem coneComparison_idealFamilyDivisorClass (J : GlobalIdealFamily F) :
    SourceModelBackend.coneComparison
        (SourceModelBackend.idealFamilyDivisorClass (F := F) J) =
      arithmeticDivisorExplicit J := by
  rw [SourceModelBackend.idealFamilyDivisorClass]
  rw [← SourceModelBackend.coneGrothendieckEquiv_apply]
  rw [AddEquiv.apply_symm_apply]
  rfl

/-- The finite coordinate of the realized divisor class is `d(J) = -delta(J)`. -/
theorem coneGrothendieckEquiv_idealFamilyDivisorClass_finite
    (J : GlobalIdealFamily F) (v : HeightOneSpectrum (𝓞 F)) :
    (SourceModelBackend.coneGrothendieckEquiv
        (SourceModelBackend.idealFamilyDivisorClass (F := F) J)).1 v =
      -J.finite v := by
  rw [SourceModelBackend.idealFamilyDivisorClass, AddEquiv.apply_symm_apply,
    Finsupp.neg_apply]

/-- **Effectivity and the effective cone**: the Grothendieck divisor class of an
effective family lies in the range of the effective cone (the nonnegative,
hence effective, part of the group completion). -/
theorem idealFamilyDivisorClass_mem_range_of_effective (J : GlobalIdealFamily F)
    (hJ : IsEffectiveFamily J) :
    SourceModelBackend.idealFamilyDivisorClass (F := F) J ∈
      Set.range (Algebra.GrothendieckAddGroup.of
        (M := SourceModelBackend.EffectiveDivisor F)) := by
  rw [SourceModelBackend.coneComparison_nonneg_iff_mem_range,
    coneComparison_idealFamilyDivisorClass]
  exact (explicitNonneg_arithmeticDivisorExplicit_iff J).mpr hJ

/-- The realized backend divisor class of an effective family lies in the
range of the effective cone. -/
theorem backendObject_divisorClass_mem_range_of_effective
    (J : GlobalIdealFamily F) (hJ : IsEffectiveFamily J) :
    (backendObject J).divisorClass ∈
      Set.range (Algebra.GrothendieckAddGroup.of
        (M := SourceModelBackend.EffectiveDivisor F)) := by
  rw [backendObject_divisorClass]
  exact idealFamilyDivisorClass_mem_range_of_effective J hJ

/-- **Balance identity at a finite place with the corrected exponent**:
`n d(J1) + Z = d(J2) + div(f)`, where the principal-divisor coordinate of the
multiplier is the corrected classical exponent. -/
theorem balance_finite_corrected
    {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom (numberFieldGlobalPlaceData (F := F)) J₁ J₂)
    (v : HeightOneSpectrum (𝓞 F)) :
    -(h.degree • J₁.finite v) + h.effectiveFinite v =
      -J₂.finite v + finitePlaceValueExponent v h.multiplier := by
  rw [GlobalIdealFamily.Hom.balance_finite, numberFieldGlobalPlaceData_finiteDelta]

/-- **Balance identity at an archimedean place with the corrected `-log`
coordinate**. -/
theorem balance_infinite_corrected
    {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom (numberFieldGlobalPlaceData (F := F)) J₁ J₂)
    (w : NumberField.InfinitePlace F) :
    -(h.degree • J₁.infinite w) + h.effectiveInfinite w =
      -J₂.infinite w + -Real.log (w (h.multiplier : F)) := by
  rw [GlobalIdealFamily.Hom.balance_infinite, numberFieldGlobalPlaceData_infiniteDelta]

/-- **The effective part is nonnegative in the corrected coordinates**. -/
theorem effectiveFinite_nonneg_corrected
    {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom (numberFieldGlobalPlaceData (F := F)) J₁ J₂)
    (v : HeightOneSpectrum (𝓞 F)) :
    0 ≤ finitePlaceValueExponent v h.multiplier + h.degree • J₁.finite v -
      J₂.finite v := by
  have hin := GlobalIdealFamily.Hom.effectiveFinite_mem_cone h v
  have hmem : 0 ≤ h.effectiveFinite v := by
    simpa [numberFieldGlobalPlaceData, numberFieldFiniteLocalValueData,
      mem_integerNonnegCone] using hin
  simpa [GlobalIdealFamily.Hom.effectiveFinite,
    numberFieldGlobalPlaceData_finiteDelta] using hmem

/-- With zero effective part, the corrected balance identity gives
`J2 = n J1 + div(f)` in the finite coordinates. -/
theorem balance_zeroEffective_eq
    {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom (numberFieldGlobalPlaceData (F := F)) J₁ J₂)
    (v : HeightOneSpectrum (𝓞 F)) (hzero : h.effectiveFinite v = 0) :
    J₂.finite v =
      h.degree • J₁.finite v + finitePlaceValueExponent v h.multiplier := by
  have hb := balance_finite_corrected h v
  rw [hzero] at hb
  linarith

/-! ## 4. The rejection regression and the legacy sign pattern -/

/-- The legacy (rejected) sign convention at the standard finite object:
replacing the corrected exponent `nu_v(f)` by its negative in the
standard-object condition gives the test `0 <= -nu_v(f)`.  This predicate
exists only to state the regression; the coherent layer never uses it. -/
def legacyStandardIntegrality (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) : Prop :=
  0 ≤ -finitePlaceValueExponent v f

/-- The legacy test accepts exactly the units whose corrected exponent is
nonpositive. -/
theorem legacyStandardIntegrality_iff (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    legacyStandardIntegrality v f ↔ finitePlaceValueExponent v f ≤ 0 := by
  unfold legacyStandardIntegrality
  constructor <;> intro h <;> omega

/-- The legacy test accepts every unit with negative corrected exponent. -/
theorem legacyStandardIntegrality_of_negative (v : HeightOneSpectrum (𝓞 F))
    (f : Fˣ) (h : finitePlaceValueExponent v f < 0) :
    legacyStandardIntegrality v f := by
  rw [legacyStandardIntegrality_iff]
  omega

/-- The corrected standard-object condition, in consumer form. -/
theorem correctedStandard_iff (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (f : Fˣ) :
    (numberFieldFiniteLocalValueData v).localInclusion n f 0 0 ↔
      0 ≤ finitePlaceValueExponent v f :=
  numberFieldFiniteLocalInclusion_standard_iff v n f

/-- The corrected standard-object condition rejects every unit with negative
exponent. -/
theorem correctedStandard_rejects_negative (v : HeightOneSpectrum (𝓞 F)) (n : ℕ)
    (f : Fˣ) (h : finitePlaceValueExponent v f < 0) :
    ¬(numberFieldFiniteLocalValueData v).localInclusion n f 0 0 :=
  numberFieldFiniteLocalInclusion_standard_of_neg v n f h

/-- At the standard finite object, a unit with negative corrected exponent is
rejected by the corrected condition while the legacy negated-sign test accepts
it. -/
theorem legacy_accepts_negative_corrected_rejects
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ)
    (h : finitePlaceValueExponent v f < 0) :
    legacyStandardIntegrality v f ∧
      ¬(numberFieldFiniteLocalValueData v).localInclusion 1 f 0 0 :=
  ⟨legacyStandardIntegrality_of_negative v f h,
    correctedStandard_rejects_negative v 1 f h⟩

/-- **A morphism of global ideal families with standard source and target
coordinates at `v` has nonnegative multiplier exponent at `v`.**  This is the
Hom-level consumer of the corrected sign. -/
theorem hom_multiplier_exponent_nonneg_of_standard
    {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom (numberFieldGlobalPlaceData (F := F)) J₁ J₂)
    (v : HeightOneSpectrum (𝓞 F)) (h₁ : J₁.finite v = 0) (h₂ : J₂.finite v = 0) :
    0 ≤ finitePlaceValueExponent v h.multiplier := by
  have hinc := h.finite_incl v
  change (numberFieldFiniteLocalValueData v).localInclusion h.degree h.multiplier
    (J₁.finite v) (J₂.finite v) at hinc
  rw [numberFieldFiniteLocalInclusion_iff] at hinc
  simpa [h₁, h₂] using hinc

/-- **No morphism exists with a negative-exponent multiplier at a standard place**:
there are no source/target standard coordinates and no global ideal-family
morphism whose multiplier has negative corrected exponent at `v`. -/
theorem no_hom_negativeExponent_at_standard (f : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) (hneg : finitePlaceValueExponent v f < 0) :
    ¬ ∃ (J₁ J₂ : GlobalIdealFamily F)
        (h : GlobalIdealFamily.Hom (numberFieldGlobalPlaceData (F := F)) J₁ J₂),
      h.multiplier = f ∧ J₁.finite v = 0 ∧ J₂.finite v = 0 := by
  rintro ⟨J₁, J₂, h, rfl, h₁, h₂⟩
  exact (not_le.mpr hneg) (hom_multiplier_exponent_nonneg_of_standard h v h₁ h₂)

/-- The standard-object version: a Hom from `0` to `0` has nonnegative
multiplier exponent at every finite place. -/
theorem standardHom_multiplier_exponent_nonneg (f : Fˣ)
    (v : HeightOneSpectrum (𝓞 F))
    (h : GlobalIdealFamily.Hom (numberFieldGlobalPlaceData (F := F)) 0 0)
    (hmult : h.multiplier = f) :
    0 ≤ finitePlaceValueExponent v f := by
  rw [← hmult]
  exact hom_multiplier_exponent_nonneg_of_standard h v (by simp) (by simp)

/-- **The `(1/2) Z_2 subset Z_2` regression**: a unit non-integral at `v`
(negative corrected exponent) is rejected at the standard object, while the
legacy negated-sign test would accept it.  The old pattern is exactly the
acceptance of this false inclusion. -/
theorem halfIntegralPattern_eliminated (v : HeightOneSpectrum (𝓞 F)) (n : ℕ)
    (f : Fˣ) (h : finitePlaceValueExponent v f < 0) :
    (¬(numberFieldFiniteLocalValueData v).localInclusion n f 0 0) ∧
      legacyStandardIntegrality v f :=
  ⟨correctedStandard_rejects_negative v n f h,
    legacyStandardIntegrality_of_negative v f h⟩

/-! ## 5. The bundled sign-consistency regression -/

/-- **End-to-end sign-consistency regression**: the corrected finite exponent is
the completion exponent of the embedded unit, is the finite coordinate of the
backend principal divisor, and rejects negative-exponent units at the standard
object. -/
theorem signConsistencyRegression :
    (∀ (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ),
        (numberFieldGlobalPlaceData (F := F)).finiteDelta f v =
          completionValuationExponent v (embeddedCompletionUnit v f)) ∧
      (∀ (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ),
        finitePlaceValueExponent v f =
          completionValuationExponent v (embeddedCompletionUnit v f)) ∧
      (∀ (f : Fˣ) (v : HeightOneSpectrum (𝓞 F)),
        (principalDivisorExplicit (F := F) f).1 v =
          finitePlaceValueExponent v f) ∧
      (∀ (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (f : Fˣ),
        finitePlaceValueExponent v f < 0 →
          ¬(numberFieldFiniteLocalValueData v).localInclusion n f 0 0) :=
  ⟨fun v f => numberField_finiteDelta_eq_completionValuationExponent v f,
    fun v f => finitePlaceValueExponent_eq_completionValuationExponent v f,
    fun f v => principalDivisorExplicit_finite_apply_eq_classicalExponent f v,
    fun v n f h => correctedStandard_rejects_negative v n f h⟩

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
