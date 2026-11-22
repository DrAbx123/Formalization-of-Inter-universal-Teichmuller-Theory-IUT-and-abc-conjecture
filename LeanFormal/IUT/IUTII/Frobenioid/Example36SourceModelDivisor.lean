import LeanFormal.IUT.IUTII.Frobenioid.Example36GlobalIdealFamily
import LeanFormal.IUT.IUTII.Frobenioid.Example36NumberFieldPlaceData
import LeanFormal.IUT.IUTII.Frobenioid.Example36LocalIdealValuation
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceModelBackend
import LeanFormal.IUT.IUTII.Frobenioid.DivisorialMonoidMinimalReplacement
import Iut.Foundations.SourceModelFrobenioid

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.show false

/-!
# The arithmetic divisor backend and principal divisor of a global ideal family

Layer-4b of the Example 3.6 backend (handoff chapter 1 H/I).

## Contents

* `arithmeticDivisor J = d(J)` with the backend sign convention
  `d(J) = -delta(J)`, and the principal divisor `sourceModelPrincipalDivisor D hD f` in the
  same `nu_v` / `-log|w|` coordinates; `d` is additive and
  `div(f g) = div(f) + div(g)`.  The construction is specialized to the
  actual number-field data (`principalDivisor_numberField`) and the finite
  support of the principal divisor is characterized.
* The backend object realization on the arithmetic-divisor interface:
  `backendObject J` is the object of the imported Layer-4a backend
  (`Example36SourceModelBackend.objectOfIdealFamily`), whose `Object.base` is
  the unique bottom-base object and whose `Object.divisorClass` is `d(J)`;
  `coneGrothendieckEquiv_backendObject_divisorClass` proves that after the
  imported group-completion equivalence the realized class is exactly the
  explicit signed divisor `d(J) = -delta(J)`, and
  `backendObject_principalDivisor_divisorClass` gives the corresponding
  agreement with `div(f)` (up to the frozen sign convention `d = -delta`).
* Naturality under a faithful domain isomorphism: the induced unit map, the
  induced map on the unit quotient `F^x/U`, commutation of principal ideals
  with a ring homomorphism, preservation of the local integrality
  `(x) (y)^n <= (z)`, and the pointwise commutation of the principal divisor
  and of `d = -delta` with the induced place maps.
* Recorded DVR-extension ramification `e` with the law
  `nu'(a) = e * nu(a)` as an explicit hypothesis (never a general theorem):
  scaling of the principal-divisor and arithmetic-divisor coordinates,
  preservation of the integral (nonnegative) condition, and the criterion
  `e = 1` iff the normalized valuations agree on a unit with nonzero
  exponent.

## Imported vs new

* Imported read-only from `Example36SourceModelBackend` (task-13): the
  effective divisor cone `EffectiveDivisor`, the explicit divisor group
  `ExplicitDivisor`, `explicitNonneg`, the comparison map `coneComparison`, the
  group-completion equivalence `coneGrothendieckEquiv`, the saturated
  `effectiveDivisorialAddMonoid`, the one-object `DivisorialMonoidOn`
  `globalDivisorMonoidOn`, and the backend object/divisor-class realization
  `objectOfIdealFamily` / `idealFamilyDivisorClass`.
* New in this file: the arithmetic divisor `d(J)` and the principal divisor
  `div(f)`; the agreement lemmas between the imported backend object and
  `d(J)` / `div(f)`; the naturality theorems; and the recorded
  DVR-ramification structure and its consequences.  No construction from the
  imported backend is duplicated here.

Boundary: no theta-pilot, q-pilot, Tate uniformization, Hodge-theater or
source-identification claim is made.  The DVR extension `e` is a hypothesis,
not a derived equality; `nu' = nu` is never claimed.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open scoped NumberField
open IsDedekindDomain NumberField

universe u

variable {F : Type u} [Field F] [NumberField F]

/-! ## 1. The arithmetic divisor `d(J) = -delta(J)` -/

/-- The arithmetic divisor `d(J)` attached to a global ideal family object
`J`, with the backend sign convention `d(J) = -delta(J)` of handoff H. -/
def arithmeticDivisor (J : GlobalIdealFamily F) : GlobalIdealFamily F :=
  -J

@[simp]
theorem arithmeticDivisor_finite (J : GlobalIdealFamily F)
    (v : HeightOneSpectrum (𝓞 F)) :
    (arithmeticDivisor J).finite v = -J.finite v := rfl

@[simp]
theorem arithmeticDivisor_infinite (J : GlobalIdealFamily F)
    (w : NumberField.InfinitePlace F) :
    (arithmeticDivisor J).infinite w = -J.infinite w := rfl

@[simp]
theorem arithmeticDivisor_zero :
    arithmeticDivisor (0 : GlobalIdealFamily F) = 0 := by
  apply GlobalIdealFamily.ext
  · ext v
    simp [arithmeticDivisor]
  · funext w
    simp [arithmeticDivisor]

@[simp]
theorem arithmeticDivisor_add (J₁ J₂ : GlobalIdealFamily F) :
    arithmeticDivisor (J₁ + J₂) = arithmeticDivisor J₁ + arithmeticDivisor J₂ := by
  apply GlobalIdealFamily.ext
  · ext v
    simp only [arithmeticDivisor, GlobalIdealFamily.neg_finite,
      GlobalIdealFamily.add_finite, Finsupp.add_apply, Finsupp.neg_apply]
    ring
  · funext w
    simp only [arithmeticDivisor, GlobalIdealFamily.neg_infinite,
      GlobalIdealFamily.add_infinite]
    change -((J₁.infinite + J₂.infinite) w) = (-J₁.infinite) w + (-J₂.infinite) w
    simp only [Pi.add_apply, Pi.neg_apply]
    ring

/-- The object coordinate is recovered from the arithmetic divisor:
`delta(J) = -d(J)`. -/
@[simp]
theorem neg_arithmeticDivisor (J : GlobalIdealFamily F) :
    -arithmeticDivisor J = J := by
  apply GlobalIdealFamily.ext
  · ext v
    simp [arithmeticDivisor]
  · funext w
    simp [arithmeticDivisor]

/-- Arithmetic divisors are additive over natural multiples:
`d(n . J) = n . d(J)`. -/
@[simp]
theorem arithmeticDivisor_nsmul (n : ℕ) (J : GlobalIdealFamily F) :
    arithmeticDivisor (n • J) = n • arithmeticDivisor J := by
  apply GlobalIdealFamily.ext
  · ext v
    simp only [arithmeticDivisor, GlobalIdealFamily.neg_finite,
      GlobalIdealFamily.nsmul_finite, Finsupp.smul_apply, Finsupp.neg_apply]
    ring
  · funext w
    simp only [arithmeticDivisor, GlobalIdealFamily.neg_infinite,
      GlobalIdealFamily.nsmul_infinite]
    change -((n • J.infinite) w) = (n • -J.infinite) w
    simp only [Pi.smul_apply, nsmul_eq_mul, Pi.neg_apply]
    ring

/-! ## 2. The principal divisor `div(f)` -/

/-- The principal divisor `div(f)` of a global unit in value coordinates:
`nu_v(f)` at finite places, `-log (w f)` at archimedean places.  The finite
part is a `Finsupp` because `D` has finite support (explicit hypothesis, proved
for the actual number-field data in `Example36NumberFieldPlaceData`). -/
def sourceModelPrincipalDivisor (D : GlobalPlaceData F) (hD : D.HasFiniteSupport)
    (f : Fˣ) : GlobalIdealFamily F where
  finite :=
    Finsupp.onFinset (hD f).toFinset (fun v => D.finiteDelta f v)
      (fun v hv => (hD f).mem_toFinset.mpr hv)
  infinite := fun w => D.infiniteDelta f w

theorem sourceModelPrincipalDivisor_finite_apply (D : GlobalPlaceData F)
    (hD : D.HasFiniteSupport) (f : Fˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (sourceModelPrincipalDivisor D hD f).finite v = D.finiteDelta f v := by
  show (Finsupp.onFinset (hD f).toFinset (fun v => D.finiteDelta f v)
    (fun v hv => (hD f).mem_toFinset.mpr hv)) v = D.finiteDelta f v
  exact Finsupp.onFinset_apply

@[simp]
theorem sourceModelPrincipalDivisor_infinite_apply (D : GlobalPlaceData F)
    (hD : D.HasFiniteSupport) (f : Fˣ) (w : NumberField.InfinitePlace F) :
    (sourceModelPrincipalDivisor D hD f).infinite w = D.infiniteDelta f w := rfl

@[simp]
theorem principalDivisor_one (D : GlobalPlaceData F)
    (hD : D.HasFiniteSupport) :
    sourceModelPrincipalDivisor D hD (1 : Fˣ) = 0 := by
  apply GlobalIdealFamily.ext
  · ext v
    rw [show (sourceModelPrincipalDivisor D hD (1 : Fˣ)).finite v = D.finiteDelta 1 v from
      sourceModelPrincipalDivisor_finite_apply D hD 1 v]
    rw [GlobalPlaceData.finiteDelta_one]
    rfl
  · funext w
    rw [sourceModelPrincipalDivisor_infinite_apply, GlobalPlaceData.infiniteDelta_one]
    rfl

/-- The principal divisor is additive: `div(f g) = div(f) + div(g)`. -/
@[simp]
theorem sourceModelPrincipalDivisor_mul (D : GlobalPlaceData F)
    (hD : D.HasFiniteSupport) (f g : Fˣ) :
    sourceModelPrincipalDivisor D hD (f * g) =
      sourceModelPrincipalDivisor D hD f + sourceModelPrincipalDivisor D hD g := by
  apply GlobalIdealFamily.ext
  · ext v
    rw [sourceModelPrincipalDivisor_finite_apply, GlobalIdealFamily.add_finite,
      Finsupp.add_apply, sourceModelPrincipalDivisor_finite_apply,
      sourceModelPrincipalDivisor_finite_apply, GlobalPlaceData.finiteDelta_mul]
  · funext w
    simp only [sourceModelPrincipalDivisor_infinite_apply, GlobalIdealFamily.add_infinite,
      GlobalPlaceData.infiniteDelta_mul]

/-- The principal divisor specializes to the principal divisor built from the
actual number-field place data in `Example36NumberFieldPlaceData`. -/
theorem principalDivisor_numberField (f : Fˣ) :
    sourceModelPrincipalDivisor (numberFieldGlobalPlaceData (F := F))
        numberFieldGlobalPlaceData_hasFiniteSupport f =
      ⟨principalDivisorFinite f, principalDivisorInfinite f⟩ := by
  apply GlobalIdealFamily.ext
  · ext v
    rw [sourceModelPrincipalDivisor_finite_apply, numberFieldGlobalPlaceData_finiteDelta,
      principalDivisorFinite_apply]
  · funext w
    rw [sourceModelPrincipalDivisor_infinite_apply, numberFieldGlobalPlaceData_infiniteDelta]
    rfl

/-- The support of the principal divisor is exactly the finite set of finite
places where the valuation exponent is nonzero. -/
theorem principalDivisor_finite_support (D : GlobalPlaceData F)
    (hD : D.HasFiniteSupport) (f : Fˣ) :
    (sourceModelPrincipalDivisor D hD f).finite.support =
      {v : HeightOneSpectrum (𝓞 F) | D.finiteDelta f v ≠ 0} := by
  ext v
  rw [Finset.mem_coe, Finsupp.mem_support_iff, sourceModelPrincipalDivisor_finite_apply]
  rfl

/-! ## 3. The backend object and its arithmetic-divisor realization -/

/-- The explicit signed divisor `d(J) = -delta(J)` attached to a global ideal
family object, in the explicit divisor group of the imported backend. -/
def arithmeticDivisorExplicit (J : GlobalIdealFamily F) :
    SourceModelBackend.ExplicitDivisor F :=
  (-J.finite, fun w => -J.infinite w)

/-- The backend object attached to a global ideal family: realized by the
imported Layer-4a backend over the bottom base category. -/
def backendObject (J : GlobalIdealFamily F) :
    Iut.SourceModelFrobenioid.Object
      (SourceModelBackend.globalDivisorMonoidOn (F := F)) :=
  SourceModelBackend.objectOfIdealFamily (F := F) J

@[simp]
theorem backendObject_base (J : GlobalIdealFamily F) :
    (backendObject J).base = SourceModelBackend.bottomPoint := rfl

@[simp]
theorem backendObject_divisorClass (J : GlobalIdealFamily F) :
    (backendObject J).divisorClass =
      SourceModelBackend.idealFamilyDivisorClass (F := F) J := rfl

/-- **Agreement of `Object.divisorClass` with `d(J)`.**  After applying the
imported group-completion equivalence, the realized divisor class of the
backend object is exactly the explicit signed divisor `d(J) = -delta(J)`. -/
theorem coneGrothendieckEquiv_backendObject_divisorClass (J : GlobalIdealFamily F) :
    SourceModelBackend.coneGrothendieckEquiv (F := F)
        ((backendObject J).divisorClass) =
      arithmeticDivisorExplicit J := by
  rw [backendObject_divisorClass, SourceModelBackend.idealFamilyDivisorClass]
  exact AddEquiv.apply_symm_apply _ _

/-- **Agreement at the standard object.**  For the standard ideal family `0`
(`d(0) = 0`), the realized divisor class maps to the zero explicit divisor
under the imported group-completion equivalence. -/
theorem coneGrothendieckEquiv_backendObject_zero :
    SourceModelBackend.coneGrothendieckEquiv (F := F)
        ((backendObject (0 : GlobalIdealFamily F)).divisorClass) =
      (0 : SourceModelBackend.ExplicitDivisor F) := by
  rw [coneGrothendieckEquiv_backendObject_divisorClass]
  apply Prod.ext
  · ext v
    show (-(0 : GlobalIdealFamily F)).finite v = (0 : HeightOneSpectrum (𝓞 F) →₀ ℤ) v
    simp
  · funext w
    show (-(0 : GlobalIdealFamily F)).infinite w = (0 : NumberField.InfinitePlace F → ℝ) w
    simp

/-- The explicit signed divisor of the principal divisor `div(f)`: the finite
support `nu_v(f)` and the archimedean `-log (w f)` coordinates. -/
def principalDivisorExplicit (f : Fˣ) : SourceModelBackend.ExplicitDivisor F :=
  (principalDivisorFinite f, fun w => principalDivisorInfinite f w)

/-- The explicit principal divisor is realized by the actual number-field
principal divisor family of `Example36NumberFieldPlaceData`. -/
theorem principalDivisorExplicit_eq_family (f : Fˣ) :
    principalDivisorExplicit f =
      ((sourceModelPrincipalDivisor (numberFieldGlobalPlaceData (F := F))
          numberFieldGlobalPlaceData_hasFiniteSupport f).finite,
        fun w => (sourceModelPrincipalDivisor (numberFieldGlobalPlaceData (F := F))
          numberFieldGlobalPlaceData_hasFiniteSupport f).infinite w) := by
  rw [principalDivisor_numberField]
  rfl

/-- **Agreement of `Object.divisorClass` with `div(f)`.**  For the backend
object attached to the principal-divisor family, the realized divisor class
maps under the group-completion equivalence to `-div(f)`; this is exactly the
frozen sign convention `d = -delta` applied to `div(f)`. -/
theorem backendObject_principalDivisor_divisorClass (f : Fˣ) :
    SourceModelBackend.coneGrothendieckEquiv (F := F)
        ((backendObject (sourceModelPrincipalDivisor (numberFieldGlobalPlaceData (F := F))
          numberFieldGlobalPlaceData_hasFiniteSupport f)).divisorClass) =
      -principalDivisorExplicit f := by
  rw [coneGrothendieckEquiv_backendObject_divisorClass]
  apply Prod.ext
  · ext v
    show -((sourceModelPrincipalDivisor (numberFieldGlobalPlaceData (F := F))
        numberFieldGlobalPlaceData_hasFiniteSupport f).finite) v =
      -((principalDivisorFinite f)) v
    rw [principalDivisor_numberField]
  · funext w
    show -((sourceModelPrincipalDivisor (numberFieldGlobalPlaceData (F := F))
        numberFieldGlobalPlaceData_hasFiniteSupport f).infinite) w =
      -((principalDivisorInfinite f) w)
    rw [principalDivisor_numberField]

/-! ## 4. Naturality under a faithful domain isomorphism -/

variable {F' : Type u} [Field F'] [NumberField F']

def unitsMapOfRingEquiv (sigma : F ≃+* F') : Fˣ ≃* F'ˣ :=
  Units.mapEquiv sigma.toMulEquiv

@[simp]
theorem unitsMapOfRingEquiv_apply_coe (sigma : F ≃+* F') (f : Fˣ) :
    (unitsMapOfRingEquiv sigma f : F') = sigma (f : F) := rfl

@[simp]
theorem unitsMapOfRingEquiv_mul (sigma : F ≃+* F') (f g : Fˣ) :
    unitsMapOfRingEquiv sigma (f * g) =
      unitsMapOfRingEquiv sigma f * unitsMapOfRingEquiv sigma g :=
  map_mul _ f g

def unitQuotientMapOfRingEquiv (sigma : F ≃+* F') (U : Subgroup Fˣ)
    (U' : Subgroup F'ˣ) (hU : U ≤ U'.comap (unitsMapOfRingEquiv sigma).toMonoidHom) :
    Fˣ ⧸ U →* F'ˣ ⧸ U' :=
  QuotientGroup.map U U' (unitsMapOfRingEquiv sigma).toMonoidHom hU

theorem unitQuotientMapOfRingEquiv_mk (sigma : F ≃+* F') (U : Subgroup Fˣ)
    (U' : Subgroup F'ˣ) (hU : U ≤ U'.comap (unitsMapOfRingEquiv sigma).toMonoidHom)
    (f : Fˣ) :
    unitQuotientMapOfRingEquiv sigma U U' hU (QuotientGroup.mk f) =
      QuotientGroup.mk (unitsMapOfRingEquiv sigma f) :=
  QuotientGroup.map_mk U U' _ hU f

theorem principalIdeal_map_span (phi : 𝓞 F →+* 𝓞 F') (a : 𝓞 F) :
    Ideal.map phi (Ideal.span {a}) = Ideal.span {phi a} := by
  rw [Ideal.map_span]
  simp

theorem principalIdeal_mul_pow_le_map (phi : 𝓞 F →+* 𝓞 F')
    {x y z : 𝓞 F} (n : ℕ)
    (h : Ideal.span {x} * Ideal.span {y} ^ n ≤ Ideal.span {z}) :
    Ideal.span {phi x} * Ideal.span {phi y} ^ n ≤ Ideal.span {phi z} := by
  have hmap := Ideal.map_mono (f := phi) h
  rwa [Ideal.map_mul, Ideal.map_pow, principalIdeal_map_span,
    principalIdeal_map_span, principalIdeal_map_span] at hmap

structure FaithfulDomainIsomorphism (D : GlobalPlaceData F)
    (D' : GlobalPlaceData F') where
  fieldEquiv : F ≃+* F'
  finitePlaceMap : HeightOneSpectrum (𝓞 F) → HeightOneSpectrum (𝓞 F')
  infinitePlaceMap : NumberField.InfinitePlace F → NumberField.InfinitePlace F'
  finiteDelta_preserved : ∀ (f : Fˣ) (v : HeightOneSpectrum (𝓞 F)),
    D'.finiteDelta (unitsMapOfRingEquiv fieldEquiv f) (finitePlaceMap v) =
      D.finiteDelta f v
  infiniteDelta_preserved : ∀ (f : Fˣ) (w : NumberField.InfinitePlace F),
    D'.infiniteDelta (unitsMapOfRingEquiv fieldEquiv f) (infinitePlaceMap w) =
      D.infiniteDelta f w

namespace FaithfulDomainIsomorphism

variable {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
  (sigma : FaithfulDomainIsomorphism D D')

theorem principalDivisor_finite_commutes (hD : D.HasFiniteSupport)
    (hD' : D'.HasFiniteSupport) (f : Fˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (sourceModelPrincipalDivisor D' hD' (unitsMapOfRingEquiv sigma.fieldEquiv f)).finite
        (sigma.finitePlaceMap v) =
      (sourceModelPrincipalDivisor D hD f).finite v := by
  rw [sourceModelPrincipalDivisor_finite_apply, sourceModelPrincipalDivisor_finite_apply,
    sigma.finiteDelta_preserved]

theorem principalDivisor_infinite_commutes (hD : D.HasFiniteSupport)
    (hD' : D'.HasFiniteSupport) (f : Fˣ) (w : NumberField.InfinitePlace F) :
    (sourceModelPrincipalDivisor D' hD' (unitsMapOfRingEquiv sigma.fieldEquiv f)).infinite
        (sigma.infinitePlaceMap w) =
      (sourceModelPrincipalDivisor D hD f).infinite w := by
  rw [sourceModelPrincipalDivisor_infinite_apply, sourceModelPrincipalDivisor_infinite_apply,
    sigma.infiniteDelta_preserved]

theorem arithmeticDivisor_principal_finite_commutes (hD : D.HasFiniteSupport)
    (hD' : D'.HasFiniteSupport) (f : Fˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (arithmeticDivisor (sourceModelPrincipalDivisor D' hD'
        (unitsMapOfRingEquiv sigma.fieldEquiv f))).finite (sigma.finitePlaceMap v) =
      (arithmeticDivisor (sourceModelPrincipalDivisor D hD f)).finite v := by
  rw [arithmeticDivisor_finite, arithmeticDivisor_finite,
    sigma.principalDivisor_finite_commutes hD hD']

end FaithfulDomainIsomorphism

/-! ## 5. Recorded same-field ramification (interface; `e = 1` only for actual data)

**Review N3.**  This interface keeps the field `F` fixed and quantifies the
recorded law over all `f : F^x`.  For the actual normalized integer valuations
the target value map is surjective onto `Z`
(`Example36ValueGroupRationality.finitePlaceValueExponent_surjective`), so
choosing `f` with `nu'_{v'}(f) = 1` forces `e = 1`:
`1 = e * nu_v(f)` with `nu_v(f)` an integer.  Hence the same-field interface
cannot express genuine `e > 1` ramification for the actual data; it is
`e = 1`-only.  The general-`e` statement is cross-field and is carried by
`PlaceLocalizationTransport` (`Example36FrobenioidTransport`), with the
corrected law `nu_w(phi f) = e_w * nu_v(f)` proved in
`Example36ValueMapTransportCorrection`.  The structure below is kept unchanged
for the conditional law; see
`Example36ValueMapTransportCorrection.globalPlaceRamification_ramificationIndex_eq_one`
for the exclusion theorem. -/

/-- Recorded same-field ramification data for the finite place `v` of `F` and
the place `v'`: a positive natural number `e` and the recorded law
`D'.finiteDelta f v' = e * D.finiteDelta f v` for every global unit `f`.

Per review N3 this interface is `e = 1`-only for actual normalized
valuations (the target value map is surjective onto `Z`); general `e` needs
the cross-field `PlaceLocalizationTransport` interface. -/
structure GlobalPlaceRamification (D D' : GlobalPlaceData F)
    (v v' : HeightOneSpectrum (𝓞 F)) where
  ramificationIndex : ℕ
  ramificationIndex_pos : 0 < ramificationIndex
  ramification : ∀ f : Fˣ,
    D'.finiteDelta f v' = (ramificationIndex : ℤ) * D.finiteDelta f v

namespace GlobalPlaceRamification

variable {D D' : GlobalPlaceData F}
  {v v' : HeightOneSpectrum (𝓞 F)}
  (ram : GlobalPlaceRamification D D' v v')

theorem principalDivisor_finite (hD : D.HasFiniteSupport)
    (hD' : D'.HasFiniteSupport) (f : Fˣ) :
    (sourceModelPrincipalDivisor D' hD' f).finite v' =
      (ram.ramificationIndex : ℤ) * (sourceModelPrincipalDivisor D hD f).finite v := by
  rw [sourceModelPrincipalDivisor_finite_apply, sourceModelPrincipalDivisor_finite_apply,
    GlobalPlaceRamification.ramification ram]

theorem arithmeticDivisor_principal_finite (hD : D.HasFiniteSupport)
    (hD' : D'.HasFiniteSupport) (f : Fˣ) :
    (arithmeticDivisor (sourceModelPrincipalDivisor D' hD' f)).finite v' =
      (ram.ramificationIndex : ℤ) *
        (arithmeticDivisor (sourceModelPrincipalDivisor D hD f)).finite v := by
  rw [arithmeticDivisor_finite, arithmeticDivisor_finite,
    ram.principalDivisor_finite hD hD']
  rw [mul_neg]

theorem nonnegative_iff (ram : GlobalPlaceRamification D D' v v') (f : Fˣ) :
    0 ≤ D.finiteDelta f v ↔ 0 ≤ D'.finiteDelta f v' := by
  rw [GlobalPlaceRamification.ramification ram]
  have he : (0 : ℤ) < (ram.ramificationIndex : ℤ) := by
    exact_mod_cast ram.ramificationIndex_pos
  constructor
  · intro h
    exact mul_nonneg he.le h
  · intro h
    exact (mul_nonneg_iff_of_pos_left he).mp h

theorem eq_of_index_eq_one (h : ram.ramificationIndex = 1) (f : Fˣ) :
    D'.finiteDelta f v' = D.finiteDelta f v := by
  rw [GlobalPlaceRamification.ramification ram, h]
  norm_num

theorem index_eq_one_of_eq {f : Fˣ} (hf : D.finiteDelta f v ≠ 0)
    (h : D'.finiteDelta f v' = D.finiteDelta f v) :
    ram.ramificationIndex = 1 := by
  have hscale : (ram.ramificationIndex : ℤ) * D.finiteDelta f v =
      D.finiteDelta f v :=
    (GlobalPlaceRamification.ramification ram f).symm.trans h
  have hzero : ((ram.ramificationIndex : ℤ) - 1) * D.finiteDelta f v = 0 := by
    calc ((ram.ramificationIndex : ℤ) - 1) * D.finiteDelta f v
        = (ram.ramificationIndex : ℤ) * D.finiteDelta f v - D.finiteDelta f v :=
          by ring
      _ = 0 := by rw [hscale]; ring
  have hcoef : (ram.ramificationIndex : ℤ) - 1 = 0 := by
    rcases mul_eq_zero.mp hzero with hzero' | hzero'
    · exact hzero'
    · exact absurd hzero' hf
  omega

end GlobalPlaceRamification

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
