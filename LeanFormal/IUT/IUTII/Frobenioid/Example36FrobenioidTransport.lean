/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanFormal.IUT.IUTII.Frobenioid.Example36GlobalPlaceData
import LeanFormal.IUT.IUTII.Frobenioid.Example36NumberFieldPlaceData
import LeanFormal.IUT.IUTII.Frobenioid.Example36GlobalIdealFamily
import LeanFormal.IUT.IUTII.Frobenioid.Example36GlobalIdealFamilyActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36LocalIdealValuation
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceModelBackend
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceModelDivisor
import LeanFormal.IUT.IUTII.Frobenioid.Example36NumberFieldPlaceCompletionBridge
import Mathlib.Tactic

/-!
# Transport of the Example 3.6 ideal-family and backend data along a place localization

This module transports the value-coordinate data of IUT III Example 3.6 along a
finite-place extension/localization, modelled abstractly as a place-restriction
datum: a ring map `F →+* F'` (the extension of global units), a restriction map
from the finite places of `F'` to the finite places of `F`, a restriction map
on the archimedean places, an explicitly recorded ramification index function,
and the delta/principal-value transport laws.

The mathematical meaning of the fields is the classical local extension law
`nu_w(f) = e(w) * nu_{rho w}(f)` for global units `f` of `F`, together with the
archimedean normalization `-log|f|_w = -log|f|_{rho w}` and the compatibility of
the effective cones.  The ramification index is a field of the datum: it is
recorded as a hypothesis and is never derived from the place data.  No identity
transport is substituted for a localization: all transport theorems are stated
for an arbitrary datum, and `PlaceLocalizationTransport.ofPlacewiseRamification`
assembles the datum from recorded single-place ramification data of
`GlobalPlaceRamification` (the value-group normalization case).  The
faithful-domain-isomorphism case corresponds to ramification index one, with the
place restriction maps supplied in the inverse direction.

## Contents

* `PlaceLocalizationTransport`: the restriction/ramification datum (Section 2),
  with the construction `ofPlacewiseRamification` from recorded single-place
  ramification data.
* Transport of the value coordinates, of global ideal-family objects, and of
  principal divisors (Sections 3 and 4).
* Transport of the morphisms of the global ideal-family category: degrees,
  multipliers, the integrality conditions, effective parts, the balance
  equation, and isomorphism preservation (Section 5).
* Transport of the effective-divisor cone and of the explicit divisor group,
  together with the induced map on the Grothendieck group and the
  `Object.divisorClass` agreement with `d(J) = -delta(J)` (Section 6).
* At the actual number-field place data: the transported places where the local
  principal value equals the completion valuation exponent
  `completionValuationExponent`, and preservation of the concrete finite- and
  archimedean-place integrality conditions (Section 7).

## Boundary

The transport datum is abstract: this file does not instantiate it with a
concrete ramified number-field extension.  Its fields are exactly the local
extension laws, with the ramification index recorded explicitly.  The torsor
presentation layer and the source Hodge-theater/theta layers are not treated
here.  All results are proved theorems of the transported value-coordinate
ideal-family category and its backend representation.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open scoped NumberField
open IsDedekindDomain NumberField

universe u

variable {F : Type u} [Field F] [NumberField F]
variable {F' : Type u} [Field F'] [NumberField F']

/-! ## 1. Global units along a ring homomorphism -/

/-- The induced monoid homomorphism on global units of a ring homomorphism of
number fields.  For a localization/extension map `F →+* F'` this is the map
sending a global unit of `F` to its image in the extension. -/
def unitsMapOfRingHom (phi : F →+* F') : Fˣ →* F'ˣ :=
  Units.map phi.toMonoidHom

@[simp]
theorem unitsMapOfRingHom_apply_coe (phi : F →+* F') (f : Fˣ) :
    (unitsMapOfRingHom phi f : F') = phi (f : F) :=
  rfl

@[simp]
theorem unitsMapOfRingHom_one (phi : F →+* F') :
    unitsMapOfRingHom phi (1 : Fˣ) = 1 :=
  map_one (unitsMapOfRingHom phi)

@[simp]
theorem unitsMapOfRingHom_mul (phi : F →+* F') (f g : Fˣ) :
    unitsMapOfRingHom phi (f * g) = unitsMapOfRingHom phi f * unitsMapOfRingHom phi g :=
  map_mul (unitsMapOfRingHom phi) f g

@[simp]
theorem unitsMapOfRingHom_pow (phi : F →+* F') (f : Fˣ) (n : ℕ) :
    unitsMapOfRingHom phi (f ^ n) = unitsMapOfRingHom phi f ^ n :=
  map_pow (unitsMapOfRingHom phi) f n

@[simp]
theorem unitsMapOfRingHom_id (f : Fˣ) :
    unitsMapOfRingHom (RingHom.id F) f = f := by
  ext
  rfl

/-! ## 2. The place-localization transport datum -/

/-- The datum of a transport of the place-indexed value data of IUT III
Example 3.6 along a finite-place extension/localization.

The fields are the classical extension laws: `fieldMap` is the map on global
units, `finitePlaceRestriction`/`infinitePlaceRestriction` are the place
restriction maps, `ramificationIndex` is the recorded ramification index
`e(w)`, and `finiteDelta_transport` states the local law
`nu_w(f) = e(w) * nu_{rho w}(f)`.  The effective-cone fields state that the
`e(w)`-scaled source integral cone is contained in the target integral cone.
The ramification index is an explicit field: no unramified or identity
assumption is built in. -/
structure PlaceLocalizationTransport (D : GlobalPlaceData F) (D' : GlobalPlaceData F') where
  /-- The map on global units induced by the localization/extension. -/
  fieldMap : F →+* F'
  /-- The restriction map on finite places. -/
  finitePlaceRestriction : HeightOneSpectrum (𝓞 F') → HeightOneSpectrum (𝓞 F)
  /-- The restriction map on archimedean places. -/
  infinitePlaceRestriction : NumberField.InfinitePlace F' → NumberField.InfinitePlace F
  /-- Only finitely many finite places of `F'` lie above a finite set of places of `F`. -/
  finitePlaceRestriction_finite :
    ∀ s : Finset (HeightOneSpectrum (𝓞 F)),
      {w : HeightOneSpectrum (𝓞 F') | finitePlaceRestriction w ∈ s}.Finite
  /-- The ramification index at each finite place of the extension. -/
  ramificationIndex : HeightOneSpectrum (𝓞 F') → ℕ
  /-- The ramification index is positive. -/
  ramificationIndex_pos : ∀ w, 0 < ramificationIndex w
  /-- The finite-place local extension law
  `nu_w(f) = e(w) * nu_{rho w}(f)` for global units. -/
  finiteDelta_transport : ∀ (f : Fˣ) (w : HeightOneSpectrum (𝓞 F')),
    D'.finiteDelta (unitsMapOfRingHom fieldMap f) w =
      (ramificationIndex w : ℤ) * D.finiteDelta f (finitePlaceRestriction w)
  /-- The archimedean local extension law: the normalized absolute value of a
  global unit at a place of the extension equals the value at the restricted
  place. -/
  infiniteDelta_transport : ∀ (f : Fˣ) (w : NumberField.InfinitePlace F'),
    D'.infiniteDelta (unitsMapOfRingHom fieldMap f) w =
      D.infiniteDelta f (infinitePlaceRestriction w)
  /-- The effective finite-place cone of the extension contains the
  `e(w)`-scaled source cone. -/
  finiteCone_transport : ∀ (w : HeightOneSpectrum (𝓞 F')) {a : ℤ},
    a ∈ (D.finiteValue (finitePlaceRestriction w)).cone →
      ramificationIndex w • a ∈ (D'.finiteValue w).cone
  /-- The effective archimedean cone of the extension contains the source cone
  at the restricted place. -/
  infiniteCone_transport : ∀ (w : NumberField.InfinitePlace F') {a : ℝ},
    a ∈ (D.infiniteValue (infinitePlaceRestriction w)).cone →
      a ∈ (D'.infiniteValue w).cone

namespace PlaceLocalizationTransport

variable {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
variable (T : PlaceLocalizationTransport D D')

/-- The finite-place local extension law, in the additive value-group form used
by the local inclusion conditions. -/
theorem deltaAdd_transport (f : Fˣ) (w : HeightOneSpectrum (𝓞 F')) :
    (D'.finiteValue w).deltaAdd (unitsMapOfRingHom T.fieldMap f) =
      (T.ramificationIndex w : ℤ) * (D.finiteValue (T.finitePlaceRestriction w)).deltaAdd f :=
  T.finiteDelta_transport f w

/-- The archimedean local extension law, in the additive value-group form. -/
theorem deltaAdd_transport_infinite (f : Fˣ) (w : NumberField.InfinitePlace F') :
    (D'.infiniteValue w).deltaAdd (unitsMapOfRingHom T.fieldMap f) =
      (D.infiniteValue (T.infinitePlaceRestriction w)).deltaAdd f :=
  T.infiniteDelta_transport f w

/-- The ramification index as a positive integer. -/
theorem ramificationIndex_pos_int (w : HeightOneSpectrum (𝓞 F')) :
    (0 : ℤ) < (T.ramificationIndex w : ℤ) := by
  exact_mod_cast T.ramificationIndex_pos w

/-- The ramification index is nonzero. -/
theorem ramificationIndex_ne_zero (w : HeightOneSpectrum (𝓞 F')) :
    (T.ramificationIndex w : ℤ) ≠ 0 :=
  (T.ramificationIndex_pos_int w).ne'

/-! ## 3. Transport of the finite value coordinates -/

/-- The transport of a finitely supported finite-place coordinate along the
place restriction, scaled by the ramification index:
`(transportFinsupp a) w = e(w) * a (rho w)`.

The support of the transported coordinate is the preimage under the restriction
map of the support of `a`, which is finite by the extension datum. -/
def transportFinsupp (a : HeightOneSpectrum (𝓞 F) →₀ ℤ) :
    HeightOneSpectrum (𝓞 F') →₀ ℤ :=
  Finsupp.onFinset (T.finitePlaceRestriction_finite a.support).toFinset
    (fun w => (T.ramificationIndex w : ℤ) * a (T.finitePlaceRestriction w))
    (fun w hw => by
      have ha : a (T.finitePlaceRestriction w) ≠ 0 := by
        intro h
        exact hw (by rw [h, mul_zero])
      exact (T.finitePlaceRestriction_finite a.support).mem_toFinset.mpr
        (Finsupp.mem_support_iff.mpr ha))

@[simp]
theorem transportFinsupp_apply (a : HeightOneSpectrum (𝓞 F) →₀ ℤ)
    (w : HeightOneSpectrum (𝓞 F')) :
    T.transportFinsupp a w =
      (T.ramificationIndex w : ℤ) * a (T.finitePlaceRestriction w) :=
  Finsupp.onFinset_apply

@[simp]
theorem transportFinsupp_zero :
    T.transportFinsupp (0 : HeightOneSpectrum (𝓞 F) →₀ ℤ) = 0 := by
  ext w
  simp

theorem transportFinsupp_add (a b : HeightOneSpectrum (𝓞 F) →₀ ℤ) :
    T.transportFinsupp (a + b) = T.transportFinsupp a + T.transportFinsupp b := by
  ext w
  simp only [transportFinsupp_apply, Finsupp.add_apply, mul_add]

/-! ## 4. Transport of global ideal-family objects and principal divisors -/

/-- The transport of a global ideal-family object: the finite coordinates are
restricted and scaled by the ramification indices, the archimedean coordinates
are restricted. -/
def transportObject (J : GlobalIdealFamily F) : GlobalIdealFamily F' where
  finite := T.transportFinsupp J.finite
  infinite := fun w => J.infinite (T.infinitePlaceRestriction w)

@[simp]
theorem transportObject_finite_apply (J : GlobalIdealFamily F)
    (w : HeightOneSpectrum (𝓞 F')) :
    (T.transportObject J).finite w =
      (T.ramificationIndex w : ℤ) * J.finite (T.finitePlaceRestriction w) :=
  T.transportFinsupp_apply J.finite w

@[simp]
theorem transportObject_infinite_apply (J : GlobalIdealFamily F)
    (w : NumberField.InfinitePlace F') :
    (T.transportObject J).infinite w = J.infinite (T.infinitePlaceRestriction w) :=
  rfl

@[simp]
theorem transportObject_zero :
    T.transportObject (0 : GlobalIdealFamily F) = 0 := by
  apply GlobalIdealFamily.ext
  · ext w
    simp only [transportObject_finite_apply, GlobalIdealFamily.zero_finite,
      Finsupp.zero_apply, mul_zero]
  · funext w
    simp only [transportObject_infinite_apply, GlobalIdealFamily.zero_infinite]

theorem transportObject_add (J₁ J₂ : GlobalIdealFamily F) :
    T.transportObject (J₁ + J₂) = T.transportObject J₁ + T.transportObject J₂ := by
  apply GlobalIdealFamily.ext
  · ext w
    simp only [transportObject_finite_apply, GlobalIdealFamily.add_finite,
      Finsupp.add_apply, mul_add]
  · funext w
    simp only [transportObject_infinite_apply, GlobalIdealFamily.add_infinite]

/-- **Principal-divisor transport.**  The principal divisor of a global unit is
transported to the principal divisor of the image unit, with the recorded
ramification scaling. -/
theorem transportObject_sourceModelPrincipalDivisor (hD : D.HasFiniteSupport)
    (hD' : D'.HasFiniteSupport) (f : Fˣ) :
    T.transportObject (sourceModelPrincipalDivisor D hD f) =
      sourceModelPrincipalDivisor D' hD' (unitsMapOfRingHom T.fieldMap f) := by
  apply GlobalIdealFamily.ext
  · ext w
    rw [transportObject_finite_apply, sourceModelPrincipalDivisor_finite_apply,
      sourceModelPrincipalDivisor_finite_apply]
    exact (T.finiteDelta_transport f w).symm
  · funext w
    rw [transportObject_infinite_apply, sourceModelPrincipalDivisor_infinite_apply,
      sourceModelPrincipalDivisor_infinite_apply]
    exact (T.infiniteDelta_transport f w).symm


/-! ## 5. Transport of morphisms of the global ideal-family category -/

/-- The transport of a morphism of global ideal families: the degree is
unchanged, the multiplier is the image of the multiplier, and the integrality
conditions at the transported places are the scaled source conditions. -/
noncomputable def transportHom {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom D J₁ J₂) :
    GlobalIdealFamily.Hom D' (T.transportObject J₁) (T.transportObject J₂) where
  degree := h.degree
  positive_degree := h.positive_degree
  multiplier := unitsMapOfRingHom T.fieldMap h.multiplier
  finite_incl w := by
    have hinner : (D.finiteValue (T.finitePlaceRestriction w)).deltaAdd h.multiplier +
        h.degree • J₁.finite (T.finitePlaceRestriction w) -
        J₂.finite (T.finitePlaceRestriction w) ∈
        (D.finiteValue (T.finitePlaceRestriction w)).cone :=
      h.finite_incl (T.finitePlaceRestriction w)
    have hscaled := T.finiteCone_transport w hinner
    change (D'.finiteValue w).deltaAdd (unitsMapOfRingHom T.fieldMap h.multiplier) +
        h.degree • (T.transportObject J₁).finite w -
        (T.transportObject J₂).finite w ∈ (D'.finiteValue w).cone
    rw [T.deltaAdd_transport h.multiplier w, T.transportObject_finite_apply J₁ w,
      T.transportObject_finite_apply J₂ w]
    have harith :
        (T.ramificationIndex w : ℤ) *
            (D.finiteValue (T.finitePlaceRestriction w)).deltaAdd h.multiplier +
          h.degree • ((T.ramificationIndex w : ℤ) *
            J₁.finite (T.finitePlaceRestriction w)) -
          (T.ramificationIndex w : ℤ) * J₂.finite (T.finitePlaceRestriction w) =
        T.ramificationIndex w •
          ((D.finiteValue (T.finitePlaceRestriction w)).deltaAdd h.multiplier +
            h.degree • J₁.finite (T.finitePlaceRestriction w) -
            J₂.finite (T.finitePlaceRestriction w)) := by
      simp only [nsmul_eq_mul]
      ring
    rw [harith]
    exact hscaled
  infinite_incl w := by
    have hinner : (D.infiniteValue (T.infinitePlaceRestriction w)).deltaAdd h.multiplier +
        h.degree • J₁.infinite (T.infinitePlaceRestriction w) -
        J₂.infinite (T.infinitePlaceRestriction w) ∈
        (D.infiniteValue (T.infinitePlaceRestriction w)).cone :=
      h.infinite_incl (T.infinitePlaceRestriction w)
    have hscaled := T.infiniteCone_transport w hinner
    change (D'.infiniteValue w).deltaAdd (unitsMapOfRingHom T.fieldMap h.multiplier) +
        h.degree • (T.transportObject J₁).infinite w -
        (T.transportObject J₂).infinite w ∈ (D'.infiniteValue w).cone
    rw [T.deltaAdd_transport_infinite h.multiplier w]
    exact hscaled

@[simp]
theorem transportHom_degree {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom D J₁ J₂) :
    (T.transportHom h).degree = h.degree :=
  rfl

@[simp]
theorem transportHom_multiplier {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom D J₁ J₂) :
    (T.transportHom h).multiplier = unitsMapOfRingHom T.fieldMap h.multiplier :=
  rfl

/-- **Transport of the finite effective part.**  The effective part of the
transported morphism at a place of the extension is the ramification multiple of
the effective part of the source morphism at the restricted place. -/
theorem transportHom_effectiveFinite {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom D J₁ J₂) (w : HeightOneSpectrum (𝓞 F')) :
    (T.transportHom h).effectiveFinite w =
      (T.ramificationIndex w : ℤ) * h.effectiveFinite (T.finitePlaceRestriction w) := by
  unfold GlobalIdealFamily.Hom.effectiveFinite
  change D'.finiteDelta (unitsMapOfRingHom T.fieldMap h.multiplier) w +
      h.degree • (T.transportObject J₁).finite w -
      (T.transportObject J₂).finite w =
    (T.ramificationIndex w : ℤ) *
      (D.finiteDelta h.multiplier (T.finitePlaceRestriction w) +
        h.degree • J₁.finite (T.finitePlaceRestriction w) -
        J₂.finite (T.finitePlaceRestriction w))
  rw [T.finiteDelta_transport h.multiplier w, T.transportObject_finite_apply J₁ w,
    T.transportObject_finite_apply J₂ w]
  simp only [nsmul_eq_mul]
  ring

/-- **Transport of the archimedean effective part.**  At an archimedean place of
the extension the effective part is the source effective part at the restricted
place. -/
theorem transportHom_effectiveInfinite {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom D J₁ J₂) (w : NumberField.InfinitePlace F') :
    (T.transportHom h).effectiveInfinite w =
      h.effectiveInfinite (T.infinitePlaceRestriction w) := by
  unfold GlobalIdealFamily.Hom.effectiveInfinite
  change D'.infiniteDelta (unitsMapOfRingHom T.fieldMap h.multiplier) w +
      h.degree • (T.transportObject J₁).infinite w -
      (T.transportObject J₂).infinite w =
    D.infiniteDelta h.multiplier (T.infinitePlaceRestriction w) +
      h.degree • J₁.infinite (T.infinitePlaceRestriction w) -
      J₂.infinite (T.infinitePlaceRestriction w)
  rw [T.infiniteDelta_transport h.multiplier w, T.transportObject_infinite_apply J₁ w,
    T.transportObject_infinite_apply J₂ w]

/-- The transport preserves the identity morphisms. -/
@[simp]
theorem transportHom_id (J : GlobalIdealFamily F) :
    T.transportHom (GlobalIdealFamily.Hom.id (D := D) J) =
      GlobalIdealFamily.Hom.id (D := D') (T.transportObject J) := by
  apply GlobalIdealFamily.Hom.ext
  · rfl
  · exact map_one (unitsMapOfRingHom T.fieldMap)

/-- The transport preserves composition of morphisms. -/
theorem transportHom_comp {J₁ J₂ J₃ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom D J₁ J₂) (k : GlobalIdealFamily.Hom D J₂ J₃) :
    T.transportHom (GlobalIdealFamily.Hom.comp h k) =
      GlobalIdealFamily.Hom.comp (T.transportHom h) (T.transportHom k) := by
  apply GlobalIdealFamily.Hom.ext
  · rfl
  · change unitsMapOfRingHom T.fieldMap (k.multiplier * h.multiplier ^ k.degree) =
      unitsMapOfRingHom T.fieldMap k.multiplier *
        (unitsMapOfRingHom T.fieldMap h.multiplier) ^ k.degree
    rw [map_mul, map_pow]

/-- The transport preserves isomorphisms of the global ideal-family category:
a degree-one morphism with vanishing effective part stays of that form. -/
theorem transportHom_isIso {J₁ J₂ : GlobalIdealFamily F}
    {h : GlobalIdealFamily.Hom D J₁ J₂} (hiso : h.IsIso) :
    (T.transportHom h).IsIso := by
  rw [GlobalIdealFamily.Hom.isIso_iff] at hiso ⊢
  obtain ⟨hdeg, hpart⟩ := hiso
  refine ⟨hdeg, ?_⟩
  constructor
  · intro w
    rw [transportHom_effectiveFinite, hpart.1 (T.finitePlaceRestriction w), mul_zero]
  · intro w
    rw [transportHom_effectiveInfinite, hpart.2 (T.infinitePlaceRestriction w)]

/-- **Balance equation after transport, finite places.**  The transported
morphisms satisfy the backend balance identity at the places of the extension. -/
theorem transportHom_balance_finite {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom D J₁ J₂) (w : HeightOneSpectrum (𝓞 F')) :
    -(h.degree • (T.transportObject J₁).finite w) + (T.transportHom h).effectiveFinite w =
      -((T.transportObject J₂).finite w) +
        D'.finiteDelta (unitsMapOfRingHom T.fieldMap h.multiplier) w :=
  GlobalIdealFamily.Hom.balance_finite (T.transportHom h) w

/-- **Balance equation after transport, archimedean places.** -/
theorem transportHom_balance_infinite {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom D J₁ J₂) (w : NumberField.InfinitePlace F') :
    -(h.degree • (T.transportObject J₁).infinite w) + (T.transportHom h).effectiveInfinite w =
      -((T.transportObject J₂).infinite w) +
        D'.infiniteDelta (unitsMapOfRingHom T.fieldMap h.multiplier) w :=
  GlobalIdealFamily.Hom.balance_infinite (T.transportHom h) w

/-- **Scaled balance equation.**  The transported finite-place balance identity
is the ramification multiple of the source balance identity at the restricted
place. -/
theorem transportHom_balance_finite_scale {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom D J₁ J₂) (w : HeightOneSpectrum (𝓞 F')) :
    -(h.degree • (T.transportObject J₁).finite w) + (T.transportHom h).effectiveFinite w =
      T.ramificationIndex w •
        (-(h.degree • J₁.finite (T.finitePlaceRestriction w)) +
          h.effectiveFinite (T.finitePlaceRestriction w)) := by
  rw [transportHom_effectiveFinite, transportObject_finite_apply]
  simp only [nsmul_eq_mul]
  ring

/-- **Scaled balance equation, archimedean places.**  The transported
archimedean balance identity is the source balance identity at the restricted
place. -/
theorem transportHom_balance_infinite_scale {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom D J₁ J₂) (w : NumberField.InfinitePlace F') :
    -(h.degree • (T.transportObject J₁).infinite w) + (T.transportHom h).effectiveInfinite w =
      -(h.degree • J₁.infinite (T.infinitePlaceRestriction w)) +
        h.effectiveInfinite (T.infinitePlaceRestriction w) := by
  rw [transportHom_effectiveInfinite, transportObject_infinite_apply]


/-! ## 6. Transport of the effective cone, the explicit divisor group, and the
backend object -/

/-- The transport of a finitely supported nonnegative finite-place coordinate:
`(transportEffectiveFinsupp d) w = e(w) * d (rho w)`. -/
noncomputable def transportEffectiveFinsupp (d : HeightOneSpectrum (𝓞 F) →₀ ℕ) :
    HeightOneSpectrum (𝓞 F') →₀ ℕ :=
  Finsupp.onFinset (T.finitePlaceRestriction_finite d.support).toFinset
    (fun w => T.ramificationIndex w * d (T.finitePlaceRestriction w))
    (fun w hw => by
      have ha : d (T.finitePlaceRestriction w) ≠ 0 := by
        intro h
        exact hw (by rw [h, mul_zero])
      exact (T.finitePlaceRestriction_finite d.support).mem_toFinset.mpr
        (Finsupp.mem_support_iff.mpr ha))

@[simp]
theorem transportEffectiveFinsupp_apply (d : HeightOneSpectrum (𝓞 F) →₀ ℕ)
    (w : HeightOneSpectrum (𝓞 F')) :
    T.transportEffectiveFinsupp d w =
      T.ramificationIndex w * d (T.finitePlaceRestriction w) :=
  Finsupp.onFinset_apply

@[simp]
theorem transportEffectiveFinsupp_zero :
    T.transportEffectiveFinsupp (0 : HeightOneSpectrum (𝓞 F) →₀ ℕ) = 0 := by
  ext w
  simp

theorem transportEffectiveFinsupp_add (d₁ d₂ : HeightOneSpectrum (𝓞 F) →₀ ℕ) :
    T.transportEffectiveFinsupp (d₁ + d₂) =
      T.transportEffectiveFinsupp d₁ + T.transportEffectiveFinsupp d₂ := by
  ext w
  simp only [transportEffectiveFinsupp_apply, Finsupp.add_apply, mul_add]

/-- **Effective-cone transport.**  The effective divisor cone of the extension
receives the source cone: finite coordinates are restricted and scaled by the
ramification indices, archimedean coordinates are restricted. -/
noncomputable def transportEffective :
    SourceModelBackend.EffectiveDivisor F →+ SourceModelBackend.EffectiveDivisor F' where
  toFun d :=
    (T.transportEffectiveFinsupp d.1, fun w => d.2 (T.infinitePlaceRestriction w))
  map_zero' := by
    apply Prod.ext
    · exact T.transportEffectiveFinsupp_zero
    · funext w
      rfl
  map_add' d₁ d₂ := by
    apply Prod.ext
    · exact T.transportEffectiveFinsupp_add d₁.1 d₂.1
    · funext w
      rfl

@[simp]
theorem transportEffective_finite_apply (d : SourceModelBackend.EffectiveDivisor F)
    (w : HeightOneSpectrum (𝓞 F')) :
    (T.transportEffective d).1 w =
      T.ramificationIndex w * d.1 (T.finitePlaceRestriction w) :=
  T.transportEffectiveFinsupp_apply d.1 w

@[simp]
theorem transportEffective_infinite_apply (d : SourceModelBackend.EffectiveDivisor F)
    (w : NumberField.InfinitePlace F') :
    (T.transportEffective d).2 w = d.2 (T.infinitePlaceRestriction w) :=
  rfl

/-- **Explicit-divisor transport.**  The signed explicit divisor group of the
extension receives the source group: finite coordinates are restricted and
scaled by the ramification indices, archimedean coordinates are restricted. -/
noncomputable def transportExplicit :
    SourceModelBackend.ExplicitDivisor F →+ SourceModelBackend.ExplicitDivisor F' where
  toFun a := (T.transportFinsupp a.1, fun w => a.2 (T.infinitePlaceRestriction w))
  map_zero' := by
    apply Prod.ext
    · simp
    · funext w
      rfl
  map_add' a b := by
    apply Prod.ext
    · simpa using T.transportFinsupp_add a.1 b.1
    · funext w
      rfl

@[simp]
theorem transportExplicit_fst_apply (a : SourceModelBackend.ExplicitDivisor F)
    (w : HeightOneSpectrum (𝓞 F')) :
    (T.transportExplicit a).1 w =
      (T.ramificationIndex w : ℤ) * a.1 (T.finitePlaceRestriction w) :=
  T.transportFinsupp_apply a.1 w

@[simp]
theorem transportExplicit_snd_apply (a : SourceModelBackend.ExplicitDivisor F)
    (w : NumberField.InfinitePlace F') :
    (T.transportExplicit a).2 w = a.2 (T.infinitePlaceRestriction w) :=
  rfl

/-- The inclusion of the effective cone into the explicit divisor group commutes
with the transport. -/
theorem transportExplicit_effectiveToExplicit (m : SourceModelBackend.EffectiveDivisor F) :
    T.transportExplicit (SourceModelBackend.effectiveToExplicit m) =
      SourceModelBackend.effectiveToExplicit (T.transportEffective m) := by
  apply Prod.ext
  · ext w
    rw [transportExplicit_fst_apply, SourceModelBackend.effectiveToExplicit_fst_apply,
      SourceModelBackend.effectiveToExplicit_fst_apply, transportEffective_finite_apply,
      Nat.cast_mul]
  · funext w
    rw [transportExplicit_snd_apply, SourceModelBackend.effectiveToExplicit_snd_apply,
      SourceModelBackend.effectiveToExplicit_snd_apply, transportEffective_infinite_apply]

/-- The transport of explicit divisors preserves nonnegativity, i.e. it maps
effective (nonnegative) explicit divisors to effective ones. -/
theorem explicitNonneg_transportExplicit {a : SourceModelBackend.ExplicitDivisor F}
    (ha : SourceModelBackend.explicitNonneg a) :
    SourceModelBackend.explicitNonneg (T.transportExplicit a) := by
  refine ⟨fun w => ?_, fun w => ?_⟩
  · rw [transportExplicit_fst_apply]
    exact mul_nonneg (Int.natCast_nonneg (T.ramificationIndex w))
      (ha.1 (T.finitePlaceRestriction w))
  · rw [transportExplicit_snd_apply]
    exact ha.2 (T.infinitePlaceRestriction w)

/-- The arithmetic divisor `d(J) = -delta(J)` is transported to the arithmetic
divisor of the transported ideal family. -/
theorem transportExplicit_arithmeticDivisorExplicit (J : GlobalIdealFamily F) :
    T.transportExplicit (arithmeticDivisorExplicit J) =
      arithmeticDivisorExplicit (T.transportObject J) := by
  apply Prod.ext
  · ext w
    rw [transportExplicit_fst_apply]
    change (T.ramificationIndex w : ℤ) * (-(J.finite (T.finitePlaceRestriction w))) =
      -((T.transportObject J).finite w)
    rw [transportObject_finite_apply]
    ring
  · funext w
    rw [transportExplicit_snd_apply]
    change -(J.infinite (T.infinitePlaceRestriction w)) =
      -((T.transportObject J).infinite w)
    rw [transportObject_infinite_apply]

/-- **Induced map on the Grothendieck group of the effective cone.**  The
additive map on the effective cone of the transport induces a group
homomorphism of the group completions. -/
noncomputable def transportGrothendieck :
    Algebra.GrothendieckAddGroup (SourceModelBackend.EffectiveDivisor F) →+
      Algebra.GrothendieckAddGroup (SourceModelBackend.EffectiveDivisor F') :=
  Algebra.GrothendieckAddGroup.lift
    (Algebra.GrothendieckAddGroup.of.comp T.transportEffective)

/-- The induced group-completion map extends the effective-cone transport. -/
theorem transportGrothendieck_of (m : SourceModelBackend.EffectiveDivisor F) :
    T.transportGrothendieck (Algebra.GrothendieckAddGroup.of m) =
      Algebra.GrothendieckAddGroup.of (T.transportEffective m) := by
  let map := Algebra.GrothendieckAddGroup.of.comp T.transportEffective
  change (Algebra.GrothendieckAddGroup.lift map)
      (Algebra.GrothendieckAddGroup.of m) = map m
  change
    ((Algebra.GrothendieckAddGroup.lift map).comp
      Algebra.GrothendieckAddGroup.of) m = map m
  rw [← Algebra.GrothendieckAddGroup.lift_symm_apply]
  exact DFunLike.congr_fun
    (Equiv.symm_apply_apply Algebra.GrothendieckAddGroup.lift map) m

/-- **Group-completion square.**  The group-completion equivalence intertwines
the induced map on the group completion of the effective cone with the
transport of explicit divisors. -/
theorem coneGrothendieckEquiv_transportGrothendieck
    (x : Algebra.GrothendieckAddGroup (SourceModelBackend.EffectiveDivisor F)) :
    SourceModelBackend.coneGrothendieckEquiv (F := F') (T.transportGrothendieck x) =
      T.transportExplicit (SourceModelBackend.coneGrothendieckEquiv (F := F) x) := by
  let leftHom : Algebra.GrothendieckAddGroup (SourceModelBackend.EffectiveDivisor F) →+
      SourceModelBackend.ExplicitDivisor F' :=
    (SourceModelBackend.coneGrothendieckEquiv (F := F')).toAddMonoidHom.comp
      T.transportGrothendieck
  let rightHom : Algebra.GrothendieckAddGroup (SourceModelBackend.EffectiveDivisor F) →+
      SourceModelBackend.ExplicitDivisor F' :=
    T.transportExplicit.comp
      (SourceModelBackend.coneGrothendieckEquiv (F := F)).toAddMonoidHom
  have h : leftHom = rightHom := by
    apply Algebra.GrothendieckAddGroup.lift.symm.injective
    apply AddMonoidHom.ext
    intro m
    rw [Algebra.GrothendieckAddGroup.lift_symm_apply,
      Algebra.GrothendieckAddGroup.lift_symm_apply]
    change SourceModelBackend.coneGrothendieckEquiv (F := F')
        (T.transportGrothendieck (Algebra.GrothendieckAddGroup.of m)) =
      T.transportExplicit (SourceModelBackend.coneGrothendieckEquiv (F := F)
        (Algebra.GrothendieckAddGroup.of m))
    rw [T.transportGrothendieck_of m, SourceModelBackend.coneGrothendieckEquiv_of,
      SourceModelBackend.coneGrothendieckEquiv_of]
    exact (T.transportExplicit_effectiveToExplicit m).symm
  exact DFunLike.congr_fun h x

/-- **Backend divisor-class transport.**  The divisor class of the backend
object attached to an ideal family is transported to the divisor class of the
backend object attached to the transported ideal family. -/
theorem transportGrothendieck_backendObject_divisorClass (J : GlobalIdealFamily F) :
    T.transportGrothendieck (backendObject (F := F) J).divisorClass =
      (backendObject (F := F') (T.transportObject J)).divisorClass := by
  apply (SourceModelBackend.coneGrothendieckEquiv (F := F')).injective
  rw [T.coneGrothendieckEquiv_transportGrothendieck]
  rw [backendObject_divisorClass,
    backendObject_divisorClass]
  rw [SourceModelBackend.idealFamilyDivisorClass, SourceModelBackend.idealFamilyDivisorClass,
    AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  exact T.transportExplicit_arithmeticDivisorExplicit J

/-- **Agreement of the transported divisor class with `d(J)`.**  After the
group-completion equivalence, the transported backend divisor class is exactly
the transport of the arithmetic divisor `d(J) = -delta(J)`. -/
theorem coneGrothendieckEquiv_backendObject_transport (J : GlobalIdealFamily F) :
    SourceModelBackend.coneGrothendieckEquiv (F := F')
        ((backendObject (F := F') (T.transportObject J)).divisorClass) =
      T.transportExplicit (SourceModelBackend.coneGrothendieckEquiv (F := F)
        ((backendObject (F := F) J).divisorClass)) := by
  rw [coneGrothendieckEquiv_backendObject_divisorClass,
    coneGrothendieckEquiv_backendObject_divisorClass]
  exact (T.transportExplicit_arithmeticDivisorExplicit J).symm

/-- The base object of the backend is unchanged by the transport: both backend
objects live over the unique object of the bottom base category. -/
@[simp]
theorem backendObject_base_transport (J : GlobalIdealFamily F) :
    (backendObject (F := F') (T.transportObject J)).base =
      (backendObject (F := F) J).base :=
  rfl


/-- **Construction from recorded placewise ramification.**  A family of
recorded single-place ramification data `GlobalPlaceRamification D D' w w`,
together with the archimedean normalization and the effective-cone inclusions,
gives a place-localization transport of the value data.  This is the case of the
value-group normalization `nu'_w = e(w) * nu_w`; the ramification index is read
off the recorded data. -/
noncomputable def ofPlacewiseRamification {D D' : GlobalPlaceData F}
    (ram : ∀ w : HeightOneSpectrum (𝓞 F), GlobalPlaceRamification D D' w w)
    (hinfinite : ∀ (f : Fˣ) (w : NumberField.InfinitePlace F),
      D'.infiniteDelta f w = D.infiniteDelta f w)
    (hconeF : ∀ (w : HeightOneSpectrum (𝓞 F)) {a : ℤ},
      a ∈ (D.finiteValue w).cone → (ram w).ramificationIndex • a ∈ (D'.finiteValue w).cone)
    (hconeI : ∀ (w : NumberField.InfinitePlace F) {a : ℝ},
      a ∈ (D.infiniteValue w).cone → a ∈ (D'.infiniteValue w).cone) :
    PlaceLocalizationTransport D D' where
  fieldMap := RingHom.id F
  finitePlaceRestriction := id
  infinitePlaceRestriction := id
  finitePlaceRestriction_finite := fun s => by
    simp
  ramificationIndex := fun w => (ram w).ramificationIndex
  ramificationIndex_pos := fun w => (ram w).ramificationIndex_pos
  finiteDelta_transport := fun f w => by
    simpa using (ram w).ramification f
  infiniteDelta_transport := fun f w => by
    simpa using hinfinite f w
  finiteCone_transport := fun w => hconeF w
  infiniteCone_transport := fun w => hconeI w

end PlaceLocalizationTransport


/-! ## 7. Compatibility with the completion bridge at the transported places -/

section CompletionBridge

variable (T : PlaceLocalizationTransport
  (numberFieldGlobalPlaceData (F := F)) (numberFieldGlobalPlaceData (F := F')))

/-- **Completion-bridge compatibility, finite places.**  At a finite place of
the extension, the local principal value of the transported global unit equals
the completion valuation exponent of the embedded unit in the local completion,
and this value is the ramification multiple of the source finite coordinate. -/
theorem numberFieldTransport_finiteDelta_eq_completionValuationExponent
    (f : Fˣ) (w : HeightOneSpectrum (𝓞 F')) :
    completionValuationExponent w
        (Units.map (algebraMap F' (w.adicCompletion F')).toMonoidHom
          (unitsMapOfRingHom T.fieldMap f)) =
      (T.ramificationIndex w : ℤ) *
        (numberFieldGlobalPlaceData (F := F)).finiteDelta f (T.finitePlaceRestriction w) := by
  rw [← numberFieldGlobalPlaceData_finiteDelta_eq_completionValuationExponent
    (F := F') w (unitsMapOfRingHom T.fieldMap f)]
  exact T.finiteDelta_transport f w

/-- **Completion-bridge compatibility on both sides.**  The completion valuation
exponent at a transported place equals the ramification multiple of the
completion valuation exponent at the restricted source place. -/
theorem numberFieldTransport_completionValuationExponent_eq
    (f : Fˣ) (w : HeightOneSpectrum (𝓞 F')) :
    completionValuationExponent w
        (Units.map (algebraMap F' (w.adicCompletion F')).toMonoidHom
          (unitsMapOfRingHom T.fieldMap f)) =
      (T.ramificationIndex w : ℤ) *
        completionValuationExponent (T.finitePlaceRestriction w)
          (Units.map (algebraMap F
            ((T.finitePlaceRestriction w).adicCompletion F)).toMonoidHom f) := by
  rw [numberFieldTransport_finiteDelta_eq_completionValuationExponent T f w,
    numberFieldGlobalPlaceData_finiteDelta_eq_completionValuationExponent]

/-- **Finite-place integrality conditions are preserved by the transport.**  At
a finite place of the extension, the transported local morphism condition for
the scaled coordinates `e(w) * a_1`, `e(w) * a_2` is equivalent to the source
local morphism condition at the restricted place.  In particular the ideal
inclusion `(f) * (J_1)^n <= J_2` in value coordinates is preserved, since the
ramification index is positive. -/
theorem numberFieldFiniteLocalInclusion_transport_iff
    (w : HeightOneSpectrum (𝓞 F')) (n : ℕ) (f : Fˣ) (a₁ a₂ : ℤ) :
    (numberFieldFiniteLocalValueData w).localInclusion n
        (unitsMapOfRingHom T.fieldMap f)
        ((T.ramificationIndex w : ℤ) * a₁) ((T.ramificationIndex w : ℤ) * a₂) ↔
      (numberFieldFiniteLocalValueData (T.finitePlaceRestriction w)).localInclusion
        n f a₁ a₂ := by
  have hdelta : finitePlaceValueExponent w (unitsMapOfRingHom T.fieldMap f) =
      (T.ramificationIndex w : ℤ) *
        finitePlaceValueExponent (T.finitePlaceRestriction w) f :=
    T.finiteDelta_transport f w
  rw [numberFieldFiniteLocalInclusion_iff, numberFieldFiniteLocalInclusion_iff, hdelta]
  have harith :
      (T.ramificationIndex w : ℤ) *
          finitePlaceValueExponent (T.finitePlaceRestriction w) f +
        n * ((T.ramificationIndex w : ℤ) * a₁) -
        (T.ramificationIndex w : ℤ) * a₂ =
      (T.ramificationIndex w : ℤ) *
        (finitePlaceValueExponent (T.finitePlaceRestriction w) f + n * a₁ - a₂) := by
    ring
  rw [harith]
  exact mul_nonneg_iff_of_pos_left (T.ramificationIndex_pos_int w)

/-- **Archimedean-place integrality conditions are preserved by the transport.**
At an archimedean place of the extension, the transported local morphism
condition is equivalent to the source condition at the restricted place. -/
theorem numberFieldInfiniteLocalInclusion_transport_iff
    (w : NumberField.InfinitePlace F') (n : ℕ) (f : Fˣ) (a₁ a₂ : ℝ) :
    (numberFieldInfiniteLocalValueData w).localInclusion n
        (unitsMapOfRingHom T.fieldMap f) a₁ a₂ ↔
      (numberFieldInfiniteLocalValueData (T.infinitePlaceRestriction w)).localInclusion
        n f a₁ a₂ := by
  have hdelta : archimedeanPlaceValue w (unitsMapOfRingHom T.fieldMap f) =
      archimedeanPlaceValue (T.infinitePlaceRestriction w) f :=
    T.infiniteDelta_transport f w
  rw [numberFieldInfiniteLocalInclusion_iff, numberFieldInfiniteLocalInclusion_iff, hdelta]

/-- **Principal-divisor transport at the actual number-field data.**  The
principal divisor of a global unit is carried to the principal divisor of the
image unit by the place-localization transport. -/
theorem numberFieldTransport_principalDivisor (f : Fˣ) :
    T.transportObject (principalDivisor f) =
      principalDivisor (unitsMapOfRingHom T.fieldMap f) := by
  rw [show principalDivisor f =
      sourceModelPrincipalDivisor (numberFieldGlobalPlaceData (F := F))
        numberFieldGlobalPlaceData_hasFiniteSupport f from
    (principalDivisor_numberField f).symm,
    show principalDivisor (unitsMapOfRingHom T.fieldMap f) =
      sourceModelPrincipalDivisor (numberFieldGlobalPlaceData (F := F'))
        numberFieldGlobalPlaceData_hasFiniteSupport (unitsMapOfRingHom T.fieldMap f) from
    (principalDivisor_numberField (unitsMapOfRingHom T.fieldMap f)).symm]
  exact T.transportObject_sourceModelPrincipalDivisor
    numberFieldGlobalPlaceData_hasFiniteSupport
    numberFieldGlobalPlaceData_hasFiniteSupport f

end CompletionBridge

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
