import LeanFormal.IUT.IUTII.Frobenioid.Example36ValueMapTransport
import LeanFormal.IUT.IUTII.Frobenioid.Example36ValueGroupRationality
import LeanFormal.IUT.IUTII.Frobenioid.Example36TransportInstance

/-!
# Review N3 correction: same-field ramification is trivial; corrected cross-field ramified transport

This module records the correction of the independent review N3.

## Finding

The frozen same-field interface `GlobalPlaceRamification`
(`Example36SourceModelDivisor`, section "Recorded DVR-extension ramification")
fixes one field `F`, quantifies over all `f : F^x`, and records the law
`nu'_{v'}(f) = e * nu_v(f)` with a natural-number `e`.  For the *actual
normalized integer valuations* of the tree this interface cannot express
`e > 1`: the target value map is surjective onto `Z`
(`finitePlaceValueExponent_surjective`, in
`Example36ValueGroupRationality`), so choose `f` with `nu'_{v'}(f) = 1`;
then `1 = e * nu_v(f)` with `nu_v(f)` an integer, which forces `e = 1`.
Consequently the general-`e` statements of
`Example36ValueMapTransport` section 4, read as actual same-field
ramification data, are vacuous: their only consistent instance is `e = 1`.
The old file's proofs remain valid (they are conditional on the recorded law),
but the *claim* that they express genuine ramification is wrong; that path is
marked `e = 1`-only / superseded in `Example36ValueMapTransport`, and in the
interface docstring of `Example36SourceModelDivisor`.

## Correction

1. `globalPlaceRamification_ramificationIndex_eq_one_of_surjective` and its
   actual instance `globalPlaceRamification_ramificationIndex_eq_one` prove
   the exclusion: the same-field interface with surjective target value group
   forces `e = 1`; the old ramified laws are restated as unramified identities
   (`sameField_ramified_valueMap_eq`, `sameField_ramifiedValueKernel_realification_eq`).
2. `PlaceLocalizationTransport.finiteDelta_transport_of_normalized` and its
   actual instance `numberField_finitePlaceValueExponent_transport` prove the
   corrected *cross-field* statement
   `nu_w(phi f) = e_w * nu_v(f)`, with the genuine `phi`-induced unit map
   `unitsMapOfRingHom T.fieldMap` (no identity unit map); the concrete
   number-field extension instance is
   `numberFieldExtension_finitePlaceValueExponent_transport`.
3. The transported K1/K2 data are restated for the cross-field case with the
   `phi`-induced unit map: the value law
   `transportedFiniteValueMap_eq`, the target kernel realification on the image
   (`transportedFiniteValueKernel_realification_image`), the `e`-th power
   degree law (`transportedFiniteValueKernel_degree_image`), the scaled source
   kernel `transportedScaledSourceValueKernel` with its target and power laws,
   and the link layer `transportedRamifiedValueLink` whose `modMap` is the
   genuine `phi`-induced unit map and whose `MODMap` is an explicitly
   supplied retraction `psi` with the explicit `MOD` value law (no identity
   substitution, no fake carrier).

The strict `Q(sqrt 2)/Q`, `e = 2` example of
`Example36QuadraticTransportStrict`/`Example36TransportInstance` is untouched
and is a genuine cross-field `PlaceLocalizationTransport` instance; it is not
an instance of the same-field interface.

## Boundary

No source claim is made: this module corrects the formal interface usage only.
No theta-pilot, q-pilot, Tate or Hodge-theater claim.  The cross-field link
layer below is stated for the actual `PlaceLocalizationTransport` data; its
`MODMap` retraction and `MOD` value law are explicit hypotheses, not proved
for every extension.
-/

set_option linter.unusedVariables false

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open IsDedekindDomain NumberField
open scoped NumberField

universe u

variable {F : Type u} [Field F] [NumberField F]
variable {F' : Type u} [Field F'] [NumberField F']

/-! ## 1. The same-field interface forces `e = 1` -/

/-- An integer with positive factor multiplying to one is one: used for the
same-field ramification exclusion. -/
theorem int_eq_one_of_pos_mul_eq_one {e k : ℤ} (he : 0 < e) (h : e * k = 1) :
    e = 1 := by
  have hk : 0 < k := by
    by_contra hk
    have hk0 : k ≤ 0 := by omega
    have hle : e * k ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt he) hk0
    omega
  by_contra he1
  have he2 : 2 ≤ e := by omega
  have hk1 : 1 ≤ k := by omega
  have hprod : 2 * 1 ≤ e * k :=
    mul_le_mul he2 hk1 (by norm_num) (le_of_lt he)
  omega

/-- **The same-field ramification exclusion, interface form.**  If the target
finite coordinate is surjective onto the integers, then the recorded
same-field ramification index is one.  In particular the same-field
`GlobalPlaceRamification` interface cannot express `e > 1` for actual
normalized integer valuations. -/
theorem globalPlaceRamification_ramificationIndex_eq_one_of_surjective
    {D D' : GlobalPlaceData F} {v v' : HeightOneSpectrum (𝓞 F)}
    (hsurj : Function.Surjective (fun f : Fˣ => D'.finiteDelta f v'))
    (ram : GlobalPlaceRamification D D' v v') :
    ram.ramificationIndex = 1 := by
  obtain ⟨f, hf⟩ := hsurj 1
  have hf' : D'.finiteDelta f v' = 1 := hf
  have hram := GlobalPlaceRamification.ramification ram f
  rw [hf'] at hram
  have he : (ram.ramificationIndex : ℤ) = 1 :=
    int_eq_one_of_pos_mul_eq_one (by exact_mod_cast ram.ramificationIndex_pos)
      hram.symm
  exact_mod_cast he

/-- **The actual same-field ramification exclusion.**  For the actual
number-field place data the target value map is surjective onto `Z`
(`finitePlaceValueExponent_surjective`, `Example36ValueGroupRationality`), so
any recorded same-field `GlobalPlaceRamification` has ramification index one. -/
theorem globalPlaceRamification_ramificationIndex_eq_one
    {v v' : HeightOneSpectrum (𝓞 F)}
    (ram : GlobalPlaceRamification (numberFieldGlobalPlaceData (F := F))
      (numberFieldGlobalPlaceData (F := F)) v v') :
    ram.ramificationIndex = 1 := by
  refine globalPlaceRamification_ramificationIndex_eq_one_of_surjective
    (D := numberFieldGlobalPlaceData (F := F))
    (D' := numberFieldGlobalPlaceData (F := F)) ?_ ram
  intro n
  obtain ⟨f, hf⟩ := finitePlaceValueExponent_surjective v' n
  refine ⟨f, ?_⟩
  change numberFieldGlobalPlaceData.finiteDelta f v' = n
  rw [numberFieldGlobalPlaceData_finiteDelta]
  exact hf

/-- Corollary: no actual same-field ramification datum has index greater than
one. -/
theorem globalPlaceRamification_not_general_ramification
    {v v' : HeightOneSpectrum (𝓞 F)}
    (ram : GlobalPlaceRamification (numberFieldGlobalPlaceData (F := F))
      (numberFieldGlobalPlaceData (F := F)) v v') :
    ¬ (1 < ram.ramificationIndex) := by
  intro h
  have hone := globalPlaceRamification_ramificationIndex_eq_one ram
  omega

/-- The old same-field `nu' = e * nu` law, restated under the forced
`e = 1`: it is the unramified identity of the actual finite value maps. -/
theorem sameField_ramified_valueMap_eq
    (ram : GlobalPlaceRamification (numberFieldGlobalPlaceData (F := F))
      (numberFieldGlobalPlaceData (F := F)) v v') (f : Fˣ) :
    finiteValueMap (numberFieldGlobalPlaceData (F := F)) v' f =
      finiteValueMap (numberFieldGlobalPlaceData (F := F)) v f := by
  rw [finiteValueMap_ramified ram f,
    globalPlaceRamification_ramificationIndex_eq_one ram]
  norm_num

/-- The old same-field ramified value kernel, restated under the forced
`e = 1`: its realification is the source value kernel realification. -/
theorem sameField_ramifiedValueKernel_realification_eq
    (ram : GlobalPlaceRamification (numberFieldGlobalPlaceData (F := F))
      (numberFieldGlobalPlaceData (F := F)) v v') (f : Fˣ) :
    (ramifiedValueKernel ram).realification f =
      (finiteValueKernel (numberFieldGlobalPlaceData (F := F)) v).realification f := by
  rw [ramifiedValueKernel_realification_apply,
    globalPlaceRamification_ramificationIndex_eq_one ram]
  norm_num

/-! ## 2. The corrected cross-field ramified value transport -/

/-- **Corrected cross-field ramification law, interface form.**  Along a
`PlaceLocalizationTransport` with both place data normalized to the actual
finite-place exponents, the value of the `phi`-induced image of a global unit
at an upper place is the ramification index times the value at the restricted
place.  The unit map is the genuine `unitsMapOfRingHom T.fieldMap`. -/
theorem PlaceLocalizationTransport.finiteDelta_transport_of_normalized
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D')
    (hD : ∀ (f : Fˣ) (v : HeightOneSpectrum (𝓞 F)),
      D.finiteDelta f v = finitePlaceValueExponent v f)
    (hD' : ∀ (f : F'ˣ) (w : HeightOneSpectrum (𝓞 F')),
      D'.finiteDelta f w = finitePlaceValueExponent w f)
    (f : Fˣ) (w : HeightOneSpectrum (𝓞 F')) :
    finitePlaceValueExponent w (unitsMapOfRingHom T.fieldMap f) =
      (T.ramificationIndex w : ℤ) *
        finitePlaceValueExponent (T.finitePlaceRestriction w) f := by
  rw [← hD' (unitsMapOfRingHom T.fieldMap f) w,
    ← hD f (T.finitePlaceRestriction w)]
  exact T.finiteDelta_transport f w

/-- **Corrected cross-field ramification law for the actual number-field place
data**: `nu_w(phi f) = e_w * nu_v(f)` for the `phi`-induced unit map. -/
theorem numberField_finitePlaceValueExponent_transport
    (T : PlaceLocalizationTransport (numberFieldGlobalPlaceData (F := F))
      (numberFieldGlobalPlaceData (F := F'))) (f : Fˣ)
    (w : HeightOneSpectrum (𝓞 F')) :
    finitePlaceValueExponent w (unitsMapOfRingHom T.fieldMap f) =
      (T.ramificationIndex w : ℤ) *
        finitePlaceValueExponent (T.finitePlaceRestriction w) f :=
  PlaceLocalizationTransport.finiteDelta_transport_of_normalized T
    (fun f v => numberFieldGlobalPlaceData_finiteDelta f v)
    (fun f w => numberFieldGlobalPlaceData_finiteDelta f w) f w

/-- The corrected cross-field law for the concrete generic number-field
extension transport `PlaceLocalizationTransport.ofNumberFieldExtension`
(`fieldMap = algebraMap F F'`, genuine upper place restriction and genuine
ideal ramification index). -/
theorem numberFieldExtension_finitePlaceValueExponent_transport
    [Algebra F F'] [FiniteDimensional F F'] (f : Fˣ) (w : HeightOneSpectrum (𝓞 F')) :
    finitePlaceValueExponent w (unitsMapOfRingHom (algebraMap F F') f) =
      (ramificationIndexAtUpperPlace (F := F) w : ℤ) *
        finitePlaceValueExponent (upperPlaceRestriction (F := F) w) f := by
  have h := numberField_finitePlaceValueExponent_transport
    (PlaceLocalizationTransport.ofNumberFieldExtension (F := F) (F' := F')) f w
  simpa only [PlaceLocalizationTransport.ofNumberFieldExtension] using h

/-- The cross-field value-map law in real form: the transported finite value
map is the ramification-index multiple of the restricted source value map. -/
theorem transportedFiniteValueMap_eq
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (f : Fˣ)
    (w : HeightOneSpectrum (𝓞 F')) :
    finiteValueMap D' w (unitsMapOfRingHom T.fieldMap f) =
      (T.ramificationIndex w : ℝ) *
        finiteValueMap D (T.finitePlaceRestriction w) f := by
  rw [finiteValueMap_apply, finiteValueMap_apply, T.finiteDelta_transport f w]
  push_cast
  ring

/-- **Transported K1/K2 value-kernel realification on the `phi`-image**: the
target kernel realification of `phi f` is the ramification multiple of the
source kernel realification at the restricted place. -/
theorem transportedFiniteValueKernel_realification_image
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (f : Fˣ)
    (w : HeightOneSpectrum (𝓞 F')) :
    (finiteValueKernel D' w).realification (unitsMapOfRingHom T.fieldMap f) =
      (T.ramificationIndex w : ℝ) *
        (finiteValueKernel D (T.finitePlaceRestriction w)).realification f := by
  rw [finiteValueKernel_realification_apply, finiteValueKernel_realification_apply,
    T.finiteDelta_transport f w]
  push_cast
  ring

/-- **Transported K1/K2 value-kernel degree on the `phi`-image**: the target
degree of `phi f` is the `e`-th power of the source degree. -/
theorem transportedFiniteValueKernel_degree_image
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (f : Fˣ)
    (w : HeightOneSpectrum (𝓞 F')) :
    (finiteValueKernel D' w).degree (unitsMapOfRingHom T.fieldMap f) =
      (finiteValueKernel D (T.finitePlaceRestriction w)).degree f ^
        T.ramificationIndex w := by
  rw [finiteValueKernel_degree_apply, finiteValueKernel_degree_apply,
    T.finiteDelta_transport f w]
  push_cast
  rw [← nsmul_eq_mul, ofAdd_nsmul]

/-- The `e`-scaled source K1/K2 value kernel of the cross-field transport, on
the global units of the base field. -/
def transportedScaledSourceValueKernel
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F')) :
    LeanFormal.IUT.FrobenioidValueKernel Fˣ :=
  LeanFormal.IUT.K1K2Realization.frobenioidValueKernelOfValueMap
    (fun f => (T.ramificationIndex w : ℝ) *
      finiteValueMap D (T.finitePlaceRestriction w) f)
    (fun f g => by rw [finiteValueMap_mul]; ring)
    (by rw [finiteValueMap_one]; ring)
    id (fun _ => rfl)

/-- The scaled source kernel realification is the ramification multiple of the
source value. -/
@[simp]
theorem transportedScaledSourceValueKernel_realification_apply
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F')) (f : Fˣ) :
    (transportedScaledSourceValueKernel T w).realification f =
      (T.ramificationIndex w : ℝ) *
        finiteValueMap D (T.finitePlaceRestriction w) f :=
  rfl

/-- The scaled source kernel degree is `ofAdd` of the ramification multiple of
the source value. -/
@[simp]
theorem transportedScaledSourceValueKernel_degree_apply
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F')) (f : Fˣ) :
    (transportedScaledSourceValueKernel T w).degree f =
      Multiplicative.ofAdd ((T.ramificationIndex w : ℝ) *
        finiteValueMap D (T.finitePlaceRestriction w) f) :=
  rfl

/-- **Cross-field version of the ramified kernel target identity**: the scaled
source kernel realification equals the target kernel realification on the
`phi`-image. -/
theorem transportedScaledSourceValueKernel_realification_eq_target
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F')) (f : Fˣ) :
    (transportedScaledSourceValueKernel T w).realification f =
      (finiteValueKernel D' w).realification (unitsMapOfRingHom T.fieldMap f) := by
  rw [transportedScaledSourceValueKernel_realification_apply,
    finiteValueKernel_realification_apply]
  rw [show ((D'.finiteDelta (unitsMapOfRingHom T.fieldMap f) w : ℤ) : ℝ) =
      finiteValueMap D' w (unitsMapOfRingHom T.fieldMap f) from
    (finiteValueMap_apply D' w _).symm]
  exact (transportedFiniteValueMap_eq T f w).symm

/-- **Degree power law of the cross-field ramified transport**: the scaled
source kernel degree is the `e`-th power of the source kernel degree. -/
theorem transportedScaledSourceValueKernel_degree_eq_pow
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F')) (f : Fˣ) :
    (transportedScaledSourceValueKernel T w).degree f =
      (finiteValueKernel D (T.finitePlaceRestriction w)).degree f ^
        T.ramificationIndex w := by
  rw [transportedScaledSourceValueKernel_degree_apply,
    finiteValueKernel_degree_apply]
  change Multiplicative.ofAdd
      ((T.ramificationIndex w : ℝ) *
        finiteValueMap D (T.finitePlaceRestriction w) f) =
    Multiplicative.ofAdd (finiteValueMap D (T.finitePlaceRestriction w) f) ^
      T.ramificationIndex w
  rw [← nsmul_eq_mul, ofAdd_nsmul]

/-- **The corrected cross-field K1/K2 link layer.**  The local kernel is the
`e`-scaled source kernel, the global kernel is the target kernel at the upper
place, and the `modMap` is the genuine `phi`-induced unit map
`unitsMapOfRingHom T.fieldMap` (never the identity).  The `MODMap` is an
explicitly supplied retraction `psi` with the explicit `MOD` value law
`hMOD`; these are hypotheses, not faked data. -/
def transportedRamifiedValueLink
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F'))
    (psi : F'ˣ →* Fˣ)
    (hpsi : ∀ f : Fˣ, psi (unitsMapOfRingHom T.fieldMap f) = f)
    (hMOD : ∀ g : F'ˣ, (T.ramificationIndex w : ℝ) *
      finiteValueMap D (T.finitePlaceRestriction w) (psi g) =
        finiteValueMap D' w g) :
    LeanFormal.IUT.PrimeStripFrobenioidLinkLayer Fˣ F'ˣ :=
  LeanFormal.IUT.K1K2Realization.primeStripFrobenioidLinkLayerOfValueMaps
    (fun f => (T.ramificationIndex w : ℝ) *
      finiteValueMap D (T.finitePlaceRestriction w) f)
    (fun f g => by rw [finiteValueMap_mul]; ring)
    (by rw [finiteValueMap_one]; ring)
    id (fun _ => rfl)
    (finiteValueMap D' w) (fun f g => finiteValueMap_mul D' w f g)
    (finiteValueMap_one D' w) id (fun _ => rfl)
    (unitsMapOfRingHom T.fieldMap)
    (fun f => transportedFiniteValueMap_eq T f w)
    (fun _ => rfl)
    psi hMOD (fun _ => rfl)

/-- The local kernel of the cross-field link is the scaled source kernel. -/
@[simp]
theorem transportedRamifiedValueLink_localFrobenioid
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F'))
    (psi : F'ˣ →* Fˣ)
    (hpsi : ∀ f : Fˣ, psi (unitsMapOfRingHom T.fieldMap f) = f)
    (hMOD : ∀ g : F'ˣ, (T.ramificationIndex w : ℝ) *
      finiteValueMap D (T.finitePlaceRestriction w) (psi g) =
        finiteValueMap D' w g) :
    (transportedRamifiedValueLink T w psi hpsi hMOD).localFrobenioid =
      transportedScaledSourceValueKernel T w :=
  rfl

/-- The global kernel of the cross-field link is the target kernel. -/
@[simp]
theorem transportedRamifiedValueLink_globalFrobenioid
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F'))
    (psi : F'ˣ →* Fˣ)
    (hpsi : ∀ f : Fˣ, psi (unitsMapOfRingHom T.fieldMap f) = f)
    (hMOD : ∀ g : F'ˣ, (T.ramificationIndex w : ℝ) *
      finiteValueMap D (T.finitePlaceRestriction w) (psi g) =
        finiteValueMap D' w g) :
    (transportedRamifiedValueLink T w psi hpsi hMOD).globalFrobenioid =
      finiteValueKernel D' w :=
  rfl

/-- The `modMap` of the cross-field link is the genuine `phi`-induced unit map
(no identity unit map). -/
theorem transportedRamifiedValueLink_modMap
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F'))
    (psi : F'ˣ →* Fˣ)
    (hpsi : ∀ f : Fˣ, psi (unitsMapOfRingHom T.fieldMap f) = f)
    (hMOD : ∀ g : F'ˣ, (T.ramificationIndex w : ℝ) *
      finiteValueMap D (T.finitePlaceRestriction w) (psi g) =
        finiteValueMap D' w g) :
    (transportedRamifiedValueLink T w psi hpsi hMOD).modMap =
      unitsMapOfRingHom T.fieldMap :=
  rfl

/-- The `MODMap` of the cross-field link is the supplied retraction. -/
theorem transportedRamifiedValueLink_MODMap
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F'))
    (psi : F'ˣ →* Fˣ)
    (hpsi : ∀ f : Fˣ, psi (unitsMapOfRingHom T.fieldMap f) = f)
    (hMOD : ∀ g : F'ˣ, (T.ramificationIndex w : ℝ) *
      finiteValueMap D (T.finitePlaceRestriction w) (psi g) =
        finiteValueMap D' w g) :
    (transportedRamifiedValueLink T w psi hpsi hMOD).MODMap = psi :=
  rfl

/-- The `MODMap` is a retraction of the `phi`-induced unit map on global
units. -/
theorem transportedRamifiedValueLink_MOD_modMap
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F'))
    (psi : F'ˣ →* Fˣ)
    (hpsi : ∀ f : Fˣ, psi (unitsMapOfRingHom T.fieldMap f) = f)
    (hMOD : ∀ g : F'ˣ, (T.ramificationIndex w : ℝ) *
      finiteValueMap D (T.finitePlaceRestriction w) (psi g) =
        finiteValueMap D' w g) (f : Fˣ) :
    (transportedRamifiedValueLink T w psi hpsi hMOD).MODMap
        ((transportedRamifiedValueLink T w psi hpsi hMOD).modMap f) = f :=
  hpsi f

/-- **mod realification of the cross-field link**: the target realification of
the `phi`-image is the ramification multiple of the source realification. -/
theorem transportedRamifiedValueLink_mod_realification
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F'))
    (psi : F'ˣ →* Fˣ)
    (hpsi : ∀ f : Fˣ, psi (unitsMapOfRingHom T.fieldMap f) = f)
    (hMOD : ∀ g : F'ˣ, (T.ramificationIndex w : ℝ) *
      finiteValueMap D (T.finitePlaceRestriction w) (psi g) =
        finiteValueMap D' w g) (f : Fˣ) :
    (transportedRamifiedValueLink T w psi hpsi hMOD).globalFrobenioid.realification
        ((transportedRamifiedValueLink T w psi hpsi hMOD).modMap f) =
      (T.ramificationIndex w : ℝ) *
        (D.finiteDelta f (T.finitePlaceRestriction w) : ℝ) := by
  rw [LeanFormal.IUT.PrimeStripFrobenioidLinkLayer.mod_realification,
    transportedRamifiedValueLink_localFrobenioid,
    transportedScaledSourceValueKernel_realification_apply, finiteValueMap_apply]

/-- **MOD realification of the cross-field link**: the source scaled
realification of the inverse-transported unit is the target realification. -/
theorem transportedRamifiedValueLink_MOD_realification
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F'))
    (psi : F'ˣ →* Fˣ)
    (hpsi : ∀ f : Fˣ, psi (unitsMapOfRingHom T.fieldMap f) = f)
    (hMOD : ∀ g : F'ˣ, (T.ramificationIndex w : ℝ) *
      finiteValueMap D (T.finitePlaceRestriction w) (psi g) =
        finiteValueMap D' w g) (g : F'ˣ) :
    (transportedRamifiedValueLink T w psi hpsi hMOD).localFrobenioid.realification
        ((transportedRamifiedValueLink T w psi hpsi hMOD).MODMap g) =
      (finiteValueKernel D' w).realification g := by
  rw [LeanFormal.IUT.PrimeStripFrobenioidLinkLayer.MOD_realification,
    transportedRamifiedValueLink_globalFrobenioid]

/-! ## 3. Bundled correction statement -/

/-- **Review N3 correction, bundled**: the actual same-field interface has only
`e = 1` instances, and the genuine general-`e` statement lives on the
cross-field `PlaceLocalizationTransport` with the `phi`-induced unit map. -/
theorem reviewN3_correction_summary :
    (∀ {v v' : HeightOneSpectrum (𝓞 F)}
        (ram : GlobalPlaceRamification (numberFieldGlobalPlaceData (F := F))
          (numberFieldGlobalPlaceData (F := F)) v v'),
        ram.ramificationIndex = 1) ∧
      (∀ (T : PlaceLocalizationTransport (numberFieldGlobalPlaceData (F := F))
          (numberFieldGlobalPlaceData (F := F'))) (f : Fˣ)
          (w : HeightOneSpectrum (𝓞 F')),
        finitePlaceValueExponent w (unitsMapOfRingHom T.fieldMap f) =
          (T.ramificationIndex w : ℤ) *
            finitePlaceValueExponent (T.finitePlaceRestriction w) f) :=
  ⟨fun _ => globalPlaceRamification_ramificationIndex_eq_one _,
    fun T f w => numberField_finitePlaceValueExponent_transport T f w⟩

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
