import LeanFormal.IUT.IUTII.Frobenioid.Example36ValueMapKernels
import LeanFormal.IUT.Audit.Status

/-!
# Prime-strip-layer transport of the actual `V_K`/`rho_v` value maps

Boundary (2), transport fragment.  This module lifts the value-map/link-layer
fragment of `Example36ValueMapKernels` (task-17) to an actual *place
transport*, and records exactly what is still missing for the source
prime-strip-layer `V_K` transport.

## What is constructed here

* **Place transport of value maps.**  A faithful domain isomorphism
  `sigma : FaithfulDomainIsomorphism D D'` acts on units by
  `placeUnitTransport sigma = unitsMapOfRingEquiv sigma.fieldEquiv`, and the
  actual value maps are compatible with it:
  `rho_{sigma v} o sigma = rho_v`, i.e.
  `finiteValueMap D' (sigma.finitePlaceMap v) (placeUnitTransport sigma f) =
  finiteValueMap D v f` (and the archimedean analogue).  This is not an
  identity-transport substitution: the unit transport is the genuine field ring
  equivalence, and the induced place maps are the recorded ones.
* **Transport of the K1/K2 reduced value kernels.**  The value kernel at the
  transported place is transported back through `placeUnitTransport`: its
  realification and degree readback commute with the place transport
  (`transportedFiniteValueKernel_realification`,
  `transportedFiniteValueKernel_degree`).
* **Transport of the K1/K2 link layer.**  `placeValueTransportLink sigma v` is
  the link layer between the source and transported target kernels; its
  `modMap` is the genuine unit transport, and the `mod`/`MOD`
  realification and degree readback commute with transport
  (`placeValueTransportLink_mod_realification`, `_MOD_realification`,
  `_mod_degree`, `_MOD_degree`).
* **Recorded same-field ramification transport (conditional, `e = 1` only for
  actual data; superseded for general `e`).**  Given an explicit
  `GlobalPlaceRamification D D' v v'` with ramification index `e` and the
  recorded law `nu' = e * nu`, the finite value map transforms as
  `rho' = e * rho` (`finiteValueMap_ramified`); the scaled value kernel and
  scaled link layer are constructed.  **Review N3 correction:** the same-field
  interface of `Example36SourceModelDivisor` quantifies over the units of one
  field, so for the actual normalized valuations (whose target value map is
  onto `Z`) it forces `e = 1`
  (`Example36ValueMapTransportCorrection.globalPlaceRamification_ramificationIndex_eq_one`).
  Read as actual same-field ramification data, this section is therefore
  `e = 1`-only; its `e > 1` statements are vacuous for the actual data and
  are *superseded* by the correct cross-field `PlaceLocalizationTransport`
  statement `nu_w(phi f) = e_w * nu_v(f)` with the `phi`-induced unit map in
  `Example36ValueMapTransportCorrection`.  The proofs below remain valid as
  conditional statements about the recorded interface; they are not a claim of
  genuine same-field ramification.
* **Backend agreement on the overlap.**  For the actual number-field place
  data, the K1/K2 value kernel realification of a global unit equals the
  finite coordinate of the backend `Input.divisor` / `globalModelDivisor`
  (`valueKernel_realification_eq_inputDivisor_finite`), and the transported
  kernel realification equals the source backend coordinate
  (`transportedValueKernel_realification_eq_inputDivisor`).

## What is recorded as missing (exact card)

The **actual `V_K` prime-strip-layer transport over the local completions**
and the **source vertical log-Kummer / log-shell carrier** are not constructed
in the tree and are not claimed here: the card
`LeanFormal.IUT.Audit.example36ValueMapPrimeStripTransport` records this as a
`VerificationStatus.interface` obligation.  The completion carrier itself
exists elsewhere; what is missing is the prime-strip-layer transport and the
source normalization identification `rho_v` (normalizing
`log|-mod(pv)|` to `1/[Kv:(Fmod)v] * logPhi(pv)`).

## Boundary

No theta-pilot, q-pilot, Tate, Hodge-theater or source-identification claim is
made.  Range/image statements are not used here.  The only hypothesis beyond
the existing structures is the recorded same-field ramification law, which is
carried by the `GlobalPlaceRamification` structure.  Per review N3 that
structure is `e = 1`-only for the actual normalized data (see
`Example36ValueMapTransportCorrection`); the general-`e` transport is
cross-field and is not attributed to it here.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open IsDedekindDomain NumberField
open scoped NumberField

universe u

variable {F : Type u} [Field F] [NumberField F]
variable {F' : Type u} [Field F'] [NumberField F']

variable {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}

/-! ## 1. Place transport of units and value maps -/

/-- The unit transport along a faithful domain isomorphism: the genuine ring
equivalence `sigma.fieldEquiv` on units. -/
def placeUnitTransport (sigma : FaithfulDomainIsomorphism D D') : Fˣ ≃* F'ˣ :=
  unitsMapOfRingEquiv sigma.fieldEquiv

/-- The transported unit is the ring-equivalence image of the unit. -/
@[simp]
theorem placeUnitTransport_apply_coe (sigma : FaithfulDomainIsomorphism D D')
    (f : Fˣ) :
    (placeUnitTransport sigma f : F') = sigma.fieldEquiv (f : F) :=
  rfl

/-- The unit transport is multiplicative. -/
theorem placeUnitTransport_mul (sigma : FaithfulDomainIsomorphism D D')
    (f g : Fˣ) :
    placeUnitTransport sigma (f * g) =
      placeUnitTransport sigma f * placeUnitTransport sigma g :=
  map_mul _ f g

/-- **Value-map compatibility on the transport**: `rho_{sigma v} o sigma = rho_v`
at a finite place. -/
theorem finiteValueMap_transport (sigma : FaithfulDomainIsomorphism D D')
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    finiteValueMap D' (sigma.finitePlaceMap v) (placeUnitTransport sigma f) =
      finiteValueMap D v f := by
  rw [finiteValueMap_apply, finiteValueMap_apply]
  change ((D'.finiteDelta (unitsMapOfRingEquiv sigma.fieldEquiv f)
    (sigma.finitePlaceMap v) : ℤ) : ℝ) = ((D.finiteDelta f v : ℤ) : ℝ)
  rw [sigma.finiteDelta_preserved]

/-- **Value-map compatibility on the transport** at an archimedean place. -/
theorem infiniteValueMap_transport (sigma : FaithfulDomainIsomorphism D D')
    (w : NumberField.InfinitePlace F) (f : Fˣ) :
    infiniteValueMap D' (sigma.infinitePlaceMap w) (placeUnitTransport sigma f) =
      infiniteValueMap D w f := by
  rw [infiniteValueMap_apply, infiniteValueMap_apply]
  change D'.infiniteDelta (unitsMapOfRingEquiv sigma.fieldEquiv f)
    (sigma.infinitePlaceMap w) = D.infiniteDelta f w
  rw [sigma.infiniteDelta_preserved]

/-- The unified place transport of the value map, finite or archimedean. -/
theorem placeValueMap_transport (sigma : FaithfulDomainIsomorphism D D')
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    finiteValueMap D' (sigma.finitePlaceMap v) (placeUnitTransport sigma f) =
        finiteValueMap D v f ∧
      ∀ w : NumberField.InfinitePlace F,
        infiniteValueMap D' (sigma.infinitePlaceMap w) (placeUnitTransport sigma f) =
          infiniteValueMap D w f :=
  ⟨finiteValueMap_transport sigma v f,
    fun w => infiniteValueMap_transport sigma w f⟩

/-! ## 2. Transport of the K1/K2 reduced value kernels -/

/-- The reduced value kernel at the transported finite place. -/
def transportedFiniteValueKernel (sigma : FaithfulDomainIsomorphism D D')
    (v : HeightOneSpectrum (𝓞 F)) : LeanFormal.IUT.FrobenioidValueKernel F'ˣ :=
  finiteValueKernel D' (sigma.finitePlaceMap v)

/-- The transported kernel is the value kernel of the target place data. -/
@[simp]
theorem transportedFiniteValueKernel_eq (sigma : FaithfulDomainIsomorphism D D')
    (v : HeightOneSpectrum (𝓞 F)) :
    transportedFiniteValueKernel sigma v = finiteValueKernel D' (sigma.finitePlaceMap v) :=
  rfl

/-- **Realification commutes with the place transport**: the realified value of
the transported unit is the realified value of the source unit. -/
theorem transportedFiniteValueKernel_realification
    (sigma : FaithfulDomainIsomorphism D D') (v : HeightOneSpectrum (𝓞 F))
    (f : Fˣ) :
    (transportedFiniteValueKernel sigma v).realification (placeUnitTransport sigma f) =
      (finiteValueKernel D v).realification f := by
  rw [transportedFiniteValueKernel_eq, finiteValueKernel_realification_apply,
    finiteValueKernel_realification_apply]
  exact finiteValueMap_transport sigma v f

/-- **Degree readback commutes with the place transport**. -/
theorem transportedFiniteValueKernel_degree
    (sigma : FaithfulDomainIsomorphism D D') (v : HeightOneSpectrum (𝓞 F))
    (f : Fˣ) :
    (transportedFiniteValueKernel sigma v).degree (placeUnitTransport sigma f) =
      (finiteValueKernel D v).degree f := by
  rw [transportedFiniteValueKernel_eq, finiteValueKernel_degree_apply,
    finiteValueKernel_degree_apply]
  congr 1
  simpa [finiteValueMap] using finiteValueMap_transport sigma v f

/-- In actual coordinates: the transported kernel's realified degree is the
source finite value. -/
theorem transportedFiniteValueKernel_degree_coe
    (sigma : FaithfulDomainIsomorphism D D') (v : HeightOneSpectrum (𝓞 F))
    (f : Fˣ) :
    ((transportedFiniteValueKernel sigma v).degree (placeUnitTransport sigma f) : ℝ) =
      (D.finiteDelta f v : ℝ) := by
  rw [FrobenioidValueKernel.degree_realification_at,
    transportedFiniteValueKernel_realification,
    finiteValueKernel_realification_apply]

/-- The transported kernel's degree is `Multiplicative.ofAdd` of the source
finite value. -/
theorem transportedFiniteValueKernel_degree_eq_ofAdd
    (sigma : FaithfulDomainIsomorphism D D') (v : HeightOneSpectrum (𝓞 F))
    (f : Fˣ) :
    (transportedFiniteValueKernel sigma v).degree (placeUnitTransport sigma f) =
      Multiplicative.ofAdd ((D.finiteDelta f v : ℝ)) := by
  rw [transportedFiniteValueKernel_eq, finiteValueKernel_degree_apply]
  congr 1
  simpa [finiteValueMap] using finiteValueMap_transport sigma v f

/-! ## 3. Transport of the K1/K2 link layer and its readback -/

/-- The K1/K2 link layer of the place transport: source kernel at `v`, target
kernel at `sigma v`, `modMap` the genuine unit transport. -/
def placeValueTransportLink (sigma : FaithfulDomainIsomorphism D D')
    (v : HeightOneSpectrum (𝓞 F)) : LeanFormal.IUT.PrimeStripFrobenioidLinkLayer Fˣ F'ˣ :=
  faithfulFiniteValueLink sigma v

/-- The local value kernel of the transport link is the source kernel. -/
@[simp]
theorem placeValueTransportLink_localFrobenioid
    (sigma : FaithfulDomainIsomorphism D D') (v : HeightOneSpectrum (𝓞 F)) :
    (placeValueTransportLink sigma v).localFrobenioid = finiteValueKernel D v :=
  rfl

/-- The global value kernel of the transport link is the transported kernel. -/
@[simp]
theorem placeValueTransportLink_globalFrobenioid
    (sigma : FaithfulDomainIsomorphism D D') (v : HeightOneSpectrum (𝓞 F)) :
    (placeValueTransportLink sigma v).globalFrobenioid =
      transportedFiniteValueKernel sigma v :=
  rfl

/-- The `modMap` of the transport link is the genuine unit transport. -/
theorem placeValueTransportLink_modMap (sigma : FaithfulDomainIsomorphism D D')
    (v : HeightOneSpectrum (𝓞 F)) :
    (placeValueTransportLink sigma v).modMap = placeUnitTransport sigma := by
  change (faithfulFiniteValueLink sigma v).modMap = unitsMapOfRingEquiv sigma.fieldEquiv
  exact faithfulFiniteValueLink_modMap sigma v

/-- The `MODMap` of the transport link is the inverse unit transport. -/
theorem placeValueTransportLink_MODMap (sigma : FaithfulDomainIsomorphism D D')
    (v : HeightOneSpectrum (𝓞 F)) :
    (placeValueTransportLink sigma v).MODMap = (placeUnitTransport sigma).symm := by
  change (faithfulFiniteValueLink sigma v).MODMap = (unitsMapOfRingEquiv sigma.fieldEquiv).symm
  exact faithfulFiniteValueLink_MODMap sigma v

/-- **mod realification commutes with transport**: the transported target value
of a unit is the source finite value. -/
theorem placeValueTransportLink_mod_realification
    (sigma : FaithfulDomainIsomorphism D D') (v : HeightOneSpectrum (𝓞 F))
    (f : Fˣ) :
    (placeValueTransportLink sigma v).globalFrobenioid.realification
        ((placeValueTransportLink sigma v).modMap f) =
      (D.finiteDelta f v : ℝ) :=
  faithfulFiniteValueLink_mod_realification sigma v f

/-- **MOD realification commutes with transport**: the target value of the
inverse-transported unit is the target finite value. -/
theorem placeValueTransportLink_MOD_realification
    (sigma : FaithfulDomainIsomorphism D D') (v : HeightOneSpectrum (𝓞 F))
    (g : F'ˣ) :
    (placeValueTransportLink sigma v).localFrobenioid.realification
        ((placeValueTransportLink sigma v).MODMap g) =
      (D'.finiteDelta g (sigma.finitePlaceMap v) : ℝ) :=
  faithfulFiniteValueLink_MOD_realification sigma v g

/-- **Degree readback of the transport link** in actual coordinates: the
transported degree is `ofAdd` of the source finite value. -/
theorem placeValueTransportLink_mod_degree
    (sigma : FaithfulDomainIsomorphism D D') (v : HeightOneSpectrum (𝓞 F))
    (f : Fˣ) :
    (placeValueTransportLink sigma v).globalFrobenioid.degree
        ((placeValueTransportLink sigma v).modMap f) =
      Multiplicative.ofAdd ((D.finiteDelta f v : ℝ)) :=
  faithfulFiniteValueLink_mod_degree sigma v f

/-- **Degree readback of the inverse transport** in actual coordinates. -/
theorem placeValueTransportLink_MOD_degree
    (sigma : FaithfulDomainIsomorphism D D') (v : HeightOneSpectrum (𝓞 F))
    (g : F'ˣ) :
    (placeValueTransportLink sigma v).localFrobenioid.degree
        ((placeValueTransportLink sigma v).MODMap g) =
      Multiplicative.ofAdd ((D'.finiteDelta g (sigma.finitePlaceMap v) : ℝ)) :=
  faithfulFiniteValueLink_MOD_degree sigma v g

/-! ## 4. Recorded same-field ramification transport (conditional; `e = 1` only for actual data)

**Review N3 correction.**  The interface `GlobalPlaceRamification D D' v v'`
lives over one field `F` and quantifies over all `f : F^x`.  For the actual
normalized integer valuations the target value map is onto `Z`
(`finitePlaceValueExponent_surjective`), so the recorded law
`nu' = e * nu` forces `e = 1`
(`globalPlaceRamification_ramificationIndex_eq_one` in
`Example36ValueMapTransportCorrection`).  The statements below are kept as
valid *conditional* consequences of the recorded interface, but they are
`e = 1`-only for the actual data; the general-`e` statements are superseded
by the cross-field `PlaceLocalizationTransport` transport in
`Example36ValueMapTransportCorrection`. -/

section Ramification

variable {D D' : GlobalPlaceData F} {v v' : HeightOneSpectrum (𝓞 F)}
variable (ram : GlobalPlaceRamification D D' v v')

/-- **The recorded ramified value-map law** `nu' = e * nu` as a real-valued
identity: `rho'` is `e` times `rho`, where `e` is the recorded ramification
index of the same-field interface.  This is a conditional statement about the
recorded interface; for the actual normalized data the interface forces
`e = 1` (review N3, `Example36ValueMapTransportCorrection`). -/
theorem finiteValueMap_ramified (f : Fˣ) :
    finiteValueMap D' v' f = (ram.ramificationIndex : ℝ) * finiteValueMap D v f := by
  rw [finiteValueMap_apply, finiteValueMap_apply, GlobalPlaceRamification.ramification ram]
  push_cast
  ring

/-- The `e`-scaled value map of the ramified place, read on the source data. -/
def ramifiedFiniteValueMap : Fˣ → ℝ :=
  fun f => (ram.ramificationIndex : ℝ) * finiteValueMap D v f

/-- The scaled value map is additive. -/
theorem ramifiedFiniteValueMap_mul (f g : Fˣ) :
    ramifiedFiniteValueMap ram (f * g) =
      ramifiedFiniteValueMap ram f + ramifiedFiniteValueMap ram g := by
  unfold ramifiedFiniteValueMap
  rw [finiteValueMap_mul]
  ring

/-- The scaled value map vanishes at `1`. -/
theorem ramifiedFiniteValueMap_one : ramifiedFiniteValueMap ram 1 = 0 := by
  unfold ramifiedFiniteValueMap
  rw [finiteValueMap_one]
  ring

/-- The reduced value kernel of the ramified value map. -/
def ramifiedValueKernel : LeanFormal.IUT.FrobenioidValueKernel Fˣ :=
  LeanFormal.IUT.K1K2Realization.frobenioidValueKernelOfValueMap
    (ramifiedFiniteValueMap ram) (fun f g => ramifiedFiniteValueMap_mul ram f g)
    (ramifiedFiniteValueMap_one ram) id (fun _ => rfl)

/-- The ramified kernel realification is the `e`-scaled finite value. -/
@[simp]
theorem ramifiedValueKernel_realification_apply (f : Fˣ) :
    (ramifiedValueKernel ram).realification f =
      (ram.ramificationIndex : ℝ) * finiteValueMap D v f :=
  rfl

/-- The ramified kernel degree is `ofAdd` of the `e`-scaled finite value. -/
@[simp]
theorem ramifiedValueKernel_degree_apply (f : Fˣ) :
    (ramifiedValueKernel ram).degree f =
      Multiplicative.ofAdd ((ram.ramificationIndex : ℝ) * finiteValueMap D v f) :=
  rfl

/-- **The ramified kernel agrees with the target kernel**: the recorded
ramification law identifies the `e`-scaled source value with the target value. -/
theorem ramifiedValueKernel_realification_eq_target (f : Fˣ) :
    (ramifiedValueKernel ram).realification f =
      (finiteValueKernel D' v').realification f := by
  rw [ramifiedValueKernel_realification_apply, finiteValueKernel_realification_apply,
    finiteValueMap_apply]
  rw [GlobalPlaceRamification.ramification ram]
  push_cast
  ring

/-- **Degree power law of the ramified transport**: the ramified degree is the
`e`-th power of the source degree in `Multiplicative Real`. -/
theorem ramifiedValueKernel_degree_eq_pow (f : Fˣ) :
    (ramifiedValueKernel ram).degree f =
      (finiteValueKernel D v).degree f ^ ram.ramificationIndex := by
  rw [ramifiedValueKernel_degree_apply, finiteValueKernel_degree_apply]
  change Multiplicative.ofAdd
      ((ram.ramificationIndex : ℝ) * finiteValueMap D v f) =
    Multiplicative.ofAdd (finiteValueMap D v f) ^ ram.ramificationIndex
  rw [← nsmul_eq_mul, ofAdd_nsmul]

/-- The same-field ramified link layer: the `e`-scaled source kernel is
linked to the target kernel at the place.  The unit map of this link is the
identity because the interface keeps the field fixed; the substantive data is
the recorded value rescaling `e`.  **Review N3:** for actual normalized
valuations the interface has no `e > 1` instances
(`globalPlaceRamification_ramificationIndex_eq_one`), so this construction is
`e = 1`-only and is superseded for general `e` by
`transportedRamifiedValueLink` in
`Example36ValueMapTransportCorrection`, whose `modMap` is the genuine
`phi`-induced unit map (no identity unit map). -/
def ramifiedValueTransportLink :
    LeanFormal.IUT.PrimeStripFrobenioidLinkLayer Fˣ Fˣ :=
  LeanFormal.IUT.K1K2Realization.primeStripFrobenioidLinkLayerOfValueMaps
    (ramifiedFiniteValueMap ram) (fun f g => ramifiedFiniteValueMap_mul ram f g)
    (ramifiedFiniteValueMap_one ram) id (fun _ => rfl)
    (finiteValueMap D' v') (fun f g => finiteValueMap_mul D' v' f g)
    (finiteValueMap_one D' v') id (fun _ => rfl)
    id (fun f => finiteValueMap_ramified ram f) (fun _ => rfl)
    id (fun f => (finiteValueMap_ramified ram f).symm) (fun _ => rfl)

/-- The local kernel of the ramified link is the ramified value kernel. -/
@[simp]
theorem ramifiedValueTransportLink_localFrobenioid :
    (ramifiedValueTransportLink ram).localFrobenioid = ramifiedValueKernel ram :=
  rfl

/-- The global kernel of the ramified link is the target value kernel. -/
@[simp]
theorem ramifiedValueTransportLink_globalFrobenioid :
    (ramifiedValueTransportLink ram).globalFrobenioid = finiteValueKernel D' v' :=
  rfl

/-- **mod realification of the ramified link**: the target realification of a
unit is the `e`-scaled source realification. -/
theorem ramifiedValueTransportLink_mod_realification (f : Fˣ) :
    (ramifiedValueTransportLink ram).globalFrobenioid.realification
        ((ramifiedValueTransportLink ram).modMap f) =
      (ram.ramificationIndex : ℝ) * (D.finiteDelta f v : ℝ) := by
  rw [LeanFormal.IUT.PrimeStripFrobenioidLinkLayer.mod_realification,
    ramifiedValueTransportLink_localFrobenioid,
    ramifiedValueKernel_realification_apply, finiteValueMap_apply]

/-- **MOD realification of the ramified link**: the source realification of an
inverse-transported unit is the target realification re-scaled exactly by the
recorded law. -/
theorem ramifiedValueTransportLink_MOD_realification (g : Fˣ) :
    (ramifiedValueTransportLink ram).localFrobenioid.realification
        ((ramifiedValueTransportLink ram).MODMap g) =
      (D'.finiteDelta g v' : ℝ) := by
  rw [LeanFormal.IUT.PrimeStripFrobenioidLinkLayer.MOD_realification,
    ramifiedValueTransportLink_globalFrobenioid,
    finiteValueKernel_realification_apply]

/-- The ramified transport reduces to the unramified value equality when the
recorded ramification index is one. -/
theorem ramifiedValueKernel_realification_eq_of_index_one
    (h : ram.ramificationIndex = 1) (f : Fˣ) :
    (ramifiedValueKernel ram).realification f =
      (D.finiteDelta f v : ℝ) := by
  rw [ramifiedValueKernel_realification_apply, h]
  simp

end Ramification

/-! ## 5. Agreement with the backend `Input.divisor` / `globalModelDivisor` -/

/-- The `divisor` of the actual number-field backend input at the unique base
object is the global model divisor. -/
theorem inputDivisor_apply (f : Fˣ) :
    (SourceModelBackend.numberFieldSourceModelInput (F := F)).divisor
        SourceModelBackend.bottomPoint (Additive.ofMul f) =
      SourceModelBackend.globalModelDivisor (F := F) (Additive.ofMul f) :=
  rfl

/-- Under the group-completion equivalence, the backend `Input.divisor` of a
global unit is the explicit principal divisor. -/
theorem coneGrothendieckEquiv_inputDivisor (f : Fˣ) :
    SourceModelBackend.coneGrothendieckEquiv
        ((SourceModelBackend.numberFieldSourceModelInput (F := F)).divisor
          SourceModelBackend.bottomPoint (Additive.ofMul f)) =
      principalDivisorExplicit (F := F) f := by
  rw [inputDivisor_apply]
  change SourceModelBackend.coneGrothendieckEquiv
      (SourceModelBackend.coneGrothendieckEquiv.symm
        (SourceModelBackend.principalDivisorExplicit (Additive.ofMul f))) =
    principalDivisorExplicit (F := F) f
  rw [AddEquiv.apply_symm_apply]
  rfl

/-- The finite coordinate of the backend `Input.divisor` is the corrected
classical exponent. -/
theorem inputDivisor_finite_apply_eq_classicalExponent (f : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    (SourceModelBackend.coneGrothendieckEquiv
        ((SourceModelBackend.numberFieldSourceModelInput (F := F)).divisor
          SourceModelBackend.bottomPoint (Additive.ofMul f))).1 v =
      finitePlaceValueExponent v f := by
  rw [coneGrothendieckEquiv_inputDivisor]
  change (principalDivisorFinite f) v = finitePlaceValueExponent v f
  exact principalDivisorFinite_apply f v

/-- The archimedean coordinate of the backend `Input.divisor` is `-log(w f)`. -/
theorem inputDivisor_infinite_apply_eq_neg_log (f : Fˣ)
    (w : NumberField.InfinitePlace F) :
    (SourceModelBackend.coneGrothendieckEquiv
        ((SourceModelBackend.numberFieldSourceModelInput (F := F)).divisor
          SourceModelBackend.bottomPoint (Additive.ofMul f))).2 w =
      -Real.log (w (f : F)) := by
  rw [coneGrothendieckEquiv_inputDivisor]
  change principalDivisorInfinite f w = -Real.log (w (f : F))
  exact principalDivisorInfinite_apply f w

/-- **Backend agreement on the overlap**: the realified K1/K2 value kernel of a
global unit is the finite coordinate of the backend
`Input.divisor`/`globalModelDivisor`. -/
theorem valueKernel_realification_eq_inputDivisor_finite (f : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    (finiteValueKernel (numberFieldGlobalPlaceData (F := F)) v).realification f =
      ((SourceModelBackend.coneGrothendieckEquiv
          ((SourceModelBackend.numberFieldSourceModelInput (F := F)).divisor
            SourceModelBackend.bottomPoint (Additive.ofMul f))).1 v : ℝ) := by
  rw [finiteValueKernel_realification_apply, inputDivisor_finite_apply_eq_classicalExponent,
    numberFieldGlobalPlaceData_finiteDelta]

/-- **Transport agrees with the backend on the overlap**: for a faithful domain
isomorphism between two actual number-field place data, the transported value
kernel realification of the image unit equals the source backend
`Input.divisor` finite coordinate. -/
theorem transportedValueKernel_realification_eq_inputDivisor
    (sigma : FaithfulDomainIsomorphism
      (numberFieldGlobalPlaceData (F := F)) (numberFieldGlobalPlaceData (F := F')))
    (v : HeightOneSpectrum (𝓞 F)) (f : Fˣ) :
    (transportedFiniteValueKernel (F := F) (F' := F') sigma v).realification
        (placeUnitTransport sigma f) =
      ((SourceModelBackend.coneGrothendieckEquiv
          ((SourceModelBackend.numberFieldSourceModelInput (F := F)).divisor
            SourceModelBackend.bottomPoint (Additive.ofMul f))).1 v : ℝ) := by
  rw [transportedFiniteValueKernel_realification]
  exact valueKernel_realification_eq_inputDivisor_finite f v

/-! ## 6. The missing source carrier: exact card -/

end Example36
end LeanFormal.IUT.IUTII.Frobenioid

namespace LeanFormal.IUT.Audit

/-- **Exact status card for boundary (2), transport fragment.**

What is constructed (this module and the modules it builds on): the actual
place transport of the finite and archimedean value maps along a faithful
domain isomorphism (`rho_{sigma v} o sigma = rho_v`); the transport of the
K1/K2 reduced value kernels and link layers, with mod/MOD realification and
degree readback commuting with transport; the recorded DVR-extension
ramification transport (`nu' = e * nu` as an explicit hypothesis, with the
`e`-th power degree law); and the agreement of the transported kernel
realification with the backend `Input.divisor`/`globalModelDivisor` finite
coordinate.

What is *not* constructed and not claimed: the actual `V_K` prime-strip-layer
transport over the local completions (`K_v`) and the source vertical
log-Kummer/log-shell carrier.  In particular the source normalization
identification of `rho_v` (normalizing `log|-mod(pv)|` to
`1/[Kv:(Fmod)v] * logPhi(pv)`) is not built; the completion carrier exists
elsewhere in the tree but its prime-strip-layer transport is absent.  The value
maps and link layers above are the frozen reduced (K1/K2) model, not the source
carrier. -/
def example36ValueMapPrimeStripTransport : Obligation :=
  { id := "IUT-I-II.example36-value-map-prime-strip-transport"
    source :=
      "IUT I, Example 3.5, (i); IUT III, Example 3.6; III Remark 3.9.5; " ++
        "boundary (2) V_K/rho_v row"
    status := VerificationStatus.interface
    note :=
      "Constructed: actual place transport of the finite/archimedean value " ++
        "maps along a faithful domain isomorphism (rho_{sigma v} o sigma = " ++
        "rho_v); transport of the K1/K2 reduced value kernels and link " ++
        "layers with mod/MOD realification and degree readback commuting " ++
        "with transport; recorded DVR-extension ramification transport " ++
        "(nu' = e * nu explicit, e-th power degree law); backend " ++
        "Input.divisor/globalModelDivisor agreement on the overlap. " ++
        "Missing: the actual V_K prime-strip-layer transport over the local " ++
        "completions K_v and the source vertical log-Kummer/log-shell " ++
        "carrier; the source rho_v normalization to " ++
        "1/[Kv:(Fmod)v] * logPhi(pv) is not identified. No source Hodge " ++
        "theater, theta-pilot or Tate claim is made."
    dependsOn :=
      [ "IUT-II.prime-strips-frobenioid-category-skeleton",
        "IUT-II.prime-strips-frobenioid-card-reductions" ] }

end LeanFormal.IUT.Audit
