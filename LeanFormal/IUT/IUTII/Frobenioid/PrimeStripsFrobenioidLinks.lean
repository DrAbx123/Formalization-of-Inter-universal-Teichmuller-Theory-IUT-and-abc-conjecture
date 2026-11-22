import LeanFormal.IUT.IUTII.Frobenioid.PrimeStripsConstruction

/-!
# Prime strips to Frobenioid links: the link-layer reduction pass

This module is the link-layer step of `IUT-I-II.prime-strips-frobenioids`
(pending at `IUTII/Frobenioid/PrimeStrips.lean:5`: "Construct the prime strips
and Frobenioid links from lower-layer objects; the carrier and degree kernels
are proved separately."), on top of the proved carrier and degree kernel of
`IUTII/Frobenioid/PrimeStripsConstruction.lean`.  It prepares the Frobenioid
link data consumed by the K1/K2 source chain
(`IUTIII/Theorem311/SourceK1K2Construction.lean`, the factored
`K2FrobenioidBoundary`) and by `SourceHodgeTheaterBridge`.

## Source locations (original text under `papers/motizuki_corpus/text`)

* Prime strips: IUT I, Definition 4.1 (holomorphic base-prime-strip) and
  Definition 5.2, (i)-(iv) (the collections of data `‡F = {‡Fv}v∈V`,
  `‡F⊢ = {‡F⊢v}v∈V`, the morphisms/capsules, and the globally realified
  `‡F⊩ = (‡C⊩, Prime(‡C⊩) ~→ V, ‡F⊢, {‡ρv}v∈V)`).
* Local Frobenioids: IUT I, Example 3.2, (iii); Example 3.3, (i), (iii)-(iv)
  (the `pv`-adic Frobenioid `Cv` and the sub-Frobenioid `C⊢v` whose divisor
  monoid is `N · logΦ(qv)|D⊢v`, with characteristic splitting `τ⊢v`); Example
  3.4, (i)-(ii) (the archimedean variant, an "MLF-Galois TM-pair").  Corollary
  5.3, (ii), (iv) records the rigidity of the passage between an F-prime-strip
  and its associated D-prime-strip.
* Global realified Frobenioids: IUT I, Example 3.5, (i): `C⊩mod` is the
  realification of the Frobenioid of [FrdI], Example 6.3 over the number field
  `Fmod` with trivial Galois extension; its divisor monoid `ΦC⊩mod` is a single
  abstract monoid, `Prime(C⊩mod)` is naturally bijective with `Vmod`, and the
  restriction functors `Cρv : C⊩mod → (C⊢v)rlf` are determined by
  `ρv : log⊢mod(pv) ↦ 1/[Kv:(Fmod)v] · logΦ(pv)`.
* MOD/mod and the global packet-theoretic Frobenioids: IUT III, Example 3.6,
  (i) (rational function torsor version `F⊛MOD`; its elementary morphisms are
  the linear morphisms and the multiplier `n` is the Frobenius degree), (ii)
  (local fractional ideal version `F⊛mod`), (iii) (natural isomorphism
  `F⊛mod ~→ F⊛MOD` inducing the identity on rational function monoids);
  Proposition 3.7, (i)-(ii) (single-packet construction of `(†F⊛MOD)α` and
  `(†F⊛mod)α` from the image monoids and the local Galois invariants);
  Proposition 3.10, (i) (local-global collections with localization
  isomorphisms); Theorem 3.11, (i), (c).

## What is proved here

* The prime-strip layer is reused as is: the carriers and fiber links of
  `PrimeStripsConstruction.lean` (its Audit record
  `primeStripsConstructionKernel`, status provedKernel) are re-exported under
  link-layer names in Section 1; no carrier is redefined.
* The finite-place model (Section 2): for any finite set `s` of rational prime
  places, the product monoid `FinitePlaceValueFamily s` of the local unit
  monoids carries a total degree homomorphism `finitePlaceTotalDegree`, and the
  `v0`-supported family induced by a local value through the integral-to-unit
  link (`finitePlaceSingleFamily`) has total degree equal to the local degree at
  `v0` (`finitePlaceSingle_totalDegree`).  This is the index-sum bookkeeping
  behind the normalization of `ρv` in IUT I, Example 3.5, (i); it is a reduced
  form: the arithmetic normalization factor `1/[Kv:(Fmod)v]` and the actual
  divisor monoid `ΦC⊩mod` are not modeled.
* The link-layer contract (Section 4): `PrimeStripFrobenioidLinkLayer` fixes
  the fields that the K2 source chain consumes (local/global degree kernels,
  `modMap`/`MODMap`, degree and transport compatibility), field-for-field
  matching the Frobenioid block of the frozen `K2FrobenioidBoundary`; the
  realification compatibility equations are derived, not assumed.  The finite
  model inhabits the `mod` direction card unconditionally
  (`finitePlaceModDirectionCard`) and the full contract conditionally on the
  `MOD` direction card (`singlePlaceLinkLayer_nonempty_of_MODCard`), following
  the `k2FromFrobenioidCards` pattern of `K1K2BoundaryReduction`.

## What is not constructed (cards; see also the Audit record at the end)

* Card CAT: the categorical Frobenioids `Cv`, `C⊢v`, `C⊩mod` with their base
  categories, value/divisor functors and elementary morphisms.  A direct
  functorial construction from the Frobenioid definition is blocked already at
  the sharpness condition of [FrdI], Definition 1.1, (i): the prime-strip
  value carriers are groups (units of algebraic closures, and products of
  such), while a divisorial monoid is sharp, so no nontrivial group carrier can
  satisfy it.
* Card MD1 (`ModDirectionCard`) / Card MD2 (`MODDirectionCard`): the two source
  directions with their degree and transport laws; in the source these are the
  arithmetic content of the fractional-ideal and rational-function-torsor
  realizations of IUT III, Example 3.6 and the comparison of Proposition 3.7.
* Boundary items (1), (2), (4) of
  `PrimeStripsConstruction.primeStripsFrobenioidBoundary`
  (`PrimeStripsConstruction.lean:390`) remain open at this layer: the
  nontrivial geometric fundamental group, the general number-field place
  carriers, and the arithmetic Frobenius data.  Boundary item (5), the
  divisorial/realified value structure, is addressed here only in the reduced
  degree-kernel form of Section 3.

## Original proof strategy vs. the route taken here

The source reconstructs `Cv`, up to isomorphism, from the pair
`π1(‡Dv) ↷ ‡Mv` (an ind-topological monoid with a continuous action; IUT I,
Example 3.3, (iii)-(iv), with [AbsTopIII], Definition 3.1, (ii)), and assembles
the global realified Frobenioids by restriction of poly-Frobenioids ([FrdII],
§5).  That route needs the categorical theory of Frobenioids and a nontrivial
geometric fundamental group, neither of which is available here (the
`PrimeStripsConstruction` carriers use `MonoidHom.id` as projection, so the
geometric kernel is trivial).  The route taken here is the structural/contract
one: keep the proved value/degree carriers, prove the degree bookkeeping that
is genuinely available, expose the remaining source content as named cards, and
assemble the contract conditionally.  The finite-model route (finite prime
intervals of `PrimeStripsConstruction` generalized to arbitrary finite place
sets) is the proved route of Section 2.  The vendor-snapshot shapes
`FrobenioidStructureEquivalence` / `FrobenioidRestriction` (Frobenioids I,
Corollary 4.11) were consulted for the CAT card only; they require categories
and are not imported.
-/

namespace LeanFormal.IUT

open FPrimeStripLink
open scoped BigOperators

noncomputable section

universe ux uy

/-! ## 1. The reused prime-strip layer

The carriers and fiber links below are the already proved declarations of
`IUTII/Frobenioid/PrimeStripsConstruction.lean` (Audit:
`primeStripsConstructionKernel`, provedKernel).  The abbreviations give the
link layer stable names; the two restatements record the parts of the existing
interface that the Frobenioid link layer consumes. -/

/-- The unit-valued F-prime-strip carrier over the rational prime places:
`localFPrimeStrip` (`LocalPrimeStrip.lean:30`), re-exported.  In the source
this is (the value-monoid side of) the collection `{Fv}v∈V` of IUT I,
Definition 5.2, (i). -/
abbrev frobenioidLinkUnitStrip : FPrimeStrip RationalPrimePlace := localFPrimeStrip

/-- The integral-valued F-prime-strip carrier: `localIntegralFPrimeStrip`
(`LocalIntegralFPrimeStrip.lean:29`), re-exported. -/
abbrev frobenioidLinkIntegralStrip : FPrimeStrip RationalPrimePlace :=
  localIntegralFPrimeStrip

/-- The integral-to-unit evaluation link: `localIntegralUnitLink`
(`PrimeStripsConstruction.lean:172`), re-exported.  In the source this link is
the value-monoid part of the identification of the F-prime-strip with the
`pv`-adic Frobenioid data (IUT I, Example 3.3, (iv); Corollary 5.3, (ii)). -/
abbrev frobenioidLinkIntegralToUnit :
    FPrimeStripLink frobenioidLinkIntegralStrip frobenioidLinkUnitStrip :=
  localIntegralUnitLink

/-- Degree compatibility of the evaluation link: the degree of an integral
value equals the degree of its unit image.  This is the `compatDegree` field
of `localIntegralUnitLink` (`PrimeStripsConstruction.lean:184`), restated for
the link-layer names. -/
theorem frobenioidLinkIntegralToUnit_degree (v : RationalPrimePlace)
    (x : frobenioidLinkIntegralStrip.Mon v) :
    frobenioidLinkUnitStrip.degree v (frobenioidLinkIntegralToUnit.mapMon v x) =
      frobenioidLinkIntegralStrip.degree v x :=
  localIntegralUnitLink.compatDegree v x

/-- Total degrees of unit families multiply: `FPrimeStrip.totalDegree_mul`
(`PrimeStripCore.lean:145`), restated for the link-layer carrier. -/
theorem frobenioidLinkUnitStrip_totalDegree_mul
    (s : Finset RationalPrimePlace) (x y : ∀ v, frobenioidLinkUnitStrip.Mon v) :
    frobenioidLinkUnitStrip.totalDegree s (fun v => x v * y v) =
      frobenioidLinkUnitStrip.totalDegree s x +
        frobenioidLinkUnitStrip.totalDegree s y :=
  FPrimeStrip.totalDegree_mul localFPrimeStrip s x y

/-! ## 2. The finite-place model (proved)

The four `rfl` facts about `Multiplicative Real` used below: the additive
reading of the type tag `Multiplicative Real` is the ordinary `Real` sum, and
all laws are definitional. -/

@[simp] theorem realToAdd_ofAdd (x : Real) :
    (Multiplicative.ofAdd x).toAdd = x := rfl

@[simp] theorem realOfAdd_toAdd (x : Multiplicative Real) :
    Multiplicative.ofAdd x.toAdd = x := rfl

@[simp] theorem realOfAdd_add (x y : Real) :
    Multiplicative.ofAdd (x + y) = Multiplicative.ofAdd x * Multiplicative.ofAdd y := rfl

@[simp] theorem realOfAdd_zero :
    Multiplicative.ofAdd (0 : Real) = 1 := rfl

@[simp] theorem realToAdd_one :
    (1 : Multiplicative Real).toAdd = 0 := rfl

@[simp] theorem realToAdd_mul (x y : Multiplicative Real) :
    (x * y).toAdd = x.toAdd + y.toAdd := rfl

/-- The place-indexed value family over a finite set `s` of rational prime
places: the product of the local unit monoids at the places of `s`.  This is
the finite-model carrier standing for the single abstract divisor monoid
`ΦC⊩mod` of IUT I, Example 3.5, (i), restricted to the places of `s`. -/
abbrev FinitePlaceValueFamily (s : Finset RationalPrimePlace) : Type :=
  (w : {v : RationalPrimePlace // v ∈ s}) → frobenioidLinkUnitStrip.Mon w.1

/-- The `v0`-supported value family: the local integral value `x` transported
to the unit family at `v0` through the integral-to-unit link, and `1` at every
other place.  In the normalization of IUT I, Example 3.5, (i), this is a
one-place element of the sort whose total degree the restriction `ρv0`
computes. -/
def finitePlaceSingleFamily (s : Finset RationalPrimePlace)
    (v₀ : {v : RationalPrimePlace // v ∈ s})
    (x : frobenioidLinkIntegralStrip.Mon v₀.1) : FinitePlaceValueFamily s :=
  Pi.mulSingle v₀ (frobenioidLinkIntegralToUnit.mapMon v₀.1 x)

@[simp] theorem finitePlaceSingleFamily_apply_same
    (s : Finset RationalPrimePlace) (v₀ : {v : RationalPrimePlace // v ∈ s})
    (x : frobenioidLinkIntegralStrip.Mon v₀.1) :
    finitePlaceSingleFamily s v₀ x v₀ =
      frobenioidLinkIntegralToUnit.mapMon v₀.1 x :=
  Pi.mulSingle_eq_same _ _

@[simp] theorem finitePlaceSingleFamily_apply_of_ne
    (s : Finset RationalPrimePlace) (v₀ : {v : RationalPrimePlace // v ∈ s})
    {b : {v : RationalPrimePlace // v ∈ s}} (hb : b ≠ v₀)
    (x : frobenioidLinkIntegralStrip.Mon v₀.1) :
    finitePlaceSingleFamily s v₀ x b = 1 :=
  Pi.mulSingle_eq_of_ne hb _

/-- The total degree of a finite place family, in additive form: the sum of
the local degrees over the places of `s`. -/
def finitePlaceTotalDegreeFun (s : Finset RationalPrimePlace)
    (f : FinitePlaceValueFamily s) : Multiplicative Real :=
  Multiplicative.ofAdd
    (∑ w : {v : RationalPrimePlace // v ∈ s},
      (frobenioidLinkUnitStrip.degree w.1 (f w)).toAdd)

@[simp] theorem finitePlaceTotalDegreeFun_one (s : Finset RationalPrimePlace) :
    finitePlaceTotalDegreeFun s (1 : FinitePlaceValueFamily s) = 1 := by
  simp [finitePlaceTotalDegreeFun]

theorem finitePlaceTotalDegreeFun_mul (s : Finset RationalPrimePlace)
    (f g : FinitePlaceValueFamily s) :
    finitePlaceTotalDegreeFun s (f * g) =
      finitePlaceTotalDegreeFun s f * finitePlaceTotalDegreeFun s g := by
  unfold finitePlaceTotalDegreeFun
  rw [← realOfAdd_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun w _ => by
    rw [Pi.mul_apply, (frobenioidLinkUnitStrip.degree w.1).map_mul, realToAdd_mul])

theorem finitePlaceTotalDegreeFun_mul_toAdd (s : Finset RationalPrimePlace)
    (f g : FinitePlaceValueFamily s) :
    (finitePlaceTotalDegreeFun s (f * g)).toAdd =
      (finitePlaceTotalDegreeFun s f).toAdd +
        (finitePlaceTotalDegreeFun s g).toAdd := by
  rw [finitePlaceTotalDegreeFun_mul, realToAdd_mul]

/-- The total degree homomorphism of the finite place family: the finite-model
reduced form of the degree of the globally realified Frobenioid `C⊩mod`
(IUT I, Example 3.5, (i)) — the degree of the single abstract monoid,
restricted to the places of `s`. -/
def finitePlaceTotalDegree (s : Finset RationalPrimePlace) :
    FinitePlaceValueFamily s →* Multiplicative Real where
  toFun := finitePlaceTotalDegreeFun s
  map_one' := finitePlaceTotalDegreeFun_one s
  map_mul' := finitePlaceTotalDegreeFun_mul s

/-- The single-place normalization (reduced form of IUT I, Example 3.5, (i)):
a local integral value placed at `v0` through the integral-to-unit link has
total family degree exactly the local degree at `v0`.  The arithmetic
normalization factor `1/[Kv:(Fmod)v]` of the source `ρv` is not modeled. -/
theorem finitePlaceSingle_totalDegree (s : Finset RationalPrimePlace)
    (v₀ : {v : RationalPrimePlace // v ∈ s})
    (x : frobenioidLinkIntegralStrip.Mon v₀.1) :
    finitePlaceTotalDegree s (finitePlaceSingleFamily s v₀ x) =
      frobenioidLinkIntegralStrip.degree v₀.1 x := by
  apply Multiplicative.ext
  change (finitePlaceTotalDegreeFun s (finitePlaceSingleFamily s v₀ x)).toAdd =
    (frobenioidLinkIntegralStrip.degree v₀.1 x).toAdd
  rw [show (finitePlaceTotalDegreeFun s (finitePlaceSingleFamily s v₀ x)).toAdd =
    (∑ w : {v : RationalPrimePlace // v ∈ s},
      (frobenioidLinkUnitStrip.degree w.1 (finitePlaceSingleFamily s v₀ x w)).toAdd)
    from rfl]
  rw [Finset.sum_eq_single v₀]
  · rw [finitePlaceSingleFamily_apply_same]
    exact congrArg Multiplicative.toAdd
      (frobenioidLinkIntegralToUnit_degree v₀.1 x)
  · intro b _ hb
    rw [finitePlaceSingleFamily_apply_of_ne s v₀ hb]
    simp
  · intro h
    exact absurd (Finset.mem_univ v₀) h

/-! ## 3. The Frobenioid value kernels -/

/-- The value/divisor-side degree kernel of a Frobenioid, in the reduced form
consumed by the K1/K2 source chain.  The fields are field-for-field those of
`Theorem311Source.SourceDependencyChain.SourceProposition37Frobenioid`
(`IUTIII/Theorem311/SourceDependencyChain.lean:995`), restated at the IUT-II
layer because the IUT-III modules import the IUT-II modules and not conversely;
the consumer fills its record from this one.

Not formalized here: the Frobenioid category itself, its base category, its
value functor and elementary morphisms (card CAT of the module doc comment). -/
structure FrobenioidValueKernel (X : Type ux) [CommMonoid X] where
  degree : X →* Multiplicative Real
  realification : X → Real
  realification_mul : ∀ x y,
    realification (x * y) = realification x + realification y
  degree_realification : ∀ x, (degree x : Real) = realification x
  unit : X
  unit_realification : realification 1 = 0
  effective : X → Prop
  effective_proved : ∀ x, effective x
  transport : X → X
  transport_degree : ∀ x, degree (transport x) = degree x

namespace FrobenioidValueKernel

variable {X : Type ux} [CommMonoid X]

theorem degree_mul (K : FrobenioidValueKernel X) (x y : X) :
    K.degree (x * y) = K.degree x * K.degree y :=
  K.degree.map_mul x y

theorem realification_mul_at (K : FrobenioidValueKernel X) (x y : X) :
    K.realification (x * y) = K.realification x + K.realification y :=
  K.realification_mul x y

theorem degree_realification_at (K : FrobenioidValueKernel X) (x : X) :
    (K.degree x : Real) = K.realification x :=
  K.degree_realification x

theorem realification_one (K : FrobenioidValueKernel X) :
    K.realification 1 = 0 :=
  K.unit_realification

theorem transport_degree_at (K : FrobenioidValueKernel X) (x : X) :
    K.degree (K.transport x) = K.degree x :=
  K.transport_degree x

theorem realification_transport (K : FrobenioidValueKernel X) (x : X) :
    K.realification (K.transport x) = K.realification x := by
  rw [← K.degree_realification (K.transport x), K.transport_degree,
    K.degree_realification]

end FrobenioidValueKernel

/-! ## 4. The link-layer contract -/

/-- The Frobenioid link-layer contract consumed by the K2 source chain.

The fields are field-for-field the Frobenioid block of
`Theorem311Source.K2FrobenioidBoundary`
(`IUTIII/Theorem311/SourceK1K2Construction.lean:350`): the local and global
degree kernels, the two source directions `modMap`/`MODMap`, and the degree and
transport compatibility equations.  As in `K1K2BoundaryReduction`, the
realification compatibility equations are derived below
(`mod_realification`, `MOD_realification`) and are not fields.

Source shape: IUT III, Proposition 3.7, (i)-(ii), and Theorem 3.11, (i), (c)
(the natural isomorphisms between the non-realified and realified MOD/mod
Frobenioids, whose global degrees are computed by log-volumes).  The
`local`/`global` reading of `modMap`/`MODMap` is the frozen consumer's reduced
form: in the source both `F⊛mod` and `F⊛MOD` are global (IUT III, Example 3.6,
(i)-(iii)), and the genuinely local-to-global source maps are the restriction
functors `Cρv : C⊩mod → (C⊢v)rlf` of IUT I, Example 3.5, (i). -/
structure PrimeStripFrobenioidLinkLayer (X : Type ux) (Y : Type uy)
    [CommMonoid X] [CommMonoid Y] where
  localFrobenioid : FrobenioidValueKernel X
  globalFrobenioid : FrobenioidValueKernel Y
  modMap : X → Y
  MODMap : Y → X
  mod_degree : ∀ x,
    globalFrobenioid.degree (modMap x) = localFrobenioid.degree x
  MOD_degree : ∀ y,
    localFrobenioid.degree (MODMap y) = globalFrobenioid.degree y
  mod_transport : ∀ x,
    modMap (localFrobenioid.transport x) =
      globalFrobenioid.transport (modMap x)
  MOD_transport : ∀ y,
    MODMap (globalFrobenioid.transport y) =
      localFrobenioid.transport (MODMap y)

namespace PrimeStripFrobenioidLinkLayer

variable {X : Type ux} {Y : Type uy} [CommMonoid X] [CommMonoid Y]

/-- Realification compatibility of `modMap`, derived from the degree equation
and the two `degree_realification` laws; it is not an independent field
(cf. `K1K2BoundaryReduction.k2FromFrobenioidCards`). -/
theorem mod_realification (L : PrimeStripFrobenioidLinkLayer X Y) (x : X) :
    L.globalFrobenioid.realification (L.modMap x) =
      L.localFrobenioid.realification x :=
  ((L.globalFrobenioid.degree_realification (L.modMap x)).symm).trans
    ((congrArg (fun r : Multiplicative Real => (r : Real))
      (L.mod_degree x)).trans
      (L.localFrobenioid.degree_realification x))

/-- Realification compatibility of `MODMap`, derived like `mod_realification`. -/
theorem MOD_realification (L : PrimeStripFrobenioidLinkLayer X Y) (y : Y) :
    L.localFrobenioid.realification (L.MODMap y) =
      L.globalFrobenioid.realification y :=
  ((L.localFrobenioid.degree_realification (L.MODMap y)).symm).trans
    ((congrArg (fun r : Multiplicative Real => (r : Real))
      (L.MOD_degree y)).trans
      (L.globalFrobenioid.degree_realification y))

theorem mod_degree_real (L : PrimeStripFrobenioidLinkLayer X Y) (x : X) :
    (L.globalFrobenioid.degree (L.modMap x) : Real) =
      (L.localFrobenioid.degree x : Real) :=
  congrArg (fun r : Multiplicative Real => (r : Real)) (L.mod_degree x)

theorem MOD_degree_real (L : PrimeStripFrobenioidLinkLayer X Y) (y : Y) :
    (L.localFrobenioid.degree (L.MODMap y) : Real) =
      (L.globalFrobenioid.degree y : Real) :=
  congrArg (fun r : Multiplicative Real => (r : Real)) (L.MOD_degree y)

theorem mod_transport_degree (L : PrimeStripFrobenioidLinkLayer X Y) (x : X) :
    L.globalFrobenioid.degree (L.modMap (L.localFrobenioid.transport x)) =
      L.localFrobenioid.degree x := by
  rw [L.mod_transport, L.globalFrobenioid.transport_degree, L.mod_degree]

theorem MOD_transport_degree (L : PrimeStripFrobenioidLinkLayer X Y) (y : Y) :
    L.localFrobenioid.degree (L.MODMap (L.globalFrobenioid.transport y)) =
      L.globalFrobenioid.degree y := by
  rw [L.MOD_transport, L.localFrobenioid.transport_degree, L.MOD_degree]

theorem mod_transport_realification (L : PrimeStripFrobenioidLinkLayer X Y)
    (x : X) :
    L.globalFrobenioid.realification
        (L.modMap (L.localFrobenioid.transport x)) =
      L.localFrobenioid.realification x :=
  (L.mod_realification (L.localFrobenioid.transport x)).trans
    (L.localFrobenioid.realification_transport x)

theorem MOD_transport_realification (L : PrimeStripFrobenioidLinkLayer X Y)
    (y : Y) :
    L.localFrobenioid.realification
        (L.MODMap (L.globalFrobenioid.transport y)) =
      L.globalFrobenioid.realification y :=
  (L.MOD_realification (L.globalFrobenioid.transport y)).trans
    (L.globalFrobenioid.realification_transport y)

end PrimeStripFrobenioidLinkLayer

/-! ## 5. The named cards and the conditional assembly -/

/-- Card MD1 (the `mod` direction, in the frozen consumer's local-to-global
reading): existence of a map from the local kernel to the global kernel with
the two compatibility laws.

Missing object/law: the map itself with its degree and transport equations;
in the source this is the arithmetic content of the fractional-ideal
realization `F⊛mod` and its comparison with `F⊛MOD` (IUT III, Example 3.6,
(ii)-(iii); Proposition 3.7, (ii)).

Why the existing material does not suffice: the carriers built in
`PrimeStripsConstruction` carry no such map.  In the finite model the natural
candidate exists and is proved in `finitePlaceModDirectionCard` (single-place
insertion); no global-to-local direction is available yet (Card MD2).

Consumers: `K2FrobenioidBoundary.modMap`, `mod_degree`, `mod_transport`
(`SourceK1K2Construction.lean:357-374`). -/
def ModDirectionCard {X : Type ux} {Y : Type uy} [CommMonoid X] [CommMonoid Y]
    (localKernel : FrobenioidValueKernel X) (globalKernel : FrobenioidValueKernel Y) :
    Prop :=
  ∃ modMap : X → Y,
    (∀ x, globalKernel.degree (modMap x) = localKernel.degree x) ∧
      ∀ x, modMap (localKernel.transport x) =
        globalKernel.transport (modMap x)

/-- Card MD2 (the `MOD` direction): existence of a map from the global kernel
back to the local kernel with the two compatibility laws.

Missing object/law: the map itself with its degree and transport equations;
in the source this is the rational-function-torsor-to-fractional-ideal
comparison (IUT III, Example 3.6, (iii)) and the log-volume comparison used
for the global arithmetic degrees (Proposition 3.9, (iii), and Corollary 3.12
in the source chain).

Why the existing material does not suffice: no global-to-local map with
degree compatibility exists on the current carriers; in the finite model a
candidate would need the arithmetic surjectivity of the local norm degree onto
the total-degree range, which is not available (the norm image on
`ℚ̄p` is `p^ℚ`, not all of `ℝ`).

Consumers: `K2FrobenioidBoundary.MODMap`, `MOD_degree`, `MOD_transport`
(`SourceK1K2Construction.lean:358-374`). -/
def MODDirectionCard {X : Type ux} {Y : Type uy} [CommMonoid X] [CommMonoid Y]
    (localKernel : FrobenioidValueKernel X) (globalKernel : FrobenioidValueKernel Y) :
    Prop :=
  ∃ MODMap : Y → X,
    (∀ y, localKernel.degree (MODMap y) = globalKernel.degree y) ∧
      ∀ y, MODMap (globalKernel.transport y) =
        localKernel.transport (MODMap y)

/-- Conditional assembly of the link layer from the two cards: the
`k2FromFrobenioidCards` pattern of `K1K2BoundaryReduction`
(`IUTII/Kummer/K1K2BoundaryReduction.lean:523`) at the prime-strip layer. -/
theorem primeStripFrobenioidLinkLayer_nonempty_of_cards
    {X : Type ux} {Y : Type uy} [CommMonoid X] [CommMonoid Y]
    (localKernel : FrobenioidValueKernel X) (globalKernel : FrobenioidValueKernel Y)
    (hmod : ModDirectionCard localKernel globalKernel)
    (hMOD : MODDirectionCard localKernel globalKernel) :
    Nonempty (PrimeStripFrobenioidLinkLayer X Y) := by
  obtain ⟨modMap, hmod_degree, hmod_transport⟩ := hmod
  obtain ⟨MODMap, hMOD_degree, hMOD_transport⟩ := hMOD
  exact ⟨{ localFrobenioid := localKernel
           globalFrobenioid := globalKernel
           modMap := modMap
           MODMap := MODMap
           mod_degree := hmod_degree
           MOD_degree := hMOD_degree
           mod_transport := hmod_transport
           MOD_transport := hMOD_transport }⟩

/-! ## 6. The finite place model as kernels and cards -/

/-- The local degree kernel at a rational prime place: the degree and
realification data of `frobenioidLinkIntegralStrip` at `v0`, with trivial
transport and total effectiveness.  Reduced form of the divisor monoid `ΦC⊢v`
normalized by `N · logΦ(qv)|D⊢v` (IUT I, Example 3.3, (iv)): only the
value/degree side is modeled. -/
def localIntegralPlaceFrobenioidValueKernel (v₀ : RationalPrimePlace) :
    FrobenioidValueKernel (frobenioidLinkIntegralStrip.Mon v₀) where
  degree := frobenioidLinkIntegralStrip.degree v₀
  realification := fun x => (frobenioidLinkIntegralStrip.degree v₀ x).toAdd
  realification_mul := fun x y => by
    rw [(frobenioidLinkIntegralStrip.degree v₀).map_mul, realToAdd_mul]
  degree_realification := fun x => rfl
  unit := 1
  unit_realification := by simp
  effective := fun _ => True
  effective_proved := fun _ => trivial
  transport := id
  transport_degree := fun x => rfl

/-- The degree kernel of the finite place family: `finitePlaceTotalDegree`
with the additive realification, trivial transport, and total effectiveness.
This is the proved `mod`-side global kernel of the finite model (reduced form
of the value side of `C⊩mod`, IUT I, Example 3.5, (i)). -/
def finitePlaceFrobenioidValueKernel (s : Finset RationalPrimePlace) :
    FrobenioidValueKernel (FinitePlaceValueFamily s) where
  degree := finitePlaceTotalDegree s
  realification := fun f => (finitePlaceTotalDegreeFun s f).toAdd
  realification_mul := fun f g => by
    change (finitePlaceTotalDegreeFun s (f * g)).toAdd =
      (finitePlaceTotalDegreeFun s f).toAdd +
        (finitePlaceTotalDegreeFun s g).toAdd
    rw [finitePlaceTotalDegreeFun_mul, realToAdd_mul]
  degree_realification := fun f => rfl
  unit := 1
  unit_realification := by simp
  effective := fun _ => True
  effective_proved := fun _ => trivial
  transport := id
  transport_degree := fun f => rfl

/-- The `mod` direction card is inhabited in the finite model: the local value
at `v0`, inserted through the integral-to-unit link, has total degree equal to
its local degree (`finitePlaceSingle_totalDegree`), and transport is trivial on
both sides.  This is the proved direction of the finite model; see Card MD2
for the missing direction. -/
theorem finitePlaceModDirectionCard (s : Finset RationalPrimePlace)
    (v₀ : {v : RationalPrimePlace // v ∈ s}) :
    ModDirectionCard (localIntegralPlaceFrobenioidValueKernel v₀.1)
      (finitePlaceFrobenioidValueKernel s) :=
  ⟨finitePlaceSingleFamily s v₀, finitePlaceSingle_totalDegree s v₀,
    fun _ => rfl⟩

/-- The finite-model link layer at a single place, conditional on the `MOD`
card: the proved `mod` direction assembled with a supplied `MOD` direction. -/
theorem singlePlaceLinkLayer_nonempty_of_MODCard (s : Finset RationalPrimePlace)
    (v₀ : {v : RationalPrimePlace // v ∈ s})
    (hMOD : MODDirectionCard (localIntegralPlaceFrobenioidValueKernel v₀.1)
      (finitePlaceFrobenioidValueKernel s)) :
    Nonempty (PrimeStripFrobenioidLinkLayer
      (frobenioidLinkIntegralStrip.Mon v₀.1) (FinitePlaceValueFamily s)) :=
  primeStripFrobenioidLinkLayer_nonempty_of_cards
    (localIntegralPlaceFrobenioidValueKernel v₀.1)
    (finitePlaceFrobenioidValueKernel s)
    (finitePlaceModDirectionCard s v₀) hMOD

end
end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Link-layer reduction pass for `IUT-I-II.prime-strips-frobenioids`
(link layer only; the prime-strip carrier/degree kernel is
`IUT-II.prime-strip-construction-kernel`). -/
def primeStripsFrobenioidLinkLayer : Obligation :=
  { id := "IUT-II.prime-strips-frobenioid-link-layer"
    source :=
      "IUT I, Definition 5.2, (i)-(iv); Example 3.3, (iii)-(iv); Example " ++
        "3.5, (i); Corollary 5.3, (i)-(iii); IUT III, Example 3.6, (i)-(iii); " ++
        "Proposition 3.7, (i)-(ii); Theorem 3.11, (i), (c)"
    status := VerificationStatus.interface
    note :=
      "Reduction pass for the Frobenioid link layer of " ++
        "`IUT-I-II.prime-strips-frobenioids`, on top of " ++
        "`IUT-II.prime-strip-construction-kernel`. Proved: the reused " ++
        "prime-strip carriers and links are re-exported with their degree " ++
        "interface restated; the finite-place model " ++
        "(`FinitePlaceValueFamily`, `finitePlaceTotalDegree`, " ++
        "`finitePlaceSingle_totalDegree`) is proved; the `FrobenioidValueKernel` " ++
        "records of the local integral place and of the finite family are " ++
        "constructed; the contract `PrimeStripFrobenioidLinkLayer` " ++
        "(field-for-field the Frobenioid block of the frozen " ++
        "`K2FrobenioidBoundary`) is derived-conditionally assembled from " ++
        "`ModDirectionCard` (inhabited by the finite model) and " ++
        "`MODDirectionCard` (card MD2). Not constructed: the categorical " ++
        "Frobenioids Cv/C⊢v/C⊩mod with value functors and elementary " ++
        "morphisms (card CAT; a direct construction from the Frobenioid " ++
        "definition is blocked at sharpness, since the prime-strip value " ++
        "carriers are groups), the global mod/MOD realizations and their " ++
        "natural isomorphism (IUT III, Example 3.6, (iii)), and the arithmetic " ++
        "normalization of `ρv` (IUT I, Example 3.5, (i)). Boundary items (1), " ++
        "(2), (4) of `primeStripsFrobenioidBoundary` remain open; item (5) is " ++
        "addressed only in the reduced degree-kernel form."
    dependsOn :=
      [ "IUT-II.prime-strip-construction-kernel",
        "IUT-I-II.prime-strip-degree-kernel",
        "IUT-I-II.local-f-prime-strip-carrier",
        "IUT-II.local-integral-f-prime-strip-carrier" ] }

end LeanFormal.IUT.Audit

