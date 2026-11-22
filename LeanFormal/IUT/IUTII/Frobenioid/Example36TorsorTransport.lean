import LeanFormal.IUT.IUTII.Frobenioid.Example36FrobenioidTransport
import LeanFormal.IUT.IUTII.Frobenioid.Example36TorsorPresentation
import LeanFormal.IUT.IUTII.Frobenioid.Example36TorsorEquivalence
import LeanFormal.IUT.IUTII.Frobenioid.Example36LocalContraction
import LeanFormal.IUT.IUTII.Frobenioid.Example36TorsorTheory
import LeanFormal.IUT.IUTII.Frobenioid.Example36GlobalPlaceData
import LeanFormal.IUT.IUTII.Frobenioid.Example36NumberFieldPlaceData
import Mathlib.Tactic

/-!
# Transport of the torsor-presentation layer of Example 3.6 along a place localization

This module transports the torsor presentations and their degree-(n) morphisms
of IUT III, Example 3.6 along a `PlaceLocalizationTransport` datum of
`Example36FrobenioidTransport`: a ring map `F →+* F'` together with the
place-restriction maps, the explicitly recorded positive ramification index
`e(w)`, and the delta/principal-value/effective-cone transport laws.

## Contents

1. The pushforward of an `F^x`-torsor along a group homomorphism
   `φ : F^x → F'^x`: the balanced product `F'^x ×^{F^x} T` is a genuine
   `F'^x`-torsor (`torsorPushforwardGTorsor`), with the canonical map
   `t ↦ [1, t]` that is `φ`-equivariant (`torsorPushforwardMap_smul`).
2. The transport of a local contracted product `Gamma ×^G T` along a pair
   (group map `φ`, additive value group map `σ`) satisfying
   `δ'(φ g) = σ(δ(g))`: `localContractionTransport`, with the coordinate law
   `localCoord (e t) (transport p) = σ (localCoord t p)`.
3. The transport of a torsor presentation: the underlying torsor is pushed
   forward, the base point becomes `[1, base]`, and the local points are the
   transported contracted-product points.  The finite-support condition is
   preserved, and the local coordinates transform by the datum:
   `(transport P).finiteCoord w = e(w) * P.finiteCoord (rho w)` and
   `(transport P).infiniteCoord w = P.infiniteCoord (rho_inf w)`.
4. The transport of torsor arrows: the degree is unchanged, the multiplier is
   the image under the unit map, and the local integrality conditions are the
   transported source conditions (via the datum's cone transport).  The
   transport preserves identities and composition.
5. Compatibility with a change of base points: the transported base point,
   local coordinates, arrow degree/multiplier and local integrality conditions
   of a rebased presentation agree with those of the rebase of the transported
   presentation (coordinate-level compatibility; the two presentations are not
   syntactically equal objects).
6. Identification, via the `(n,f)` coordinates, of the ideal family of the
   transported presentation with the transported ideal family of
   `Example36FrobenioidTransport` (`presentationToIdealFamily_transport`,
   reusing the coordinate equivalence of `Example36TorsorEquivalence`), both as
   an exact equality of ideal-family objects and at the level of degrees,
   multipliers and the finite/archimedean local inclusion conditions of the
   corresponding ideal-family morphisms.
7. Specialization of the identification and of the arrow comparison to the
   actual number-field place data.

## Boundary (coordinate-level transport versus object-level transport)

* The underlying torsor, the base point and the local points of the transported
  presentation are constructed objects, not a substitution by the identity
  transport or by a trivial regular torsor.
* The ramification `e` is the datum's positive field; at a finite place with
  `e(w) ≠ 1` the transported finite coordinate genuinely differs from the
  source coordinate (`transport_finiteCoord_ne_of_ramification`).
* Change of base points commutes with the transport at the level of base
  points, local coordinates, arrow degrees, arrow multipliers and local
  integrality conditions.  The transported rebased presentation and the rebase
  of the transported presentation are not claimed to be syntactically equal
  presentations: only their explicit base-point/coordinate data are compared.
* The ideal-family identification is an exact equality of global ideal-family
  objects.  On morphisms the comparison with the transported ideal-family
  morphism is proved for the degree, the multiplier and the
  finite/archimedean local inclusion conditions; the conditions are compared as
  predicates, not as fields of a single typed identity of morphisms, because
  the two ideal-family objects involved are syntactically different (but
  proved equal) objects.
* No theta-pilot, q-pilot, Tate or Hodge-theater claim is made.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open scoped NumberField
open IsDedekindDomain NumberField

universe u v w

/-! ## 1. The pushforward of a torsor along a group homomorphism -/

section Pushforward

variable {F : Type u} [Field F] {F' : Type u} [Field F']

/-- The relation of the balanced product `F'^x ×^{F^x} T`: two pairs are
related when one is obtained from the other by the diagonal action
`k • (a, t) = (a * φ(k)⁻¹, k • t)`. -/
def torsorPushforwardRel (φ : Fˣ →* F'ˣ) (T : GTorsor Fˣ)
    (p q : F'ˣ × T.carrier) : Prop :=
  ∃ g : Fˣ, q = (p.1 * (φ g)⁻¹, g • p.2)

/-- The pushforward relation is reflexive. -/
theorem torsorPushforwardRel_refl (φ : Fˣ →* F'ˣ) (T : GTorsor Fˣ)
    (p : F'ˣ × T.carrier) : torsorPushforwardRel φ T p p := by
  refine ⟨1, ?_⟩
  ext <;> simp

/-- The pushforward relation is symmetric. -/
theorem torsorPushforwardRel_symm {φ : Fˣ →* F'ˣ} {T : GTorsor Fˣ}
    {p q : F'ˣ × T.carrier} (h : torsorPushforwardRel φ T p q) :
    torsorPushforwardRel φ T q p := by
  obtain ⟨g, rfl⟩ := h
  refine ⟨g⁻¹, ?_⟩
  apply Prod.ext
  · show p.1 = (p.1 * (φ g)⁻¹) * (φ g⁻¹)⁻¹
    rw [map_inv, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
  · show p.2 = g⁻¹ • (g • p.2)
    rw [← mul_smul, inv_mul_cancel, one_smul]

/-- The pushforward relation is transitive. -/
theorem torsorPushforwardRel_trans {φ : Fˣ →* F'ˣ} {T : GTorsor Fˣ}
    {p q r : F'ˣ × T.carrier} (h1 : torsorPushforwardRel φ T p q)
    (h2 : torsorPushforwardRel φ T q r) : torsorPushforwardRel φ T p r := by
  obtain ⟨g, rfl⟩ := h1
  obtain ⟨h, rfl⟩ := h2
  refine ⟨h * g, ?_⟩
  apply Prod.ext
  · show (p.1 * (φ g)⁻¹) * (φ h)⁻¹ = p.1 * (φ (h * g))⁻¹
    rw [map_mul, mul_inv_rev, ← mul_assoc]
  · show h • (g • p.2) = (h * g) • p.2
    rw [mul_smul]

/-- The setoid of the balanced product `F'^x ×^{F^x} T`. -/
def torsorPushforwardSetoid (φ : Fˣ →* F'ˣ) (T : GTorsor Fˣ) :
    Setoid (F'ˣ × T.carrier) where
  r := torsorPushforwardRel φ T
  iseqv :=
    ⟨torsorPushforwardRel_refl φ T,
      fun h => torsorPushforwardRel_symm h,
      fun h1 h2 => torsorPushforwardRel_trans h1 h2⟩

/-- The underlying type of the pushforward of an `F^x`-torsor along
`φ : F^x → F'^x`: the balanced product `F'^x ×^{F^x} T`. -/
abbrev TorsorPushforward (φ : Fˣ →* F'ˣ) (T : GTorsor Fˣ) : Type u :=
  Quotient (torsorPushforwardSetoid φ T)

/-- The class of a pair in the pushforward. -/
abbrev torsorPushforwardMk (φ : Fˣ →* F'ˣ) (T : GTorsor Fˣ)
    (p : F'ˣ × T.carrier) : TorsorPushforward φ T :=
  Quotient.mk (torsorPushforwardSetoid φ T) p

/-- Two representatives define the same point of the pushforward exactly when
they are related by the diagonal `F^x`-action. -/
theorem torsorPushforwardMk_eq_iff {φ : Fˣ →* F'ˣ} {T : GTorsor Fˣ}
    {p q : F'ˣ × T.carrier} :
    torsorPushforwardMk φ T p = torsorPushforwardMk φ T q ↔
      torsorPushforwardRel φ T p q :=
  Quotient.eq

/-- The defining relation of the balanced product: moving `g` from the torsor
coordinate to the group coordinate multiplies the group coordinate by `φ(g)`. -/
theorem torsorPushforwardMk_smul (φ : Fˣ →* F'ˣ) (T : GTorsor Fˣ)
    (a : F'ˣ) (g : Fˣ) (t : T.carrier) :
    torsorPushforwardMk φ T (a, g • t) = torsorPushforwardMk φ T (a * φ g, t) := by
  apply Quotient.sound
  refine ⟨g⁻¹, ?_⟩
  apply Prod.ext
  · show a * φ g = a * (φ g⁻¹)⁻¹
    rw [map_inv, inv_inv]
  · show t = g⁻¹ • (g • t)
    rw [← mul_smul, inv_mul_cancel, one_smul]

/-- The action of `F'^x` on representatives of the pushforward: left
multiplication on the group coordinate. -/
def torsorPushforwardActionFun (T : GTorsor Fˣ) (m : F'ˣ)
    (p : F'ˣ × T.carrier) : F'ˣ × T.carrier :=
  (m * p.1, p.2)

/-- The action on representatives respects the balanced-product relation. -/
theorem torsorPushforwardActionFun_respect (φ : Fˣ →* F'ˣ) (T : GTorsor Fˣ)
    (m : F'ˣ) {a b : F'ˣ × T.carrier} (h : torsorPushforwardRel φ T a b) :
    torsorPushforwardRel φ T (torsorPushforwardActionFun T m a)
      (torsorPushforwardActionFun T m b) := by
  obtain ⟨g, rfl⟩ := h
  refine ⟨g, ?_⟩
  apply Prod.ext
  · show m * (a.1 * (φ g)⁻¹) = m * a.1 * (φ g)⁻¹
    rw [mul_assoc]
  · rfl

/-- The action of `F'^x` on the pushforward. -/
def torsorPushforwardAddSmul (φ : Fˣ →* F'ˣ) (T : GTorsor Fˣ) (m : F'ˣ)
    (p : TorsorPushforward φ T) : TorsorPushforward φ T :=
  Quotient.map (torsorPushforwardActionFun T m)
    (fun _ _ h => torsorPushforwardActionFun_respect φ T m h) p

instance torsorPushforwardSMul (φ : Fˣ →* F'ˣ) (T : GTorsor Fˣ) :
    SMul F'ˣ (TorsorPushforward φ T) where
  smul := torsorPushforwardAddSmul φ T

/-- The action on the class of a representative. -/
@[simp]
theorem torsorPushforwardAddSmul_mk (φ : Fˣ →* F'ˣ) (T : GTorsor Fˣ)
    (m a : F'ˣ) (t : T.carrier) :
    m • torsorPushforwardMk φ T (a, t) = torsorPushforwardMk φ T (m * a, t) :=
  rfl

/-- The identity of `F'^x` acts trivially on the pushforward. -/
theorem torsorPushforward_one_smul (φ : Fˣ →* F'ˣ) (T : GTorsor Fˣ)
    (p : TorsorPushforward φ T) : (1 : F'ˣ) • p = p := by
  induction p using Quotient.inductionOn with
  | h p =>
      rw [torsorPushforwardAddSmul_mk, one_mul]

/-- The pushforward action is associative. -/
theorem torsorPushforward_mul_smul (φ : Fˣ →* F'ˣ) (T : GTorsor Fˣ)
    (m n : F'ˣ) (p : TorsorPushforward φ T) :
    (m * n) • p = m • (n • p) := by
  induction p using Quotient.inductionOn with
  | h p =>
      rw [torsorPushforwardAddSmul_mk, torsorPushforwardAddSmul_mk,
        torsorPushforwardAddSmul_mk, mul_assoc]

/-- The `F'^x`-action on the pushforward is a genuine `MulAction`. -/
instance torsorPushforwardMulAction (φ : Fˣ →* F'ˣ) (T : GTorsor Fˣ) :
    MulAction F'ˣ (TorsorPushforward φ T) where
  one_smul := torsorPushforward_one_smul φ T
  mul_smul := torsorPushforward_mul_smul φ T

/-- **The pushforward torsor**: the balanced product `F'^x ×^{F^x} T` is a
genuine `F'^x`-torsor. -/
def torsorPushforwardGTorsor (φ : Fˣ →* F'ˣ) (T : GTorsor Fˣ) :
    GTorsor F'ˣ where
  carrier := TorsorPushforward φ T
  inst := torsorPushforwardMulAction φ T
  nonempty := by
    obtain ⟨t⟩ := T.nonempty
    exact ⟨torsorPushforwardMk φ T (1, t)⟩
  free := by
    intro m p hp
    induction p using Quotient.inductionOn with
    | h p =>
        rw [torsorPushforwardAddSmul_mk] at hp
        have hrel : torsorPushforwardRel φ T (m * p.1, p.2) p := Quotient.exact hp
        obtain ⟨g, hg⟩ := hrel
        have hg1 : p.1 = (m * p.1) * (φ g)⁻¹ := congrArg Prod.fst hg
        have hg2 : p.2 = g • p.2 := congrArg Prod.snd hg
        have hg_eq : g = 1 := T.free g p.2 hg2.symm
        rw [hg_eq, map_one, inv_one, mul_one] at hg1
        exact mul_right_cancel (by rw [← hg1, one_mul])
  transitive := by
    intro p q
    induction p using Quotient.inductionOn with
    | h p =>
        induction q using Quotient.inductionOn with
        | h q =>
            obtain ⟨g, hg⟩ := T.transitive p.2 q.2
            refine ⟨q.1 * φ g * p.1⁻¹, ?_⟩
            rw [torsorPushforwardAddSmul_mk]
            apply Quotient.sound
            refine ⟨g, ?_⟩
            apply Prod.ext
            · show q.1 = (q.1 * φ g * p.1⁻¹ * p.1) * (φ g)⁻¹
              group
            · show q.2 = g • p.2
              exact hg.symm

/-- The canonical map from the source torsor into its pushforward:
`t ↦ [1, t]`. -/
def torsorPushforwardMap (φ : Fˣ →* F'ˣ) (T : GTorsor Fˣ) (t : T.carrier) :
    (torsorPushforwardGTorsor φ T).carrier :=
  torsorPushforwardMk φ T (1, t)

/-- The canonical map is `φ`-equivariant. -/
theorem torsorPushforwardMap_smul (φ : Fˣ →* F'ˣ) (T : GTorsor Fˣ)
    (g : Fˣ) (t : T.carrier) :
    torsorPushforwardMap φ T (g • t) = φ g • torsorPushforwardMap φ T t := by
  change torsorPushforwardMk φ T (1, g • t) =
    φ g • torsorPushforwardMk φ T (1, t)
  rw [torsorPushforwardAddSmul_mk]
  apply Quotient.sound
  refine ⟨g⁻¹, ?_⟩
  apply Prod.ext
  · show φ g * 1 = 1 * (φ g⁻¹)⁻¹
    rw [mul_one, one_mul, map_inv, inv_inv]
  · show t = g⁻¹ • (g • t)
    rw [← mul_smul, inv_mul_cancel, one_smul]

end Pushforward

/-! ## 2. Transport of a local contracted product along a value-group morphism -/

section LocalContractionTransport

variable {F : Type u} [Field F] {F' : Type u} [Field F']

/-- The representative-level map of contracted products:
`(gamma, t) ↦ (sigma gamma, e t)`. -/
def localContractionTransportFun {Γ : Type v} {Γ' : Type w}
    [AddCommGroup Γ] [AddCommGroup Γ']
    (σ : Γ →+ Γ') {T : GTorsor Fˣ} {T' : GTorsor F'ˣ}
    (e : T.carrier → T'.carrier) (p : Γ × T.carrier) : Γ' × T'.carrier :=
  (σ p.1, e p.2)

/-- The representative-level map respects the contracted-product relation. -/
theorem localContractionTransportFun_respect {Γ : Type v} {Γ' : Type w}
    [AddCommGroup Γ] [AddCommGroup Γ']
    (D : LocalValueData F Γ) (D' : LocalValueData F' Γ')
    (φ : Fˣ →* F'ˣ) (σ : Γ →+ Γ')
    (hσ : ∀ g : Fˣ, D'.deltaAdd (φ g) = σ (D.deltaAdd g))
    (T : GTorsor Fˣ) (T' : GTorsor F'ˣ) (e : T.carrier → T'.carrier)
    (he : ∀ (g : Fˣ) (t : T.carrier), e (g • t) = φ g • e t)
    {a b : Γ × T.carrier} (h : localContractionRel D T a b) :
    localContractionRel D' T'
      (localContractionTransportFun σ e a)
      (localContractionTransportFun σ e b) := by
  obtain ⟨g, rfl⟩ := h
  refine ⟨φ g, ?_⟩
  apply Prod.ext
  · show σ (a.1 - D.deltaAdd g) = σ a.1 - D'.deltaAdd (φ g)
    rw [map_sub, ← hσ g]
  · show e (g • a.2) = φ g • e a.2
    exact he g a.2

/-- **Transport of the local contracted product** along a group map and an
additive value-group map compatible with the principal maps. -/
def localContractionTransport {Γ : Type v} {Γ' : Type w}
    [AddCommGroup Γ] [AddCommGroup Γ']
    (D : LocalValueData F Γ) (D' : LocalValueData F' Γ')
    (φ : Fˣ →* F'ˣ) (σ : Γ →+ Γ')
    (hσ : ∀ g : Fˣ, D'.deltaAdd (φ g) = σ (D.deltaAdd g))
    (T : GTorsor Fˣ) (T' : GTorsor F'ˣ) (e : T.carrier → T'.carrier)
    (he : ∀ (g : Fˣ) (t : T.carrier), e (g • t) = φ g • e t)
    (p : LocalContraction D T) : LocalContraction D' T' :=
  Quotient.map (localContractionTransportFun σ e)
    (fun _ _ h => localContractionTransportFun_respect D D' φ σ hσ T T' e he h) p

/-- The transport of a class is the class of the transported representative. -/
theorem localContractionTransport_mk {Γ : Type v} {Γ' : Type w}
    [AddCommGroup Γ] [AddCommGroup Γ']
    (D : LocalValueData F Γ) (D' : LocalValueData F' Γ')
    (φ : Fˣ →* F'ˣ) (σ : Γ →+ Γ')
    (hσ : ∀ g : Fˣ, D'.deltaAdd (φ g) = σ (D.deltaAdd g))
    (T : GTorsor Fˣ) (T' : GTorsor F'ˣ) (e : T.carrier → T'.carrier)
    (he : ∀ (g : Fˣ) (t : T.carrier), e (g • t) = φ g • e t)
    (gamma : Γ) (x : T.carrier) :
    localContractionTransport D D' φ σ hσ T T' e he
        (localContractionMk D T (gamma, x)) =
      localContractionMk D' T' (σ gamma, e x) :=
  rfl

/-- **Coordinate law of the contracted-product transport**: the coordinate of
the transported point relative to the transported base point is the image of the
source coordinate under the value-group map. -/
theorem localContractionTransport_localCoord {Γ : Type v} {Γ' : Type w}
    [AddCommGroup Γ] [AddCommGroup Γ']
    (D : LocalValueData F Γ) (D' : LocalValueData F' Γ')
    (φ : Fˣ →* F'ˣ) (σ : Γ →+ Γ')
    (hσ : ∀ g : Fˣ, D'.deltaAdd (φ g) = σ (D.deltaAdd g))
    (T : GTorsor Fˣ) (T' : GTorsor F'ˣ) (e : T.carrier → T'.carrier)
    (he : ∀ (g : Fˣ) (t : T.carrier), e (g • t) = φ g • e t)
    (t : T.carrier) (p : LocalContraction D T) :
    localCoord D' T' (e t)
        (localContractionTransport D D' φ σ hσ T T' e he p) =
      σ (localCoord D T t p) := by
  induction p using Quotient.inductionOn with
  | h p =>
      rw [localContractionTransport_mk, localCoord_mk, localCoord_mk]
      have hcoord : T'.coordinate (e t) (e p.2) = φ (T.coordinate t p.2) := by
        apply GTorsor.coordinate_apply
        rw [← he (T.coordinate t p.2) t, GTorsor.coordinate_spec]
      rw [hcoord, map_add, ← hσ]

/-- The transport sends the local point with coordinate `a` to the local point
with coordinate `sigma a`. -/
theorem localContractionTransport_localPoint {Γ : Type v} {Γ' : Type w}
    [AddCommGroup Γ] [AddCommGroup Γ']
    (D : LocalValueData F Γ) (D' : LocalValueData F' Γ')
    (φ : Fˣ →* F'ˣ) (σ : Γ →+ Γ')
    (hσ : ∀ g : Fˣ, D'.deltaAdd (φ g) = σ (D.deltaAdd g))
    (T : GTorsor Fˣ) (T' : GTorsor F'ˣ) (e : T.carrier → T'.carrier)
    (he : ∀ (g : Fˣ) (t : T.carrier), e (g • t) = φ g • e t)
    (t : T.carrier) (a : Γ) :
    localContractionTransport D D' φ σ hσ T T' e he
        (localPoint D T t a) =
      localPoint D' T' (e t) (σ a) :=
  rfl

end LocalContractionTransport


variable {F : Type u} [Field F] [NumberField F]
variable {F' : Type u} [Field F'] [NumberField F']

/-! ## 3. Transport of torsor presentations -/

/-- The additive endomorphism of the integer value group given by multiplication
by a natural number: the value-group map `delta ↦ e(w) * delta` induced at a
finite place with ramification index `e(w)`. -/
def integerScaleHom (n : ℕ) : ℤ →+ ℤ where
  toFun a := (n : ℤ) * a
  map_zero' := by simp
  map_add' a b := by ring

/-- Evaluation of the integer scaling endomorphism. -/
@[simp]
theorem integerScaleHom_apply (n : ℕ) (a : ℤ) :
    integerScaleHom n a = (n : ℤ) * a :=
  rfl

/-- The finite-place principal values transform by the ramification scaling:
this is the datum's finite delta transport law, read as compatibility with
`integerScaleHom`. -/
theorem finiteDelta_scale {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (L : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F')) (g : Fˣ) :
    (D'.finiteValue w).deltaAdd (unitsMapOfRingHom L.fieldMap g) =
      integerScaleHom (L.ramificationIndex w)
        ((D.finiteValue (L.finitePlaceRestriction w)).deltaAdd g) :=
  L.deltaAdd_transport g w

/-- The archimedean principal values transform without scaling: this is the
datum's archimedean delta transport law, read as compatibility with the identity
of the real value group. -/
theorem infiniteDelta_transport_id {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (L : PlaceLocalizationTransport D D') (w : NumberField.InfinitePlace F') (g : Fˣ) :
    (D'.infiniteValue w).deltaAdd (unitsMapOfRingHom L.fieldMap g) =
      AddMonoidHom.id ℝ
        ((D.infiniteValue (L.infinitePlaceRestriction w)).deltaAdd g) :=
  L.deltaAdd_transport_infinite g w

namespace PlaceLocalizationTransport

variable {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
variable (L : PlaceLocalizationTransport D D')

/-- The transported finite local point of a presentation at a finite place of
the extension: the contracted-product point obtained by scaling the value
coordinate by the ramification index and pushing the torsor point forward. -/
def transportTorsorFinitePoint (P : TorsorPresentation D) (w : HeightOneSpectrum (𝓞 F')) :
    LocalContraction (D'.finiteValue w)
      (torsorPushforwardGTorsor (unitsMapOfRingHom L.fieldMap) P.T) :=
  localContractionTransport (D.finiteValue (L.finitePlaceRestriction w)) (D'.finiteValue w)
    (unitsMapOfRingHom L.fieldMap) (integerScaleHom (L.ramificationIndex w))
    (finiteDelta_scale L w) P.T
    (torsorPushforwardGTorsor (unitsMapOfRingHom L.fieldMap) P.T)
    (torsorPushforwardMap (unitsMapOfRingHom L.fieldMap) P.T)
    (torsorPushforwardMap_smul (unitsMapOfRingHom L.fieldMap) P.T)
    (P.finitePoint (L.finitePlaceRestriction w))

/-- The transported archimedean local point of a presentation: the value
coordinate is unchanged and the torsor point is pushed forward. -/
def transportTorsorInfinitePoint (P : TorsorPresentation D)
    (w : NumberField.InfinitePlace F') :
    LocalContraction (D'.infiniteValue w)
      (torsorPushforwardGTorsor (unitsMapOfRingHom L.fieldMap) P.T) :=
  localContractionTransport (D.infiniteValue (L.infinitePlaceRestriction w)) (D'.infiniteValue w)
    (unitsMapOfRingHom L.fieldMap) (AddMonoidHom.id ℝ)
    (infiniteDelta_transport_id L w) P.T
    (torsorPushforwardGTorsor (unitsMapOfRingHom L.fieldMap) P.T)
    (torsorPushforwardMap (unitsMapOfRingHom L.fieldMap) P.T)
    (torsorPushforwardMap_smul (unitsMapOfRingHom L.fieldMap) P.T)
    (P.infinitePoint (L.infinitePlaceRestriction w))

/-- The transported finite local point has the ramification-scaled source
coordinate. -/
theorem transportTorsorFinitePoint_localCoord (P : TorsorPresentation D)
    (w : HeightOneSpectrum (𝓞 F')) :
    localCoord (D'.finiteValue w)
        (torsorPushforwardGTorsor (unitsMapOfRingHom L.fieldMap) P.T)
        (torsorPushforwardMap (unitsMapOfRingHom L.fieldMap) P.T P.base)
        (transportTorsorFinitePoint L P w) =
      (L.ramificationIndex w : ℤ) * P.finiteCoord (L.finitePlaceRestriction w) :=
  localContractionTransport_localCoord (D.finiteValue (L.finitePlaceRestriction w))
    (D'.finiteValue w) (unitsMapOfRingHom L.fieldMap) (integerScaleHom (L.ramificationIndex w))
    (finiteDelta_scale L w) P.T
    (torsorPushforwardGTorsor (unitsMapOfRingHom L.fieldMap) P.T)
    (torsorPushforwardMap (unitsMapOfRingHom L.fieldMap) P.T)
    (torsorPushforwardMap_smul (unitsMapOfRingHom L.fieldMap) P.T)
    P.base (P.finitePoint (L.finitePlaceRestriction w))

/-- The transported archimedean local point has the source coordinate at the
restricted place. -/
theorem transportTorsorInfinitePoint_localCoord (P : TorsorPresentation D)
    (w : NumberField.InfinitePlace F') :
    localCoord (D'.infiniteValue w)
        (torsorPushforwardGTorsor (unitsMapOfRingHom L.fieldMap) P.T)
        (torsorPushforwardMap (unitsMapOfRingHom L.fieldMap) P.T P.base)
        (transportTorsorInfinitePoint L P w) =
      P.infiniteCoord (L.infinitePlaceRestriction w) :=
  localContractionTransport_localCoord (D.infiniteValue (L.infinitePlaceRestriction w))
    (D'.infiniteValue w) (unitsMapOfRingHom L.fieldMap) (AddMonoidHom.id ℝ)
    (infiniteDelta_transport_id L w) P.T
    (torsorPushforwardGTorsor (unitsMapOfRingHom L.fieldMap) P.T)
    (torsorPushforwardMap (unitsMapOfRingHom L.fieldMap) P.T)
    (torsorPushforwardMap_smul (unitsMapOfRingHom L.fieldMap) P.T)
    P.base (P.infinitePoint (L.infinitePlaceRestriction w))

/-- **Transport of a torsor presentation**: the underlying torsor is pushed
forward along the datum's unit map, the base point becomes `[1, base]`, and the
local points are the transported contracted-product points.  The finite-support
condition is preserved. -/
def transportTorsorPresentation (P : TorsorPresentation D) : TorsorPresentation D' where
  T := torsorPushforwardGTorsor (unitsMapOfRingHom L.fieldMap) P.T
  base := torsorPushforwardMap (unitsMapOfRingHom L.fieldMap) P.T P.base
  finitePoint := transportTorsorFinitePoint L P
  infinitePoint := transportTorsorInfinitePoint L P
  finite_support := by
    refine (L.finitePlaceRestriction_finite P.finite_support.toFinset).subset ?_
    intro w hw
    rw [Set.mem_setOf_eq] at hw ⊢
    rw [transportTorsorFinitePoint_localCoord L P w] at hw
    refine P.finite_support.mem_toFinset.mpr ?_
    show P.finiteCoord (L.finitePlaceRestriction w) ≠ 0
    intro hc
    exact hw (by rw [hc, mul_zero])

@[simp]
theorem transportTorsorPresentation_T (P : TorsorPresentation D) :
    (L.transportTorsorPresentation P).T =
      torsorPushforwardGTorsor (unitsMapOfRingHom L.fieldMap) P.T :=
  rfl

@[simp]
theorem transportTorsorPresentation_base (P : TorsorPresentation D) :
    (L.transportTorsorPresentation P).base =
      torsorPushforwardMap (unitsMapOfRingHom L.fieldMap) P.T P.base :=
  rfl

@[simp]
theorem transportTorsorPresentation_finitePoint (P : TorsorPresentation D)
    (w : HeightOneSpectrum (𝓞 F')) :
    (L.transportTorsorPresentation P).finitePoint w =
      transportTorsorFinitePoint L P w :=
  rfl

@[simp]
theorem transportTorsorPresentation_infinitePoint (P : TorsorPresentation D)
    (w : NumberField.InfinitePlace F') :
    (L.transportTorsorPresentation P).infinitePoint w =
      transportTorsorInfinitePoint L P w :=
  rfl

/-- **Finite-coordinate transport law**: the transported presentation's finite
coordinate at a place `w` of the extension is the ramification multiple of the
source coordinate at the restricted place. -/
theorem transportTorsorPresentation_finiteCoord (P : TorsorPresentation D)
    (w : HeightOneSpectrum (𝓞 F')) :
    (L.transportTorsorPresentation P).finiteCoord w =
      (L.ramificationIndex w : ℤ) * P.finiteCoord (L.finitePlaceRestriction w) :=
  transportTorsorFinitePoint_localCoord L P w

/-- **Archimedean-coordinate transport law**: the transported presentation's
archimedean coordinate at a place of the extension is the source coordinate at
the restricted place. -/
theorem transportTorsorPresentation_infiniteCoord (P : TorsorPresentation D)
    (w : NumberField.InfinitePlace F') :
    (L.transportTorsorPresentation P).infiniteCoord w =
      P.infiniteCoord (L.infinitePlaceRestriction w) :=
  transportTorsorInfinitePoint_localCoord L P w

/-- **Non-triviality at ramified places.**  If the ramification index at a
finite place is not one and the source coordinate at the restricted place is
nonzero, then the transported finite coordinate genuinely differs from the
source coordinate: no identity transport is substituted at ramified places. -/
theorem transportTorsorPresentation_finiteCoord_ne_of_ramification
    (P : TorsorPresentation D) (w : HeightOneSpectrum (𝓞 F'))
    (he : L.ramificationIndex w ≠ 1)
    (hP : P.finiteCoord (L.finitePlaceRestriction w) ≠ 0) :
    (L.transportTorsorPresentation P).finiteCoord w ≠
      P.finiteCoord (L.finitePlaceRestriction w) := by
  rw [transportTorsorPresentation_finiteCoord]
  intro h
  have h' : ((L.ramificationIndex w : ℤ) - 1) *
      P.finiteCoord (L.finitePlaceRestriction w) = 0 := by
    rw [sub_mul, one_mul, h, sub_self]
  have hcoef : (L.ramificationIndex w : ℤ) - 1 = 0 := by
    rcases mul_eq_zero.mp h' with h1 | h2
    · exact h1
    · exact absurd h2 hP
  have hnat : L.ramificationIndex w = 1 := by omega
  exact he hnat

end PlaceLocalizationTransport

/-! ## 4. Transport of torsor arrows -/

/-- The finite-place local inclusion condition of a torsor arrow, as a function
of its degree and multiplier. -/
def torsorArrowFiniteCondition {D : GlobalPlaceData F}
    (P₁ P₂ : TorsorPresentation D) (n : ℕ) (f : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  (D.finiteValue v).localInclusion n f (P₁.finiteCoord v) (P₂.finiteCoord v)

/-- The archimedean local inclusion condition of a torsor arrow, as a function
of its degree and multiplier. -/
def torsorArrowInfiniteCondition {D : GlobalPlaceData F}
    (P₁ P₂ : TorsorPresentation D) (n : ℕ) (f : Fˣ)
    (w : NumberField.InfinitePlace F) : Prop :=
  (D.infiniteValue w).localInclusion n f (P₁.infiniteCoord w) (P₂.infiniteCoord w)

namespace PlaceLocalizationTransport

variable {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
variable (L : PlaceLocalizationTransport D D')

/-- **Transport of a torsor arrow**: the degree is unchanged, the multiplier is
the image under the datum's unit map, and the local integrality conditions are
the transported source conditions (using the datum's cone transport). -/
def transportTorsorArrow {P₁ P₂ : TorsorPresentation D}
    (ψ : TorsorArrow P₁ P₂) :
    TorsorArrow (L.transportTorsorPresentation P₁)
      (L.transportTorsorPresentation P₂) where
  degree := ψ.degree
  positive_degree := ψ.positive_degree
  multiplier := unitsMapOfRingHom L.fieldMap ψ.multiplier
  finite_incl w := by
    have hsource := ψ.finite_incl (L.finitePlaceRestriction w)
    have hcone := L.finiteCone_transport w hsource
    change (D'.finiteValue w).deltaAdd (unitsMapOfRingHom L.fieldMap ψ.multiplier) +
        ψ.degree • (L.transportTorsorPresentation P₁).finiteCoord w -
        (L.transportTorsorPresentation P₂).finiteCoord w ∈ (D'.finiteValue w).cone
    rw [L.deltaAdd_transport ψ.multiplier w,
      transportTorsorPresentation_finiteCoord L P₁ w,
      transportTorsorPresentation_finiteCoord L P₂ w]
    have harith :
        (L.ramificationIndex w : ℤ) *
            (D.finiteValue (L.finitePlaceRestriction w)).deltaAdd ψ.multiplier +
          ψ.degree • ((L.ramificationIndex w : ℤ) *
            P₁.finiteCoord (L.finitePlaceRestriction w)) -
          (L.ramificationIndex w : ℤ) *
            P₂.finiteCoord (L.finitePlaceRestriction w) =
        L.ramificationIndex w •
          ((D.finiteValue (L.finitePlaceRestriction w)).deltaAdd ψ.multiplier +
            ψ.degree • P₁.finiteCoord (L.finitePlaceRestriction w) -
            P₂.finiteCoord (L.finitePlaceRestriction w)) := by
      simp only [nsmul_eq_mul]
      ring
    rw [harith]
    exact hcone
  infinite_incl w := by
    have hsource := ψ.infinite_incl (L.infinitePlaceRestriction w)
    have hcone := L.infiniteCone_transport w hsource
    change (D'.infiniteValue w).deltaAdd (unitsMapOfRingHom L.fieldMap ψ.multiplier) +
        ψ.degree • (L.transportTorsorPresentation P₁).infiniteCoord w -
        (L.transportTorsorPresentation P₂).infiniteCoord w ∈ (D'.infiniteValue w).cone
    rw [L.deltaAdd_transport_infinite ψ.multiplier w,
      transportTorsorPresentation_infiniteCoord L P₁ w,
      transportTorsorPresentation_infiniteCoord L P₂ w]
    exact hcone

@[simp]
theorem transportTorsorArrow_degree {P₁ P₂ : TorsorPresentation D}
    (ψ : TorsorArrow P₁ P₂) :
    (L.transportTorsorArrow ψ).degree = ψ.degree :=
  rfl

@[simp]
theorem transportTorsorArrow_multiplier {P₁ P₂ : TorsorPresentation D}
    (ψ : TorsorArrow P₁ P₂) :
    (L.transportTorsorArrow ψ).multiplier =
      unitsMapOfRingHom L.fieldMap ψ.multiplier :=
  rfl

/-- The transport preserves identity arrows. -/
@[simp]
theorem transportTorsorArrow_id (P : TorsorPresentation D) :
    L.transportTorsorArrow (TorsorArrow.id P) =
      TorsorArrow.id (L.transportTorsorPresentation P) := by
  apply TorsorArrow.ext
  · rfl
  · exact map_one (unitsMapOfRingHom L.fieldMap)

/-- The transport preserves composition of torsor arrows. -/
theorem transportTorsorArrow_comp {P₁ P₂ P₃ : TorsorPresentation D}
    (φ : TorsorArrow P₁ P₂) (ψ : TorsorArrow P₂ P₃) :
    L.transportTorsorArrow (TorsorArrow.comp φ ψ) =
      TorsorArrow.comp (L.transportTorsorArrow φ) (L.transportTorsorArrow ψ) := by
  apply TorsorArrow.ext
  · rfl
  · change unitsMapOfRingHom L.fieldMap (ψ.multiplier * φ.multiplier ^ ψ.degree) =
      unitsMapOfRingHom L.fieldMap ψ.multiplier *
        (unitsMapOfRingHom L.fieldMap φ.multiplier) ^ ψ.degree
    rw [map_mul, map_pow]

/-! ## 5. Compatibility with a change of base points -/

/-- The transported base point of a rebased presentation is the rebased
transported base point. -/
theorem transportTorsorPresentation_rebase_base
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (L : PlaceLocalizationTransport D D')
    (hD : D.HasFiniteSupport) (hD' : D'.HasFiniteSupport)
    (P : TorsorPresentation D) (h : Fˣ) :
    (L.transportTorsorPresentation (TorsorPresentation.rebase hD P h)).base =
      (TorsorPresentation.rebase hD' (L.transportTorsorPresentation P)
        (unitsMapOfRingHom L.fieldMap h)).base := by
  show torsorPushforwardMk (unitsMapOfRingHom L.fieldMap) P.T (1, h • P.base) =
    unitsMapOfRingHom L.fieldMap h •
      torsorPushforwardMk (unitsMapOfRingHom L.fieldMap) P.T (1, P.base)
  rw [torsorPushforwardAddSmul_mk]
  apply Quotient.sound
  refine ⟨h⁻¹, ?_⟩
  apply Prod.ext
  · show (unitsMapOfRingHom L.fieldMap h) * 1 =
      1 * (unitsMapOfRingHom L.fieldMap h⁻¹)⁻¹
    rw [mul_one, one_mul, map_inv, inv_inv]
  · show P.base = h⁻¹ • (h • P.base)
    rw [← mul_smul, inv_mul_cancel, one_smul]

/-- The finite coordinates of the transported rebased presentation agree with
those of the rebase of the transported presentation. -/
theorem transportTorsorPresentation_rebase_finiteCoord
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (L : PlaceLocalizationTransport D D')
    (hD : D.HasFiniteSupport) (hD' : D'.HasFiniteSupport)
    (P : TorsorPresentation D) (h : Fˣ) (w : HeightOneSpectrum (𝓞 F')) :
    (L.transportTorsorPresentation (TorsorPresentation.rebase hD P h)).finiteCoord w =
      (TorsorPresentation.rebase hD' (L.transportTorsorPresentation P)
        (unitsMapOfRingHom L.fieldMap h)).finiteCoord w := by
  rw [transportTorsorPresentation_finiteCoord L (TorsorPresentation.rebase hD P h) w,
    TorsorPresentation.rebase_finiteCoord hD P h (L.finitePlaceRestriction w),
    TorsorPresentation.rebase_finiteCoord hD' (L.transportTorsorPresentation P)
      (unitsMapOfRingHom L.fieldMap h) w,
    transportTorsorPresentation_finiteCoord L P w,
    L.finiteDelta_transport h w]
  ring

/-- The archimedean coordinates of the transported rebased presentation agree
with those of the rebase of the transported presentation. -/
theorem transportTorsorPresentation_rebase_infiniteCoord
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (L : PlaceLocalizationTransport D D')
    (hD : D.HasFiniteSupport) (hD' : D'.HasFiniteSupport)
    (P : TorsorPresentation D) (h : Fˣ) (w : NumberField.InfinitePlace F') :
    (L.transportTorsorPresentation (TorsorPresentation.rebase hD P h)).infiniteCoord w =
      (TorsorPresentation.rebase hD' (L.transportTorsorPresentation P)
        (unitsMapOfRingHom L.fieldMap h)).infiniteCoord w := by
  rw [transportTorsorPresentation_infiniteCoord L (TorsorPresentation.rebase hD P h) w,
    TorsorPresentation.rebase_infiniteCoord hD P h (L.infinitePlaceRestriction w),
    TorsorPresentation.rebase_infiniteCoord hD' (L.transportTorsorPresentation P)
      (unitsMapOfRingHom L.fieldMap h) w,
    transportTorsorPresentation_infiniteCoord L P w,
    L.infiniteDelta_transport h w]

/-- The degree of the transported rebased arrow agrees with the degree of the
rebase of the transported arrow. -/
theorem transportTorsorArrow_rebase_degree
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (L : PlaceLocalizationTransport D D')
    (hD : D.HasFiniteSupport) (hD' : D'.HasFiniteSupport)
    (h₁ h₂ : Fˣ) {P₁ P₂ : TorsorPresentation D} (ψ : TorsorArrow P₁ P₂) :
    (L.transportTorsorArrow (TorsorArrow.rebaseArrow hD h₁ h₂ ψ)).degree =
      (TorsorArrow.rebaseArrow hD' (unitsMapOfRingHom L.fieldMap h₁)
        (unitsMapOfRingHom L.fieldMap h₂) (L.transportTorsorArrow ψ)).degree :=
  rfl

/-- The multiplier of the transported rebased arrow agrees with the multiplier
of the rebase of the transported arrow. -/
theorem transportTorsorArrow_rebase_multiplier
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (L : PlaceLocalizationTransport D D')
    (hD : D.HasFiniteSupport) (hD' : D'.HasFiniteSupport)
    (h₁ h₂ : Fˣ) {P₁ P₂ : TorsorPresentation D} (ψ : TorsorArrow P₁ P₂) :
    (L.transportTorsorArrow (TorsorArrow.rebaseArrow hD h₁ h₂ ψ)).multiplier =
      (TorsorArrow.rebaseArrow hD' (unitsMapOfRingHom L.fieldMap h₁)
        (unitsMapOfRingHom L.fieldMap h₂) (L.transportTorsorArrow ψ)).multiplier := by
  show unitsMapOfRingHom L.fieldMap (h₂⁻¹ * ψ.multiplier * h₁ ^ ψ.degree) =
    (unitsMapOfRingHom L.fieldMap h₂)⁻¹ *
      unitsMapOfRingHom L.fieldMap ψ.multiplier *
      (unitsMapOfRingHom L.fieldMap h₁) ^ ψ.degree
  simp only [map_mul, map_inv, map_pow]

/-- The finite local inclusion condition of the transported rebased arrow is
equivalent to that of the rebase of the transported arrow, at the transported
presentations' coordinates. -/
theorem transportTorsorArrow_rebase_finite_condition_iff
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (L : PlaceLocalizationTransport D D')
    (hD : D.HasFiniteSupport) (hD' : D'.HasFiniteSupport)
    (h₁ h₂ : Fˣ) {P₁ P₂ : TorsorPresentation D} (ψ : TorsorArrow P₁ P₂)
    (w : HeightOneSpectrum (𝓞 F')) :
    torsorArrowFiniteCondition
        (L.transportTorsorPresentation (TorsorPresentation.rebase hD P₁ h₁))
        (L.transportTorsorPresentation (TorsorPresentation.rebase hD P₂ h₂))
        ψ.degree
        (unitsMapOfRingHom L.fieldMap (h₂⁻¹ * ψ.multiplier * h₁ ^ ψ.degree)) w ↔
      torsorArrowFiniteCondition
        (TorsorPresentation.rebase hD' (L.transportTorsorPresentation P₁)
          (unitsMapOfRingHom L.fieldMap h₁))
        (TorsorPresentation.rebase hD' (L.transportTorsorPresentation P₂)
          (unitsMapOfRingHom L.fieldMap h₂))
        ψ.degree
        ((unitsMapOfRingHom L.fieldMap h₂)⁻¹ *
          unitsMapOfRingHom L.fieldMap ψ.multiplier *
          (unitsMapOfRingHom L.fieldMap h₁) ^ ψ.degree) w := by
  unfold torsorArrowFiniteCondition
  rw [transportTorsorPresentation_rebase_finiteCoord L hD hD' P₁ h₁ w,
    transportTorsorPresentation_rebase_finiteCoord L hD hD' P₂ h₂ w]
  rw [show unitsMapOfRingHom L.fieldMap (h₂⁻¹ * ψ.multiplier * h₁ ^ ψ.degree) =
      (unitsMapOfRingHom L.fieldMap h₂)⁻¹ * unitsMapOfRingHom L.fieldMap ψ.multiplier *
        (unitsMapOfRingHom L.fieldMap h₁) ^ ψ.degree from by
    simp only [map_mul, map_inv, map_pow]]

/-- The archimedean local inclusion condition of the transported rebased arrow
is equivalent to that of the rebase of the transported arrow, at the transported
presentations' coordinates. -/
theorem transportTorsorArrow_rebase_infinite_condition_iff
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (L : PlaceLocalizationTransport D D')
    (hD : D.HasFiniteSupport) (hD' : D'.HasFiniteSupport)
    (h₁ h₂ : Fˣ) {P₁ P₂ : TorsorPresentation D} (ψ : TorsorArrow P₁ P₂)
    (w : NumberField.InfinitePlace F') :
    torsorArrowInfiniteCondition
        (L.transportTorsorPresentation (TorsorPresentation.rebase hD P₁ h₁))
        (L.transportTorsorPresentation (TorsorPresentation.rebase hD P₂ h₂))
        ψ.degree
        (unitsMapOfRingHom L.fieldMap (h₂⁻¹ * ψ.multiplier * h₁ ^ ψ.degree)) w ↔
      torsorArrowInfiniteCondition
        (TorsorPresentation.rebase hD' (L.transportTorsorPresentation P₁)
          (unitsMapOfRingHom L.fieldMap h₁))
        (TorsorPresentation.rebase hD' (L.transportTorsorPresentation P₂)
          (unitsMapOfRingHom L.fieldMap h₂))
        ψ.degree
        ((unitsMapOfRingHom L.fieldMap h₂)⁻¹ *
          unitsMapOfRingHom L.fieldMap ψ.multiplier *
          (unitsMapOfRingHom L.fieldMap h₁) ^ ψ.degree) w := by
  unfold torsorArrowInfiniteCondition
  rw [transportTorsorPresentation_rebase_infiniteCoord L hD hD' P₁ h₁ w,
    transportTorsorPresentation_rebase_infiniteCoord L hD hD' P₂ h₂ w]
  rw [show unitsMapOfRingHom L.fieldMap (h₂⁻¹ * ψ.multiplier * h₁ ^ ψ.degree) =
      (unitsMapOfRingHom L.fieldMap h₂)⁻¹ * unitsMapOfRingHom L.fieldMap ψ.multiplier *
        (unitsMapOfRingHom L.fieldMap h₁) ^ ψ.degree from by
    simp only [map_mul, map_inv, map_pow]]

/-! ## 6. The ideal family of a transported presentation -/

/-- **Object-level identification.**  The global ideal family of the transported
torsor presentation, in `(n, f)` coordinates, is the transport of the global
ideal family of the source presentation by the task-22 ideal-family transport.
This is an exact equality of global ideal-family objects. -/
theorem presentationToIdealFamily_transport
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (L : PlaceLocalizationTransport D D') (P : TorsorPresentation D) :
    presentationToIdealFamily D' (L.transportTorsorPresentation P) =
      L.transportObject (presentationToIdealFamily D P) := by
  apply GlobalIdealFamily.ext
  · ext w
    rw [presentationToIdealFamily_finite D' (L.transportTorsorPresentation P) w,
      transportTorsorPresentation_finiteCoord L P w,
      transportObject_finite_apply L (presentationToIdealFamily D P) w,
      presentationToIdealFamily_finite D P (L.finitePlaceRestriction w)]
  · funext w
    rw [presentationToIdealFamily_infinite D' (L.transportTorsorPresentation P) w,
      transportTorsorPresentation_infiniteCoord L P w,
      transportObject_infinite_apply L (presentationToIdealFamily D P) w,
      presentationToIdealFamily_infinite D P (L.infinitePlaceRestriction w)]

/-- The degree of the ideal-family morphism of the transported arrow agrees with
the degree of the transport of the ideal-family morphism of the source arrow. -/
theorem presentationArrowToIdealFamilyHom_transport_degree
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (L : PlaceLocalizationTransport D D')
    {P₁ P₂ : TorsorPresentation D} (ψ : TorsorArrow P₁ P₂) :
    (presentationArrowToIdealFamilyHom D' (L.transportTorsorArrow ψ)).degree =
      (L.transportHom (presentationArrowToIdealFamilyHom D ψ)).degree :=
  rfl

/-- The multiplier of the ideal-family morphism of the transported arrow agrees
with the multiplier of the transport of the ideal-family morphism of the source
arrow. -/
theorem presentationArrowToIdealFamilyHom_transport_multiplier
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (L : PlaceLocalizationTransport D D')
    {P₁ P₂ : TorsorPresentation D} (ψ : TorsorArrow P₁ P₂) :
    (presentationArrowToIdealFamilyHom D' (L.transportTorsorArrow ψ)).multiplier =
      (L.transportHom (presentationArrowToIdealFamilyHom D ψ)).multiplier :=
  rfl

end PlaceLocalizationTransport

/-! ## 6b. Ideal-family morphism conditions of a transported presentation -/

/-- The finite-place local inclusion condition of a morphism of global ideal
families, as a function of its degree and multiplier. -/
def idealFamilyHomFiniteCondition {D : GlobalPlaceData F}
    (J₁ J₂ : GlobalIdealFamily F) (n : ℕ) (f : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  (D.finiteValue v).localInclusion n f (J₁.finite v) (J₂.finite v)

/-- The archimedean local inclusion condition of a morphism of global ideal
families, as a function of its degree and multiplier. -/
def idealFamilyHomInfiniteCondition {D : GlobalPlaceData F}
    (J₁ J₂ : GlobalIdealFamily F) (n : ℕ) (f : Fˣ)
    (w : NumberField.InfinitePlace F) : Prop :=
  (D.infiniteValue w).localInclusion n f (J₁.infinite w) (J₂.infinite w)

/-- **Finite-place arrow-condition comparison.**  At a finite place of the
extension, the finite local inclusion condition of the ideal-family morphism of
the transported arrow is equivalent to the condition of the transported
ideal-family morphism of the source arrow, using the object identification
`presentationToIdealFamily_transport`. -/
theorem presentationArrowToIdealFamilyHom_transport_finite_condition_iff
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (L : PlaceLocalizationTransport D D')
    {P₁ P₂ : TorsorPresentation D} (ψ : TorsorArrow P₁ P₂)
    (v : HeightOneSpectrum (𝓞 F')) :
    idealFamilyHomFiniteCondition (D := D')
        (presentationToIdealFamily D' (L.transportTorsorPresentation P₁))
        (presentationToIdealFamily D' (L.transportTorsorPresentation P₂))
        ψ.degree (unitsMapOfRingHom L.fieldMap ψ.multiplier) v ↔
      idealFamilyHomFiniteCondition (D := D')
        (L.transportObject (presentationToIdealFamily D P₁))
        (L.transportObject (presentationToIdealFamily D P₂))
        ψ.degree (unitsMapOfRingHom L.fieldMap ψ.multiplier) v := by
  unfold idealFamilyHomFiniteCondition
  rw [PlaceLocalizationTransport.presentationToIdealFamily_transport L P₁,
    PlaceLocalizationTransport.presentationToIdealFamily_transport L P₂]

/-- **Archimedean arrow-condition comparison.**  At an archimedean place of the
extension, the archimedean local inclusion condition of the ideal-family
morphism of the transported arrow is equivalent to the condition of the
transported ideal-family morphism of the source arrow. -/
theorem presentationArrowToIdealFamilyHom_transport_infinite_condition_iff
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (L : PlaceLocalizationTransport D D')
    {P₁ P₂ : TorsorPresentation D} (ψ : TorsorArrow P₁ P₂)
    (w : NumberField.InfinitePlace F') :
    idealFamilyHomInfiniteCondition (D := D')
        (presentationToIdealFamily D' (L.transportTorsorPresentation P₁))
        (presentationToIdealFamily D' (L.transportTorsorPresentation P₂))
        ψ.degree (unitsMapOfRingHom L.fieldMap ψ.multiplier) w ↔
      idealFamilyHomInfiniteCondition (D := D')
        (L.transportObject (presentationToIdealFamily D P₁))
        (L.transportObject (presentationToIdealFamily D P₂))
        ψ.degree (unitsMapOfRingHom L.fieldMap ψ.multiplier) w := by
  unfold idealFamilyHomInfiniteCondition
  rw [PlaceLocalizationTransport.presentationToIdealFamily_transport L P₁,
    PlaceLocalizationTransport.presentationToIdealFamily_transport L P₂]

/-! ## 7. Specialization to the actual number-field place data -/

section NumberFieldSpecialization

variable (L : PlaceLocalizationTransport
  (numberFieldGlobalPlaceData (F := F)) (numberFieldGlobalPlaceData (F := F')))

/-- **Number-field specialization of the object identification.**  For the
actual number-field place data, the global ideal family of the transported torsor
presentation is the transport of the global ideal family of the source
presentation. -/
theorem numberFieldPresentationToIdealFamily_transport
    (P : TorsorPresentation (numberFieldGlobalPlaceData (F := F))) :
    presentationToIdealFamily (numberFieldGlobalPlaceData (F := F'))
        (L.transportTorsorPresentation P) =
      L.transportObject
        (presentationToIdealFamily (numberFieldGlobalPlaceData (F := F)) P) :=
  PlaceLocalizationTransport.presentationToIdealFamily_transport L P

/-- **Number-field specialization of the arrow identification.**  For the actual
number-field place data, the ideal-family morphism of the transported arrow has
the same degree as the transported ideal-family morphism of the source arrow. -/
theorem numberFieldPresentationArrowToIdealFamilyHom_transport_degree
    {P₁ P₂ : TorsorPresentation (numberFieldGlobalPlaceData (F := F))}
    (ψ : TorsorArrow P₁ P₂) :
    (presentationArrowToIdealFamilyHom (numberFieldGlobalPlaceData (F := F'))
      (L.transportTorsorArrow ψ)).degree =
      (L.transportHom (presentationArrowToIdealFamilyHom
        (numberFieldGlobalPlaceData (F := F)) ψ)).degree :=
  PlaceLocalizationTransport.presentationArrowToIdealFamilyHom_transport_degree L ψ

/-- **Number-field specialization of the arrow identification, multipliers.** -/
theorem numberFieldPresentationArrowToIdealFamilyHom_transport_multiplier
    {P₁ P₂ : TorsorPresentation (numberFieldGlobalPlaceData (F := F))}
    (ψ : TorsorArrow P₁ P₂) :
    (presentationArrowToIdealFamilyHom (numberFieldGlobalPlaceData (F := F'))
      (L.transportTorsorArrow ψ)).multiplier =
      (L.transportHom (presentationArrowToIdealFamilyHom
        (numberFieldGlobalPlaceData (F := F)) ψ)).multiplier :=
  PlaceLocalizationTransport.presentationArrowToIdealFamilyHom_transport_multiplier L ψ

end NumberFieldSpecialization

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
