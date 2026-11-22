import LeanFormal.IUT.IUTII.Frobenioid.Example36TorsorPresentation
import LeanFormal.IUT.IUTII.Frobenioid.Example36NumberFieldPlaceData

/-!
# The torsor-ideal family equivalence of IUT III, Example 3.6

This module proves the coordinate-level equivalence between the global
ideal-family category of Example 3.6 (`Example36GlobalIdealFamily`,
`GlobalIdealFamily D` with `Hom D`) and the torsor-presentation category
(`Example36TorsorPresentation`, `TorsorPresentation D` with `TorsorArrow`).

The equivalence is the two-functor dictionary of the handoff
(n8-distilled-01, chapter 1 F-G):

* the *ideal-family to presentation* functor `idealFamilyToPresentation D`:
  the underlying `F^x`-torsor is the regular torsor `GTorsor.regular F^x`
  with base point `1`; the local point at a finite place is the point of the
  local contraction with value coordinate equal to the ideal-family exponent
  `J.finite v`; at an archimedean place it is the point with coordinate
  `J.infinite w`; the almost-everywhere-standard condition is exactly finite
  support of the `Finsupp` `J.finite`;
* the *presentation to ideal-family* functor `presentationToIdealFamily D`:
  the finite coordinates are the presentation's finite coordinates packaged as
  a `Finsupp` via the presentation's finite-support condition; the
  archimedean coordinates are the presentation's archimedean coordinates;
* the object roundtrip `presentationToIdealFamily D (idealFamilyToPresentation D J) = J`
  is exact;
* the natural isomorphism `F (G P) ≅ P` is realized by transporting along
  the torsor equivalence from the regular torsor to `P.T` (the equivariant map
  sending `1` to `P.base`), together with the induced map on local
  contractions; the base point and all local points match
  (`counitIso`, `counitIso_finitePoint`, ...);
* the arrow-level dictionary `idealFamilyHomEquivTorsorArrow` is a bijection
  between `Hom D J₁ J₂` and `TorsorArrow (F J₁) (F J₂)` preserving degree
  and multiplier, so the functor is full and faithful; every presentation is
  isomorphic to one in the image of the object functor, so the functor is
  essentially surjective.  The bundled statement is
  `coordinateEquivalence` / `torsorIdealFamilyEquivalence`.

Everything is at the coordinate level: `TorsorArrow` records a degree, a
global multiplier and the local integrality conditions between coordinates
relative to the chosen base points.  This module does not construct the
actual equivariant maps on the source objects (`Example36TorsorArrowRealization`
is a separate, not imported, obligation), does not construct the source Hodge
theater, and does not identify any source theta-pilot object.

Boundary: the equivalence is between the two explicit coordinate categories
frozen in Layers 2-3.  It does not assert a global Frobenioid equivalence, an
arithmetic identification of the presentation functor, or any statement about
the source data of IUT.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open scoped NumberField
open IsDedekindDomain NumberField

universe u v

/-! ## 1. Transport of local contractions along torsor maps -/

section ContractionTransport

variable {F : Type u} {Gamma : Type v} [Field F] [AddCommGroup Gamma]
variable (D : LocalValueData F Gamma) (T₁ T₂ : GTorsor Fˣ)

/-- The representative-level action of a torsor map on the local contraction:
the value coordinate is untouched and the torsor coordinate is mapped. -/
def localContractionMapFun (e : T₁.carrier → T₂.carrier) (p : Gamma × T₁.carrier) :
    Gamma × T₂.carrier :=
  (p.1, e p.2)

/-- A map of torsors that is equivariant for the `F^x`-actions respects the
contracted-product relations. -/
theorem localContractionMapFun_respect (e : T₁.carrier → T₂.carrier)
    (he : ∀ (g : Fˣ) (t : T₁.carrier), e (g • t) = g • e t)
    {a b : Gamma × T₁.carrier} (h : localContractionRel D T₁ a b) :
    localContractionRel D T₂ (localContractionMapFun T₁ T₂ e a)
      (localContractionMapFun T₁ T₂ e b) := by
  obtain ⟨g, rfl⟩ := h
  refine ⟨g, ?_⟩
  ext
  · rfl
  · change e (g • a.2) = g • e a.2
    exact he g a.2

/-- The induced map of local contractions associated to an equivariant map of
`F^x`-torsors: `[gamma, t] ↦ [gamma, e t]`. -/
def localContractionMap (e : T₁.carrier → T₂.carrier)
    (he : ∀ (g : Fˣ) (t : T₁.carrier), e (g • t) = g • e t) :
    LocalContraction D T₁ → LocalContraction D T₂ :=
  Quotient.map (localContractionMapFun T₁ T₂ e)
    (fun _ _ h => localContractionMapFun_respect D T₁ T₂ e he h)

/-- The induced map on the class of a representative. -/
@[simp]
theorem localContractionMap_mk (e : T₁.carrier → T₂.carrier)
    (he : ∀ (g : Fˣ) (t : T₁.carrier), e (g • t) = g • e t)
    (p : Gamma × T₁.carrier) :
    localContractionMap D T₁ T₂ e he (localContractionMk D T₁ p) =
      localContractionMk D T₂ (p.1, e p.2) :=
  rfl

/-- The induced map sends the point with coordinate `a` relative to `t` to
the point with coordinate `a` relative to `e t`. -/
@[simp]
theorem localContractionMap_localPoint (e : T₁.carrier → T₂.carrier)
    (he : ∀ (g : Fˣ) (t : T₁.carrier), e (g • t) = g • e t)
    (t : T₁.carrier) (a : Gamma) :
    localContractionMap D T₁ T₂ e he (localPoint D T₁ t a) =
      localPoint D T₂ (e t) a :=
  rfl

/-- The induced map of local contractions is compatible with the local
coordinates: the coordinate of the image relative to `e t` equals the
coordinate of the original point relative to `t`. -/
theorem localCoord_map (e : T₁.carrier → T₂.carrier)
    (he : ∀ (g : Fˣ) (t : T₁.carrier), e (g • t) = g • e t)
    (t : T₁.carrier) (p : LocalContraction D T₁) :
    localCoord D T₂ (e t) (localContractionMap D T₁ T₂ e he p) =
      localCoord D T₁ t p := by
  induction p using Quotient.inductionOn with
  | h p =>
      rw [localCoord_mk, localContractionMap_mk, localCoord_mk]
      have hcoord : T₂.coordinate (e t) (e p.2) = T₁.coordinate t p.2 := by
        have h : T₁.coordinate t p.2 • e t = e p.2 := by
          rw [← he, GTorsor.coordinate_spec]
        exact GTorsor.coordinate_apply T₂ (e t) h
      rw [hcoord]

/-- The induced map of the identity torsor map is the identity. -/
theorem localContractionMap_id (p : LocalContraction D T₁) :
    localContractionMap D T₁ T₁ id (fun _ _ => rfl) p = p := by
  induction p using Quotient.inductionOn with
  | h p =>
      change Quotient.mk (localContractionSetoid D T₁) (localContractionMapFun T₁ T₁ id p) =
        Quotient.mk (localContractionSetoid D T₁) p
      rfl

/-- Induced maps of local contractions compose. -/
theorem localContractionMap_comp {T₃ : GTorsor Fˣ}
    (e₁ : T₁.carrier → T₂.carrier)
    (he₁ : ∀ (g : Fˣ) (t : T₁.carrier), e₁ (g • t) = g • e₁ t)
    (e₂ : T₂.carrier → T₃.carrier)
    (he₂ : ∀ (g : Fˣ) (t : T₂.carrier), e₂ (g • t) = g • e₂ t)
    (p : LocalContraction D T₁) :
    localContractionMap D T₂ T₃ e₂ he₂ (localContractionMap D T₁ T₂ e₁ he₁ p) =
      localContractionMap D T₁ T₃ (e₂ ∘ e₁)
        (fun g t => by
          change e₂ (e₁ (g • t)) = g • e₂ (e₁ t)
          rw [he₁, he₂]) p := by
  induction p using Quotient.inductionOn with
  | h p =>
      change Quotient.mk (localContractionSetoid D T₃)
          (localContractionMapFun T₂ T₃ e₂ (localContractionMapFun T₁ T₂ e₁ p)) =
        Quotient.mk (localContractionSetoid D T₃)
          (localContractionMapFun T₁ T₃ (e₂ ∘ e₁) p)
      rfl

/-- The induced map of an injective equivariant map of torsors is injective. -/
theorem localContractionMap_injective (e : T₁.carrier ≃ T₂.carrier)
    (he : ∀ (g : Fˣ) (t : T₁.carrier), e (g • t) = g • e t)
    (t : T₁.carrier) :
    Function.Injective (localContractionMap D T₁ T₂ e he) := by
  intro p q h
  have hp := localCoord_map D T₁ T₂ e he t p
  have hq := localCoord_map D T₁ T₂ e he t q
  have hcoord : localCoord D T₁ t p = localCoord D T₁ t q := by
    rw [← hp, ← hq, h]
  exact (localCoord_eq_iff D T₁ t p q).mp hcoord

/-- The induced map of an equivariant map of torsors is surjective. -/
theorem localContractionMap_surjective (e : T₁.carrier → T₂.carrier)
    (he : ∀ (g : Fˣ) (t : T₁.carrier), e (g • t) = g • e t)
    (t : T₁.carrier) :
    Function.Surjective (localContractionMap D T₁ T₂ e he) := by
  intro q
  refine ⟨localPoint D T₁ t (localCoord D T₂ (e t) q), ?_⟩
  rw [localContractionMap_localPoint, localPoint_localCoord]

/-- The induced map of an equivariant equivalence of torsors is bijective. -/
theorem localContractionMap_bijective (e : T₁.carrier ≃ T₂.carrier)
    (he : ∀ (g : Fˣ) (t : T₁.carrier), e (g • t) = g • e t)
    (t : T₁.carrier) :
    Function.Bijective (localContractionMap D T₁ T₂ e he) :=
  ⟨localContractionMap_injective D T₁ T₂ e he t,
    localContractionMap_surjective D T₁ T₂ e he t⟩

end ContractionTransport

/-- The inverse of an equivariant equivalence of torsors is itself
equivariant. -/
theorem equivariant_symm {F : Type u} [Field F] {T₁ T₂ : GTorsor Fˣ}
    (e : T₁.carrier ≃ T₂.carrier)
    (he : ∀ (g : Fˣ) (t : T₁.carrier), e (g • t) = g • e t)
    (g : Fˣ) (t : T₂.carrier) :
    e.symm (g • t) = g • e.symm t := by
  apply e.injective
  rw [e.apply_symm_apply, he, e.apply_symm_apply]

/-! ## 2. Isomorphisms of torsor presentations -/

section PresentationIsoSection

variable {F : Type u} [Field F] [NumberField F] {D : GlobalPlaceData F}

/-- An isomorphism of torsor presentations: a genuine equivariant bijection of
the underlying `F^x`-torsors carrying the base point and every local point
(finite and archimedean) to its counterpart.  The local point conditions are
phrased through the induced bijections of the local contractions. -/
structure PresentationIso (P Q : TorsorPresentation D) where
  /-- The underlying bijection of torsors. -/
  torsorEquiv : P.T.carrier ≃ Q.T.carrier
  /-- The bijection is equivariant for the `F^x`-actions. -/
  equivariant : ∀ (g : Fˣ) (t : P.T.carrier), torsorEquiv (g • t) = g • torsorEquiv t
  /-- The base point is carried to the base point. -/
  base_eq : torsorEquiv P.base = Q.base
  /-- The induced map on finite local contractions carries the local points of
  `P` to the local points of `Q`. -/
  finitePoint_eq : ∀ v : HeightOneSpectrum (𝓞 F),
    localContractionMap (D.finiteValue v) P.T Q.T torsorEquiv equivariant
      (P.finitePoint v) = Q.finitePoint v
  /-- The induced map on archimedean local contractions carries the local points
  of `P` to the local points of `Q`. -/
  infinitePoint_eq : ∀ w : NumberField.InfinitePlace F,
    localContractionMap (D.infiniteValue w) P.T Q.T torsorEquiv equivariant
      (P.infinitePoint w) = Q.infinitePoint w

namespace PresentationIso

variable {P Q R : TorsorPresentation D}

/-- The identity isomorphism of a presentation. -/
def refl (P : TorsorPresentation D) : PresentationIso P P where
  torsorEquiv := Equiv.refl P.T.carrier
  equivariant := fun _ _ => rfl
  base_eq := rfl
  finitePoint_eq v := by
    change localContractionMap (D.finiteValue v) P.T P.T id (fun _ _ => rfl)
      (P.finitePoint v) = P.finitePoint v
    rw [localContractionMap_id]
  infinitePoint_eq w := by
    change localContractionMap (D.infiniteValue w) P.T P.T id (fun _ _ => rfl)
      (P.infinitePoint w) = P.infinitePoint w
    rw [localContractionMap_id]

/-- The inverse of a presentation isomorphism. -/
def symm (e : PresentationIso P Q) : PresentationIso Q P where
  torsorEquiv := e.torsorEquiv.symm
  equivariant := equivariant_symm e.torsorEquiv e.equivariant
  base_eq := by
    apply e.torsorEquiv.injective
    rw [e.torsorEquiv.apply_symm_apply, e.base_eq]
  finitePoint_eq v := by
    rw [← e.finitePoint_eq v]
    induction P.finitePoint v using Quotient.inductionOn with
    | h p =>
        rw [localContractionMap_mk, localContractionMap_mk, e.torsorEquiv.symm_apply_apply]
  infinitePoint_eq w := by
    rw [← e.infinitePoint_eq w]
    induction P.infinitePoint w using Quotient.inductionOn with
    | h p =>
        rw [localContractionMap_mk, localContractionMap_mk, e.torsorEquiv.symm_apply_apply]

/-- The composite of two presentation isomorphisms. -/
def trans (e₁ : PresentationIso P Q) (e₂ : PresentationIso Q R) :
    PresentationIso P R where
  torsorEquiv := e₁.torsorEquiv.trans e₂.torsorEquiv
  equivariant g t := by
    change e₂.torsorEquiv (e₁.torsorEquiv (g • t)) =
      g • e₂.torsorEquiv (e₁.torsorEquiv t)
    rw [e₁.equivariant, e₂.equivariant]
  base_eq := by
    change e₂.torsorEquiv (e₁.torsorEquiv P.base) = R.base
    rw [e₁.base_eq, e₂.base_eq]
  finitePoint_eq v := by
    rw [← e₂.finitePoint_eq v, ← e₁.finitePoint_eq v]
    induction P.finitePoint v using Quotient.inductionOn with
    | h p =>
        rw [localContractionMap_mk, localContractionMap_mk, localContractionMap_mk]
        rfl
  infinitePoint_eq w := by
    rw [← e₂.infinitePoint_eq w, ← e₁.infinitePoint_eq w]
    induction P.infinitePoint w using Quotient.inductionOn with
    | h p =>
        rw [localContractionMap_mk, localContractionMap_mk, localContractionMap_mk]
        rfl

/-- A presentation isomorphism preserves the finite coordinates. -/
theorem finiteCoord_eq (e : PresentationIso P Q) (v : HeightOneSpectrum (𝓞 F)) :
    P.finiteCoord v = Q.finiteCoord v := by
  have h := localCoord_map (D.finiteValue v) P.T Q.T e.torsorEquiv e.equivariant
    P.base (P.finitePoint v)
  rw [e.base_eq, e.finitePoint_eq v] at h
  exact h.symm

/-- A presentation isomorphism preserves the archimedean coordinates. -/
theorem infiniteCoord_eq (e : PresentationIso P Q) (w : NumberField.InfinitePlace F) :
    P.infiniteCoord w = Q.infiniteCoord w := by
  have h := localCoord_map (D.infiniteValue w) P.T Q.T e.torsorEquiv e.equivariant
    P.base (P.infinitePoint w)
  rw [e.base_eq, e.infinitePoint_eq w] at h
  exact h.symm

/-- Every presentation isomorphism gives a degree-one, multiplier-one arrow of
the coordinate category (the identity local inclusion conditions). -/
def toArrow (e : PresentationIso P Q) : TorsorArrow P Q where
  degree := 1
  positive_degree := Nat.one_pos
  multiplier := 1
  finite_incl v := by
    rw [← e.finiteCoord_eq v]
    exact (D.finiteValue v).localInclusion_one_one (P.finiteCoord v)
  infinite_incl w := by
    rw [← e.infiniteCoord_eq w]
    exact (D.infiniteValue w).localInclusion_one_one (P.infiniteCoord w)

end PresentationIso

end PresentationIsoSection

/-! ## 3. The functor from global ideal families to torsor presentations -/

/-- The base point `1` of the regular `F^x`-torsor, as an element of its
carrier type.  Bundling it keeps the carrier type explicit in later
applications. -/
def regularTorsorBasePoint (F : Type u) [Field F] : (GTorsor.regular Fˣ).carrier :=
  (1 : Fˣ)

section IdealFamilyToPresentation

variable {F : Type u} [Field F] [NumberField F] (D : GlobalPlaceData F)

/-- The functor `F` of the coordinate equivalence: an ideal family becomes the
torsor presentation with underlying regular `F^x`-torsor, base point `1`, and
local points the contraction points with value coordinates `J.finite v` and
`J.infinite w`. -/
def idealFamilyToPresentation (J : GlobalIdealFamily F) : TorsorPresentation D where
  T := GTorsor.regular Fˣ
  base := regularTorsorBasePoint F
  finitePoint v :=
    localPoint (D.finiteValue v) (GTorsor.regular Fˣ) (regularTorsorBasePoint F) (J.finite v)
  infinitePoint w :=
    localPoint (D.infiniteValue w) (GTorsor.regular Fˣ) (regularTorsorBasePoint F)
      (J.infinite w)
  finite_support := by
    have hset : {v : HeightOneSpectrum (𝓞 F) |
        localCoord (D.finiteValue v) (GTorsor.regular Fˣ) (regularTorsorBasePoint F)
          (localPoint (D.finiteValue v) (GTorsor.regular Fˣ) (regularTorsorBasePoint F)
            (J.finite v)) ≠ 0}
        = {v : HeightOneSpectrum (𝓞 F) | J.finite v ≠ 0} := by
      ext v
      change (localCoord (D.finiteValue v) (GTorsor.regular Fˣ) (regularTorsorBasePoint F)
          (localPoint (D.finiteValue v) (GTorsor.regular Fˣ) (regularTorsorBasePoint F)
            (J.finite v)) ≠ 0) ↔ (J.finite v ≠ 0)
      rw [localCoord_localPoint (D.finiteValue v) (GTorsor.regular Fˣ)
        (regularTorsorBasePoint F) (J.finite v)]
    rw [hset]
    refine Set.Finite.ofFinset J.finite.support ?_
    intro v
    rw [Finsupp.mem_support_iff]
    exact Iff.rfl

/-- The underlying torsor of the presentation of an ideal family is the regular
torsor. -/
@[simp]
theorem idealFamilyToPresentation_T (J : GlobalIdealFamily F) :
    (idealFamilyToPresentation D J).T = GTorsor.regular Fˣ :=
  rfl

/-- The base point of the presentation of an ideal family is `1`. -/
@[simp]
theorem idealFamilyToPresentation_base (J : GlobalIdealFamily F) :
    (idealFamilyToPresentation D J).base = regularTorsorBasePoint F :=
  rfl

/-- The finite local points are the contraction points with value coordinates
the ideal-family exponents. -/
@[simp]
theorem idealFamilyToPresentation_finitePoint (J : GlobalIdealFamily F)
    (v : HeightOneSpectrum (𝓞 F)) :
    (idealFamilyToPresentation D J).finitePoint v =
      localPoint (D.finiteValue v) (GTorsor.regular Fˣ) (regularTorsorBasePoint F)
        (J.finite v) :=
  rfl

/-- The archimedean local points are the contraction points with the
archimedean coordinates. -/
@[simp]
theorem idealFamilyToPresentation_infinitePoint (J : GlobalIdealFamily F)
    (w : NumberField.InfinitePlace F) :
    (idealFamilyToPresentation D J).infinitePoint w =
      localPoint (D.infiniteValue w) (GTorsor.regular Fˣ) (regularTorsorBasePoint F)
        (J.infinite w) :=
  rfl

/-- The finite coordinate of the presentation of an ideal family is the
ideal-family exponent. -/
@[simp]
theorem idealFamilyToPresentation_finiteCoord (J : GlobalIdealFamily F)
    (v : HeightOneSpectrum (𝓞 F)) :
    (idealFamilyToPresentation D J).finiteCoord v = J.finite v := by
  rw [TorsorPresentation.finiteCoord_def, idealFamilyToPresentation_finitePoint]
  exact localCoord_localPoint (D.finiteValue v) (GTorsor.regular Fˣ)
    (regularTorsorBasePoint F) (J.finite v)

/-- The archimedean coordinate of the presentation of an ideal family is the
ideal-family archimedean coordinate. -/
@[simp]
theorem idealFamilyToPresentation_infiniteCoord (J : GlobalIdealFamily F)
    (w : NumberField.InfinitePlace F) :
    (idealFamilyToPresentation D J).infiniteCoord w = J.infinite w := by
  rw [TorsorPresentation.infiniteCoord_def, idealFamilyToPresentation_infinitePoint]
  exact localCoord_localPoint (D.infiniteValue w) (GTorsor.regular Fˣ)
    (regularTorsorBasePoint F) (J.infinite w)

/-- The functor `F` on morphisms: a morphism of global ideal families becomes
the torsor arrow with the same degree and multiplier; the local integrality
conditions are the same conditions read through the coordinates. -/
def idealFamilyHomToTorsorArrow {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom D J₁ J₂) :
    TorsorArrow (idealFamilyToPresentation D J₁) (idealFamilyToPresentation D J₂) where
  degree := h.degree
  positive_degree := h.positive_degree
  multiplier := h.multiplier
  finite_incl v := by
    have hh := h.finite_incl v
    rw [idealFamilyToPresentation_finiteCoord, idealFamilyToPresentation_finiteCoord]
    exact hh
  infinite_incl w := by
    have hh := h.infinite_incl w
    rw [idealFamilyToPresentation_infiniteCoord, idealFamilyToPresentation_infiniteCoord]
    exact hh

/-- The functor `F` preserves the degree of an arrow. -/
@[simp]
theorem idealFamilyHomToTorsorArrow_degree {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom D J₁ J₂) :
    (idealFamilyHomToTorsorArrow D h).degree = h.degree :=
  rfl

/-- The functor `F` preserves the multiplier of an arrow. -/
@[simp]
theorem idealFamilyHomToTorsorArrow_multiplier {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom D J₁ J₂) :
    (idealFamilyHomToTorsorArrow D h).multiplier = h.multiplier :=
  rfl

/-- The functor `F` preserves identities. -/
theorem idealFamilyHomToTorsorArrow_id (J : GlobalIdealFamily F) :
    idealFamilyHomToTorsorArrow D (GlobalIdealFamily.Hom.id (D := D) J) =
      TorsorArrow.id (idealFamilyToPresentation D J) := by
  apply TorsorArrow.ext <;> rfl

/-- The functor `F` preserves composition. -/
theorem idealFamilyHomToTorsorArrow_comp {J₁ J₂ J₃ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom D J₁ J₂) (k : GlobalIdealFamily.Hom D J₂ J₃) :
    idealFamilyHomToTorsorArrow D (GlobalIdealFamily.Hom.comp h k) =
      TorsorArrow.comp (idealFamilyHomToTorsorArrow D h)
        (idealFamilyHomToTorsorArrow D k) := by
  apply TorsorArrow.ext <;> rfl

end IdealFamilyToPresentation

/-! ## 4. The functor from torsor presentations to global ideal families -/

section PresentationToIdealFamily

variable {F : Type u} [Field F] [NumberField F] (D : GlobalPlaceData F)

/-- The functor `G` of the coordinate equivalence: a torsor presentation
becomes the global ideal family whose finite coordinates are the presentation's
finite coordinates, packaged as a finitely supported function by the
presentation's finite-support condition, and whose archimedean coordinates are
the presentation's archimedean coordinates. -/
def presentationToIdealFamily (P : TorsorPresentation D) : GlobalIdealFamily F where
  finite := Finsupp.onFinset P.finite_support.toFinset (fun v => P.finiteCoord v)
    (fun _ hv => P.finite_support.mem_toFinset.mpr hv)
  infinite := fun w => P.infiniteCoord w

/-- Evaluation of the finite coordinates of the ideal family of a presentation. -/
@[simp]
theorem presentationToIdealFamily_finite (P : TorsorPresentation D)
    (v : HeightOneSpectrum (𝓞 F)) :
    (presentationToIdealFamily D P).finite v = P.finiteCoord v :=
  rfl

/-- Evaluation of the archimedean coordinates of the ideal family of a
presentation. -/
@[simp]
theorem presentationToIdealFamily_infinite (P : TorsorPresentation D)
    (w : NumberField.InfinitePlace F) :
    (presentationToIdealFamily D P).infinite w = P.infiniteCoord w :=
  rfl

/-- **Object roundtrip**: applying `G` after `F` returns the original global
ideal family exactly. -/
theorem presentationToIdealFamily_idealFamilyToPresentation (J : GlobalIdealFamily F) :
    presentationToIdealFamily D (idealFamilyToPresentation D J) = J := by
  apply GlobalIdealFamily.ext
  · apply Finsupp.ext
    intro v
    rw [presentationToIdealFamily_finite, idealFamilyToPresentation_finiteCoord]
  · funext w
    rw [presentationToIdealFamily_infinite, idealFamilyToPresentation_infiniteCoord]

/-- The functor `G` on morphisms: a torsor arrow becomes the morphism of
global ideal families with the same degree and multiplier. -/
def presentationArrowToIdealFamilyHom {P₁ P₂ : TorsorPresentation D}
    (ψ : TorsorArrow P₁ P₂) :
    GlobalIdealFamily.Hom D (presentationToIdealFamily D P₁)
      (presentationToIdealFamily D P₂) where
  degree := ψ.degree
  positive_degree := ψ.positive_degree
  multiplier := ψ.multiplier
  finite_incl v := by
    have hh := ψ.finite_incl v
    rw [presentationToIdealFamily_finite, presentationToIdealFamily_finite]
    exact hh
  infinite_incl w := by
    have hh := ψ.infinite_incl w
    rw [presentationToIdealFamily_infinite, presentationToIdealFamily_infinite]
    exact hh

/-- The functor `G` preserves the degree of an arrow. -/
@[simp]
theorem presentationArrowToIdealFamilyHom_degree {P₁ P₂ : TorsorPresentation D}
    (ψ : TorsorArrow P₁ P₂) :
    (presentationArrowToIdealFamilyHom D ψ).degree = ψ.degree :=
  rfl

/-- The functor `G` preserves the multiplier of an arrow. -/
@[simp]
theorem presentationArrowToIdealFamilyHom_multiplier {P₁ P₂ : TorsorPresentation D}
    (ψ : TorsorArrow P₁ P₂) :
    (presentationArrowToIdealFamilyHom D ψ).multiplier = ψ.multiplier :=
  rfl

/-- The functor `G` preserves identities. -/
theorem presentationArrowToIdealFamilyHom_id (P : TorsorPresentation D) :
    presentationArrowToIdealFamilyHom D (TorsorArrow.id P) =
      GlobalIdealFamily.Hom.id (D := D) (presentationToIdealFamily D P) := by
  apply GlobalIdealFamily.Hom.ext <;> rfl

/-- The functor `G` preserves composition. -/
theorem presentationArrowToIdealFamilyHom_comp {P₁ P₂ P₃ : TorsorPresentation D}
    (φ : TorsorArrow P₁ P₂) (ψ : TorsorArrow P₂ P₃) :
    presentationArrowToIdealFamilyHom D (TorsorArrow.comp φ ψ) =
      GlobalIdealFamily.Hom.comp (presentationArrowToIdealFamilyHom D φ)
        (presentationArrowToIdealFamilyHom D ψ) := by
  apply GlobalIdealFamily.Hom.ext <;> rfl

/-- For an arrow between presentations in the image of `F`, the inverse
translation of `G` on morphisms lands back in the original ideal families.
This is the coordinate-level inverse of the Hom-set dictionary. -/
def torsorArrowToIdealFamilyHom (J₁ J₂ : GlobalIdealFamily F)
    (ψ : TorsorArrow (idealFamilyToPresentation D J₁) (idealFamilyToPresentation D J₂)) :
    GlobalIdealFamily.Hom D J₁ J₂ where
  degree := ψ.degree
  positive_degree := ψ.positive_degree
  multiplier := ψ.multiplier
  finite_incl v := by
    have hh := ψ.finite_incl v
    rw [idealFamilyToPresentation_finiteCoord, idealFamilyToPresentation_finiteCoord] at hh
    exact hh
  infinite_incl w := by
    have hh := ψ.infinite_incl w
    rw [idealFamilyToPresentation_infiniteCoord,
      idealFamilyToPresentation_infiniteCoord] at hh
    exact hh

/-- **The Hom-set dictionary**: morphisms `J₁ → J₂` of global ideal families
are in bijection with torsor arrows between their presentations. -/
def idealFamilyHomEquivTorsorArrow (J₁ J₂ : GlobalIdealFamily F) :
    GlobalIdealFamily.Hom D J₁ J₂ ≃
      TorsorArrow (idealFamilyToPresentation D J₁) (idealFamilyToPresentation D J₂) where
  toFun := idealFamilyHomToTorsorArrow D
  invFun := torsorArrowToIdealFamilyHom D J₁ J₂
  left_inv _ := GlobalIdealFamily.Hom.ext rfl rfl
  right_inv _ := TorsorArrow.ext rfl rfl

/-- The Hom-set dictionary sends a morphism to the torsor arrow with the same
degree and multiplier. -/
@[simp]
theorem idealFamilyHomEquivTorsorArrow_apply {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom D J₁ J₂) :
    idealFamilyHomEquivTorsorArrow D J₁ J₂ h = idealFamilyHomToTorsorArrow D h :=
  rfl

/-- **Fullness**: every torsor arrow between the presentations of two ideal
families is the image of a morphism of ideal families. -/
theorem idealFamilyHomToTorsorArrow_surjective (J₁ J₂ : GlobalIdealFamily F) :
    Function.Surjective
      (idealFamilyHomToTorsorArrow (D := D) (J₁ := J₁) (J₂ := J₂)) :=
  (idealFamilyHomEquivTorsorArrow D J₁ J₂).surjective

/-- **Faithfulness**: the functor `F` is injective on morphisms. -/
theorem idealFamilyHomToTorsorArrow_injective (J₁ J₂ : GlobalIdealFamily F) :
    Function.Injective
      (idealFamilyHomToTorsorArrow (D := D) (J₁ := J₁) (J₂ := J₂)) :=
  (idealFamilyHomEquivTorsorArrow D J₁ J₂).injective

end PresentationToIdealFamily

/-! ## 5. The natural isomorphism `F (G P) ≅ P`, fullness, faithfulness and
essential surjectivity -/

section Counit

variable {F : Type u} [Field F] [NumberField F] {D : GlobalPlaceData F}

/-- The equivariant bijection from the regular torsor to `P.T` carrying the
base point `1` to the base point `P.base`: the map `x ↦ x • P.base`. -/
def regularToTorsorEquiv (P : TorsorPresentation D) :
    (GTorsor.regular Fˣ).carrier ≃ P.T.carrier :=
  Equiv.ofBijective
    (GTorsor.equivariantMapOfPoint (GTorsor.regular Fˣ) P.T
      (regularTorsorBasePoint F) P.base)
    (GTorsor.equivariantMapOfPoint_bijective (GTorsor.regular Fˣ) P.T
      (regularTorsorBasePoint F) P.base)

/-- The underlying map of the torsor equivalence from the regular torsor. -/
@[simp]
theorem regularToTorsorEquiv_apply (P : TorsorPresentation D)
    (x : (GTorsor.regular Fˣ).carrier) :
    regularToTorsorEquiv P x =
      GTorsor.equivariantMapOfPoint (GTorsor.regular Fˣ) P.T
        (regularTorsorBasePoint F) P.base x :=
  rfl

/-- The torsor equivalence from the regular torsor is equivariant. -/
theorem regularToTorsorEquiv_equivariant (P : TorsorPresentation D) (g : Fˣ)
    (x : (GTorsor.regular Fˣ).carrier) :
    regularToTorsorEquiv P (g • x) = g • regularToTorsorEquiv P x :=
  GTorsor.equivariantMapOfPoint_smul (GTorsor.regular Fˣ) P.T
    (regularTorsorBasePoint F) P.base g x

/-- The torsor equivalence from the regular torsor sends the base point `1` to
`P.base`. -/
theorem regularToTorsorEquiv_base (P : TorsorPresentation D) :
    regularToTorsorEquiv P (regularTorsorBasePoint F) = P.base :=
  GTorsor.equivariantMapOfPoint_base (GTorsor.regular Fˣ) P.T
    (regularTorsorBasePoint F) P.base

/-- **The natural isomorphism `F (G P) ≅ P`**: transport along the torsor
equivalence from the regular torsor to `P.T`, together with the induced maps on
the local contractions.  The base point and all local points match. -/
def counitIso (P : TorsorPresentation D) :
    PresentationIso (idealFamilyToPresentation D (presentationToIdealFamily D P)) P where
  torsorEquiv := regularToTorsorEquiv P
  equivariant := regularToTorsorEquiv_equivariant P
  base_eq := regularToTorsorEquiv_base P
  finitePoint_eq v := by
    change localContractionMap (D.finiteValue v) (GTorsor.regular Fˣ) P.T
        ⇑(regularToTorsorEquiv P) (regularToTorsorEquiv_equivariant P)
        ((idealFamilyToPresentation D (presentationToIdealFamily D P)).finitePoint v) =
      P.finitePoint v
    rw [idealFamilyToPresentation_finitePoint, localContractionMap_localPoint,
      regularToTorsorEquiv_base, presentationToIdealFamily_finite]
    exact localPoint_localCoord (D.finiteValue v) P.T P.base (P.finitePoint v)
  infinitePoint_eq w := by
    change localContractionMap (D.infiniteValue w) (GTorsor.regular Fˣ) P.T
        ⇑(regularToTorsorEquiv P) (regularToTorsorEquiv_equivariant P)
        ((idealFamilyToPresentation D (presentationToIdealFamily D P)).infinitePoint w) =
      P.infinitePoint w
    rw [idealFamilyToPresentation_infinitePoint, localContractionMap_localPoint,
      regularToTorsorEquiv_base, presentationToIdealFamily_infinite]
    exact localPoint_localCoord (D.infiniteValue w) P.T P.base (P.infinitePoint w)

/-- The base point matches under the counit isomorphism. -/
@[simp]
theorem counitIso_base (P : TorsorPresentation D) :
    (counitIso P).torsorEquiv
      (idealFamilyToPresentation D (presentationToIdealFamily D P)).base = P.base :=
  (counitIso P).base_eq

/-- The finite local points match under the counit isomorphism. -/
@[simp]
theorem counitIso_finitePoint (P : TorsorPresentation D)
    (v : HeightOneSpectrum (𝓞 F)) :
    localContractionMap (D.finiteValue v)
      (idealFamilyToPresentation D (presentationToIdealFamily D P)).T P.T
      (counitIso P).torsorEquiv (counitIso P).equivariant
      ((idealFamilyToPresentation D (presentationToIdealFamily D P)).finitePoint v) =
      P.finitePoint v :=
  (counitIso P).finitePoint_eq v

/-- The archimedean local points match under the counit isomorphism. -/
@[simp]
theorem counitIso_infinitePoint (P : TorsorPresentation D)
    (w : NumberField.InfinitePlace F) :
    localContractionMap (D.infiniteValue w)
      (idealFamilyToPresentation D (presentationToIdealFamily D P)).T P.T
      (counitIso P).torsorEquiv (counitIso P).equivariant
      ((idealFamilyToPresentation D (presentationToIdealFamily D P)).infinitePoint w) =
      P.infinitePoint w :=
  (counitIso P).infinitePoint_eq w

/-- **Naturality of the counit**: for every torsor arrow `ψ`, the square with
the functor images commutes at the coordinate level. -/
theorem counit_naturality {P₁ P₂ : TorsorPresentation D} (ψ : TorsorArrow P₁ P₂) :
    TorsorArrow.comp
        (idealFamilyHomToTorsorArrow D (presentationArrowToIdealFamilyHom D ψ))
        (PresentationIso.toArrow (counitIso P₂)) =
      TorsorArrow.comp (PresentationIso.toArrow (counitIso P₁)) ψ := by
  apply TorsorArrow.ext <;> simp [TorsorArrow.comp, PresentationIso.toArrow]

/-- **Essential surjectivity**: every torsor presentation is isomorphic, via the
counit isomorphism, to a presentation in the image of the object functor `F`. -/
theorem essentially_surjective (P : TorsorPresentation D) :
    ∃ J : GlobalIdealFamily F,
      Nonempty (PresentationIso (idealFamilyToPresentation D J) P) :=
  ⟨presentationToIdealFamily D P, ⟨counitIso P⟩⟩

end Counit

/-! ## 6. The packaged coordinate equivalence -/

section CoordinateEquivalenceSection

variable {F : Type u} [Field F] [NumberField F] (D : GlobalPlaceData F)

/-- The bundled coordinate equivalence between the global ideal-family category
and the torsor-presentation category of Example 3.6: object functors, arrow
functors, functor laws, the exact object roundtrip `G (F J) = J`, the Hom-set
bijection, the counit natural isomorphism, and essential surjectivity. -/
structure CoordinateEquivalence where
  /-- The object functor from ideal families to presentations. -/
  toPresentation : GlobalIdealFamily F → TorsorPresentation D
  /-- The object functor from presentations to ideal families. -/
  toFamily : TorsorPresentation D → GlobalIdealFamily F
  /-- The arrow functor from ideal families to presentations. -/
  mapHom : ∀ {J₁ J₂ : GlobalIdealFamily F},
    GlobalIdealFamily.Hom D J₁ J₂ → TorsorArrow (toPresentation J₁) (toPresentation J₂)
  /-- The arrow functor from presentations to ideal families. -/
  mapArrow : ∀ {P₁ P₂ : TorsorPresentation D},
    TorsorArrow P₁ P₂ → GlobalIdealFamily.Hom D (toFamily P₁) (toFamily P₂)
  /-- The arrow functor from ideal families preserves identities. -/
  mapHom_id : ∀ J : GlobalIdealFamily F,
    mapHom (GlobalIdealFamily.Hom.id (D := D) J) = TorsorArrow.id (toPresentation J)
  /-- The arrow functor from ideal families preserves composition. -/
  mapHom_comp : ∀ {J₁ J₂ J₃ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom D J₁ J₂) (k : GlobalIdealFamily.Hom D J₂ J₃),
    mapHom (GlobalIdealFamily.Hom.comp h k) =
      TorsorArrow.comp (mapHom h) (mapHom k)
  /-- The arrow functor from presentations preserves identities. -/
  mapArrow_id : ∀ P : TorsorPresentation D,
    mapArrow (TorsorArrow.id P) = GlobalIdealFamily.Hom.id (D := D) (toFamily P)
  /-- The arrow functor from presentations preserves composition. -/
  mapArrow_comp : ∀ {P₁ P₂ P₃ : TorsorPresentation D}
    (φ : TorsorArrow P₁ P₂) (ψ : TorsorArrow P₂ P₃),
    mapArrow (TorsorArrow.comp φ ψ) =
      GlobalIdealFamily.Hom.comp (mapArrow φ) (mapArrow ψ)
  /-- The object roundtrip is exact. -/
  roundtrip : ∀ J : GlobalIdealFamily F, toFamily (toPresentation J) = J
  /-- The Hom-set bijection. -/
  homEquiv : ∀ J₁ J₂ : GlobalIdealFamily F,
    GlobalIdealFamily.Hom D J₁ J₂ ≃ TorsorArrow (toPresentation J₁) (toPresentation J₂)
  /-- The Hom-set bijection agrees with the arrow functor. -/
  homEquiv_apply : ∀ (J₁ J₂ : GlobalIdealFamily F) (h : GlobalIdealFamily.Hom D J₁ J₂),
    homEquiv J₁ J₂ h = mapHom h
  /-- The counit natural isomorphism `F (G P) ≅ P`. -/
  counit : ∀ P : TorsorPresentation D, PresentationIso (toPresentation (toFamily P)) P
  /-- Naturality of the counit with respect to torsor arrows. -/
  counit_natural : ∀ {P₁ P₂ : TorsorPresentation D} (ψ : TorsorArrow P₁ P₂),
    TorsorArrow.comp (mapHom (mapArrow ψ)) (PresentationIso.toArrow (counit P₂)) =
      TorsorArrow.comp (PresentationIso.toArrow (counit P₁)) ψ

/-- The coordinate equivalence of Example 3.6, constructed from the functors
`F` and `G` and the lemmas proved above. -/
def torsorIdealFamilyEquivalence : CoordinateEquivalence D where
  toPresentation := idealFamilyToPresentation D
  toFamily := presentationToIdealFamily D
  mapHom := idealFamilyHomToTorsorArrow D
  mapArrow := presentationArrowToIdealFamilyHom D
  mapHom_id := idealFamilyHomToTorsorArrow_id D
  mapHom_comp := fun h k => idealFamilyHomToTorsorArrow_comp D h k
  mapArrow_id := presentationArrowToIdealFamilyHom_id D
  mapArrow_comp := fun φ ψ => presentationArrowToIdealFamilyHom_comp D φ ψ
  roundtrip := presentationToIdealFamily_idealFamilyToPresentation D
  homEquiv := idealFamilyHomEquivTorsorArrow D
  homEquiv_apply := fun _ _ _ => rfl
  counit := fun P => counitIso P
  counit_natural := fun ψ => counit_naturality ψ

/-- **The explicit Full + Faithful + EssentiallySurjective statement** for the
torsor-presentation functor: the object roundtrip is exact, the functor is
bijective on Hom-sets, and every presentation is isomorphic to one in the image
of the object functor. -/
theorem coordinateEquivalence_statements :
    (∀ J : GlobalIdealFamily F,
        presentationToIdealFamily D (idealFamilyToPresentation D J) = J) ∧
      (∀ J₁ J₂ : GlobalIdealFamily F,
        Function.Bijective
          (idealFamilyHomToTorsorArrow (D := D) (J₁ := J₁) (J₂ := J₂))) ∧
      (∀ P : TorsorPresentation D, ∃ J : GlobalIdealFamily F,
        Nonempty (PresentationIso (idealFamilyToPresentation D J) P)) := by
  refine ⟨presentationToIdealFamily_idealFamilyToPresentation D, ?_, ?_⟩
  · intro J₁ J₂
    exact ⟨idealFamilyHomToTorsorArrow_injective D J₁ J₂,
      idealFamilyHomToTorsorArrow_surjective D J₁ J₂⟩
  · intro P
    exact essentially_surjective P

end CoordinateEquivalenceSection

/-! ## 7. The actual number-field place data -/

section NumberFieldInstantiation

variable {F : Type u} [Field F] [NumberField F]

/-- The coordinate equivalence at the actual number-field place data
`numberFieldGlobalPlaceData` of Layer 2. -/
def numberFieldTorsorIdealFamilyEquivalence :
    CoordinateEquivalence (numberFieldGlobalPlaceData (F := F)) :=
  torsorIdealFamilyEquivalence _

/-- The object roundtrip at the actual number-field place data. -/
theorem numberFieldObjectRoundtrip (J : GlobalIdealFamily F) :
    presentationToIdealFamily (numberFieldGlobalPlaceData (F := F))
      (idealFamilyToPresentation (numberFieldGlobalPlaceData (F := F)) J) = J :=
  presentationToIdealFamily_idealFamilyToPresentation _ J

end NumberFieldInstantiation

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
