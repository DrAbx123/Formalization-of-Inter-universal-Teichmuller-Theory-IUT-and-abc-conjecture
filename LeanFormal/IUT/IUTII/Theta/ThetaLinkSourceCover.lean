/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceTemperedCoveringCategory
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Equivalence

/-!
# A source-cover model of the product comparison in IUT I, Example 3.2(v)

IUT I, Example 3.2(v), works with the following data.

* `D_v = B^temp(X_v)^0` is the category of *connected* tempered coverings of
  the curve `X_v`, and `D_v^⊢ = B(K_v)^0` is the full subcategory of coverings
  whose base field is the base field `K_v` of `X_v`.
* For an object `Yddot_v` of `D_v` whose base field is `K_v`, one considers
  the slice category `(D_v)_{Yddot_v}` and its full subcategory `D_v^Θ`
  determined by the products `Yddot_v × A` with `A ∈ Ob(D_v^⊢)`.
* Forming the product with `Yddot_v` gives a natural equivalence of categories
  `D_v^⊢ ~→ D_v^Θ`, written `A ↦ A_Θ := Yddot_v × A`.

This file formalizes the *generic categorical skeleton* of that construction on
top of the literal geometric covering category
`SourceSemiGraphOfAnabelioids.CovObject` and its tempered full subcategory
`TemperedCover`.  It deliberately does **not** identify any of its inputs with
the actual objects `X_v`, `Yddot_v`, `B(K_v)^0`, or with the paper's `D_v`.

## Modelling decisions and boundaries

* `TemperedCover` is the literal full subcategory of tempered objects of the
  covering category.  It is **not** called `D_v` here: temperedness is a
  componentwise condition, so `TemperedCover` may contain disconnected covers,
  and it also contains covers with no geometric point at all (on which
  temperedness holds vacuously; see the last section).  The paper's `D_v`
  consists of connected objects, so we introduce the full subcategory
  `ConnectedTemperedCover` as the candidate source model of `D_v`.  We do not
  assert that it is the paper's `D_v`.
* The base field `B(K_v)^0` is not represented by an object of the existing
  API.  Instead, `BaseFieldCoverModel` is an *explicit structure parameter*
  consisting of a predicate on connected tempered covers, a distinguished
  base object, and a proof that the base object satisfies the predicate.  It
  contains no `Card`-valued or otherwise empty placeholder field.  The paper's
  assertion that the base field of `Yddot_v` is `K_v` is represented only by
  the explicit isomorphism `BaseFieldProductIdentification.baseProductIso`,
  which records the formal consequence `Yddot_v × B(K_v)^0 ≅ Yddot_v` in the
  slice over `Yddot_v`.  No claim is made that this isomorphism comes from a
  real curve or a real base field.
* Connected tempered covers do **not** have all binary products: the product
  of two connected covers is in general disconnected, and no `HasBinaryProducts`
  instance for `TemperedCover` or `ConnectedTemperedCover` exists (and such an
  instance would be mathematically wrong).  Accordingly, the products
  `Yddot_v × A` are supplied by an explicit product-cone structure
  `ThetaProductData`, with a first projection to `Yddot_v`, a second
  projection to `A`, and the full universal property.  This is the honest
  formal counterpart of "the product in `D_v` of `Yddot_v` with `A`".
* Fullness of `A ↦ Yddot_v × A` is *not* formal from the product universal
  property alone.  It uses the base-field condition: a morphism
  `Yddot_v × A ⟶ Yddot_v × B` over `Yddot_v` must be constant along the
  `Yddot_v`-direction.  This condition is isolated as the explicit proposition
  `SliceFactorization`, which is a hypothesis of the fullness and equivalence
  theorems, not an axiom and not a proved fact about a real curve.
* Faithfulness uses that the second projection `Yddot_v × A ⟶ A` is an
  epimorphism, recorded as the explicit field `ThetaProductData.snd_epi`.
  This models surjectivity of the projection on geometric points; it is not
  derived here from the source geometry.
* `D_v^Θ` is modelled by the essential image `ThetaCoverSubcategory` of the
  product functor, i.e. by the full subcategory of slice objects isomorphic to
  some `Yddot_v × A`.  This is the categorical reading of "the full
  subcategory determined by the products".

The equivalence proved below is therefore a conditional categorical theorem
about a supplied source-cover model.  It does not construct `Yddot_v`, does not
construct `B(K_v)^0`, and does not identify the real tempered covering category
of `X_v` with these data.
-/

namespace Iut

universe u

namespace SourceSemiGraphOfAnabelioids

namespace CovObject

namespace ThetaLinkSourceCover

open CategoryTheory

variable (diagram : Iut.SourceSemiGraphOfAnabelioids.{u})

/-! ## The connected tempered full subcategory -/

/-- The property of a tempered cover that it is geometrically connected, in
the intrinsic sense of `AssociatedQuotient.IsGeometricallyConnected` (existence
of a geometric point from which every geometric point is reachable). -/
abbrev connectedTemperedObjectProperty
    (diagram : Iut.SourceSemiGraphOfAnabelioids.{u}) (root : diagram.base.Vertex) :
    ObjectProperty (TemperedCover diagram root) :=
  fun object => AssociatedQuotient.IsGeometricallyConnected object.obj

/-- The full subcategory of `TemperedCover` consisting of geometrically
connected tempered covers.  This is the candidate source model of the paper's
`D_v = B^temp(X_v)^0`; no identification with the paper's category is
asserted. -/
abbrev ConnectedTemperedCover
    (diagram : Iut.SourceSemiGraphOfAnabelioids.{u}) (root : diagram.base.Vertex) :=
  (connectedTemperedObjectProperty diagram root).FullSubcategory

/-- The inclusion of connected tempered covers into all tempered covers. -/
abbrev connectedTemperedInclusion
    (diagram : Iut.SourceSemiGraphOfAnabelioids.{u}) (root : diagram.base.Vertex) :
    ConnectedTemperedCover diagram root ⥤ TemperedCover diagram root :=
  (connectedTemperedObjectProperty diagram root).ι

/-- The underlying countable covering of a connected tempered cover. -/
abbrev connectedTemperedUnderlying
    (diagram : Iut.SourceSemiGraphOfAnabelioids.{u}) (root : diagram.base.Vertex) :
    ConnectedTemperedCover diagram root ⥤ diagram.CovObject :=
  connectedTemperedInclusion diagram root ⋙ temperedCovInclusion diagram root

/-- Every connected tempered cover is tempered. -/
theorem connectedTemperedCover_isTempered
    (diagram : Iut.SourceSemiGraphOfAnabelioids.{u}) (root : diagram.base.Vertex)
    (object : ConnectedTemperedCover diagram root) :
    IsTempered diagram root object.obj.obj :=
  object.obj.property

/-- Every connected tempered cover is geometrically connected. -/
theorem connectedTemperedCover_isGeometricallyConnected
    (diagram : Iut.SourceSemiGraphOfAnabelioids.{u}) (root : diagram.base.Vertex)
    (object : ConnectedTemperedCover diagram root) :
    AssociatedQuotient.IsGeometricallyConnected object.obj.obj :=
  object.property

/-- A connected tempered cover has at least one geometric point.  This is the
precise sense in which `ConnectedTemperedCover` excludes the empty/pointless
tempered covers discussed at the end of the file. -/
theorem connectedTemperedCover_geometricPoint_nonempty
    (diagram : Iut.SourceSemiGraphOfAnabelioids.{u}) (root : diagram.base.Vertex)
    (object : ConnectedTemperedCover diagram root) :
    Nonempty (AssociatedQuotient.GeometricPoint object.obj.obj) := by
  obtain ⟨basePoint, _⟩ := object.property
  exact ⟨basePoint⟩

/-! ## An explicit model of the base-field full subcategory -/

/-- An explicit model of the base-field full subcategory `D_v^⊢ = B(K_v)^0`.

The existing API has no object representing the base field `K_v`, so the base
field is encoded by an explicit predicate `IsBaseFieldCover` on connected
tempered covers together with a distinguished base object and a proof that it
satisfies the predicate.  This is a structure parameter of the construction,
not a claim that such a predicate has been derived from a real curve.  In
particular, no `Card`-valued placeholder or empty promise field is used. -/
structure BaseFieldCoverModel
    (diagram : Iut.SourceSemiGraphOfAnabelioids.{u}) (root : diagram.base.Vertex) where
  /-- The predicate modelling "the base field of the cover is `K_v`". -/
  IsBaseFieldCover : ConnectedTemperedCover diagram root → Prop
  /-- The chosen model of the base object of `B(K_v)^0`. -/
  baseObject : ConnectedTemperedCover diagram root
  /-- The distinguished base object lies in the base-field full subcategory. -/
  baseObject_mem : IsBaseFieldCover baseObject

/-- The full subcategory of connected tempered covers whose base field is
`K_v`, modelled by the predicate of a `BaseFieldCoverModel`.  This is the
candidate source model of `D_v^⊢ = B(K_v)^0`. -/
abbrev BaseCover {diagram : Iut.SourceSemiGraphOfAnabelioids.{u}}
    {root : diagram.base.Vertex} (model : BaseFieldCoverModel diagram root) :=
  ObjectProperty.FullSubcategory model.IsBaseFieldCover

/-- The distinguished base object as an object of `BaseCover`. -/
def baseCoverObject {diagram : Iut.SourceSemiGraphOfAnabelioids.{u}}
    {root : diagram.base.Vertex} (model : BaseFieldCoverModel diagram root) :
    BaseCover model :=
  ⟨model.baseObject, model.baseObject_mem⟩

/-- The inclusion `D_v^⊢ → D_v`, modelled at the level of connected tempered
covers. -/
abbrev baseCoverInclusion {diagram : Iut.SourceSemiGraphOfAnabelioids.{u}}
    {root : diagram.base.Vertex} (model : BaseFieldCoverModel diagram root) :
    BaseCover model ⥤ ConnectedTemperedCover diagram root :=
  ObjectProperty.ι model.IsBaseFieldCover

/-- Base-field covers are connected tempered covers, hence tempered. -/
theorem baseCover_isTempered {diagram : Iut.SourceSemiGraphOfAnabelioids.{u}}
    {root : diagram.base.Vertex} (model : BaseFieldCoverModel diagram root)
    (object : BaseCover model) :
    IsTempered diagram root object.obj.obj.obj :=
  object.obj.obj.property

/-- Base-field covers are connected. -/
theorem baseCover_isGeometricallyConnected
    {diagram : Iut.SourceSemiGraphOfAnabelioids.{u}}
    {root : diagram.base.Vertex} (model : BaseFieldCoverModel diagram root)
    (object : BaseCover model) :
    AssociatedQuotient.IsGeometricallyConnected object.obj.obj.obj :=
  object.obj.property

/-! ## The slice category over `Yddot_v` -/

/-- The slice category `(D_v)_{Yddot_v}` of connected tempered covers over a
fixed connected tempered cover `Yddot`.  This is Mathlib's `Over` category. -/
abbrev YddotSlice (diagram : Iut.SourceSemiGraphOfAnabelioids.{u})
    (root : diagram.base.Vertex) (Yddot : ConnectedTemperedCover diagram root) :=
  Over Yddot

/-! ## Product cones `Yddot_v × A` and the product functor -/

/-- The product cones `A ↦ Yddot_v × A` for `A` in the base-field full
subcategory.

`product A` is the product object, `fst A` and `snd A` are its two
projections, `lift` is the pairing, `lift_fst`/`lift_snd` are the computation
rules, and `lift_unique` is the uniqueness part of the universal property.
`snd_epi` records that the second projection is an epimorphism, which is the
formal counterpart of surjectivity on geometric points.

The structure is indexed only by the chosen base-field model: connected
tempered covers do not have all binary products, so the products used in
Example 3.2(v) are supplied explicitly rather than obtained from a global
product instance. -/
structure ThetaProductData
    (diagram : Iut.SourceSemiGraphOfAnabelioids.{u}) (root : diagram.base.Vertex)
    (Yddot : ConnectedTemperedCover diagram root)
    (model : BaseFieldCoverModel diagram root) where
  /-- The product object `Yddot_v × A`. -/
  product : BaseCover model → ConnectedTemperedCover diagram root
  /-- The first projection `Yddot_v × A ⟶ Yddot_v`. -/
  fst : ∀ A : BaseCover model, product A ⟶ Yddot
  /-- The second projection `Yddot_v × A ⟶ A`. -/
  snd : ∀ A : BaseCover model, product A ⟶ A.obj
  /-- The pairing map into the product. -/
  lift : ∀ {A : BaseCover model} {X : ConnectedTemperedCover diagram root},
    (X ⟶ Yddot) → (X ⟶ A.obj) → (X ⟶ product A)
  /-- The pairing map is compatible with the first projection. -/
  lift_fst : ∀ {A : BaseCover model} {X : ConnectedTemperedCover diagram root}
    (f : X ⟶ Yddot) (g : X ⟶ A.obj),
    lift (A := A) (X := X) f g ≫ fst A = f
  /-- The pairing map is compatible with the second projection. -/
  lift_snd : ∀ {A : BaseCover model} {X : ConnectedTemperedCover diagram root}
    (f : X ⟶ Yddot) (g : X ⟶ A.obj),
    lift (A := A) (X := X) f g ≫ snd A = g
  /-- Uniqueness in the universal property of the product. -/
  lift_unique : ∀ {A : BaseCover model} {X : ConnectedTemperedCover diagram root}
    (f : X ⟶ Yddot) (g : X ⟶ A.obj) (h : X ⟶ product A),
    h ≫ fst A = f → h ≫ snd A = g → h = lift (A := A) (X := X) f g
  /-- The second projection is an epimorphism. -/
  snd_epi : ∀ A : BaseCover model, Epi (snd A)

namespace ThetaProductData

variable {diagram : Iut.SourceSemiGraphOfAnabelioids.{u}}
variable {root : diagram.base.Vertex}
variable {Yddot : ConnectedTemperedCover diagram root}
variable {model : BaseFieldCoverModel diagram root}

/-- The functorial action of `A ↦ Yddot_v × A` on a morphism `f : A ⟶ B`,
obtained by pairing the first projection with `snd A ≫ f`. -/
def productMap (data : ThetaProductData diagram root Yddot model)
    {A B : BaseCover model} (f : A ⟶ B) : data.product A ⟶ data.product B :=
  data.lift (data.fst A) (data.snd A ≫ f.hom)

/-- The functorial action is compatible with the first projection. -/
theorem productMap_fst (data : ThetaProductData diagram root Yddot model)
    {A B : BaseCover model} (f : A ⟶ B) :
    data.productMap f ≫ data.fst B = data.fst A :=
  data.lift_fst (data.fst A) (data.snd A ≫ f.hom)

/-- The functorial action is compatible with the second projection. -/
theorem productMap_snd (data : ThetaProductData diagram root Yddot model)
    {A B : BaseCover model} (f : A ⟶ B) :
    data.productMap f ≫ data.snd B = data.snd A ≫ f.hom :=
  data.lift_snd (data.fst A) (data.snd A ≫ f.hom)

/-- The functorial action sends identities to identities. -/
theorem productMap_id (data : ThetaProductData diagram root Yddot model)
    (A : BaseCover model) :
    data.productMap (𝟙 A) = 𝟙 (data.product A) := by
  have h : data.productMap (𝟙 A) =
      data.lift (data.fst A) (data.snd A) := by
    simp [productMap]
  rw [h]
  exact (data.lift_unique (data.fst A) (data.snd A) (𝟙 (data.product A))
    (by simp) (by simp)).symm

/-- The functorial action preserves composition. -/
theorem productMap_comp (data : ThetaProductData diagram root Yddot model)
    {A B C : BaseCover model} (f : A ⟶ B) (g : B ⟶ C) :
    data.productMap (f ≫ g) = data.productMap f ≫ data.productMap g := by
  refine (data.lift_unique (data.fst A) (data.snd A ≫ (f ≫ g).hom)
    (data.productMap f ≫ data.productMap g) ?_ ?_).symm
  · simp only [Category.assoc, productMap_fst]
  · rw [Category.assoc, productMap_snd, ← Category.assoc, productMap_snd]
    rfl

end ThetaProductData

/-- The product functor `A ↦ Yddot_v × A`, regarded as a functor from the
base-field full subcategory to the slice category over `Yddot_v`. -/
def productFunctor {diagram : Iut.SourceSemiGraphOfAnabelioids.{u}}
    {root : diagram.base.Vertex} {Yddot : ConnectedTemperedCover diagram root}
    {model : BaseFieldCoverModel diagram root}
    (data : ThetaProductData diagram root Yddot model) :
    BaseCover model ⥤ YddotSlice diagram root Yddot where
  obj A := Over.mk (data.fst A)
  map f := Over.homMk (data.productMap f) (data.productMap_fst f)
  map_id A := by
    apply Over.OverMorphism.ext
    exact data.productMap_id A
  map_comp f g := by
    apply Over.OverMorphism.ext
    exact data.productMap_comp f g

/-- The product functor is faithful, assuming that the second projection
`Yddot_v × A ⟶ A` is an epimorphism. -/
instance productFunctorFaithful {diagram : Iut.SourceSemiGraphOfAnabelioids.{u}}
    {root : diagram.base.Vertex} {Yddot : ConnectedTemperedCover diagram root}
    {model : BaseFieldCoverModel diagram root}
    (data : ThetaProductData diagram root Yddot model) :
    (productFunctor data).Faithful where
  map_injective {A B} f g hfg := by
    have hleft : data.productMap f = data.productMap g :=
      congrArg Over.Hom.left hfg
    have hsnd : data.snd A ≫ f.hom = data.snd A ≫ g.hom := by
      rw [← data.productMap_snd f, ← data.productMap_snd g, hleft]
    letI := data.snd_epi A
    exact ObjectProperty.hom_ext model.IsBaseFieldCover
      ((cancel_epi (data.snd A)).mp hsnd)

/-- The base-field condition needed for fullness of `A ↦ Yddot_v × A`: every
slice morphism between two products `Yddot_v × A` and `Yddot_v × B` over
`Yddot_v` is induced by a morphism `A ⟶ B` of base-field covers.

This is the formal counterpart of the paper's use of
`base field of Yddot_v = K_v`: morphisms over `Yddot_v` cannot vary in the
`Yddot_v`-direction.  It is an explicit hypothesis, not a consequence of the
product universal property alone and not an axiom. -/
def SliceFactorization {diagram : Iut.SourceSemiGraphOfAnabelioids.{u}}
    {root : diagram.base.Vertex} {Yddot : ConnectedTemperedCover diagram root}
    {model : BaseFieldCoverModel diagram root}
    (data : ThetaProductData diagram root Yddot model) : Prop :=
  ∀ ⦃A B : BaseCover model⦄
    (h : Over.mk (data.fst A) ⟶ Over.mk (data.fst B)),
    ∃ f : A ⟶ B, h = Over.homMk (data.productMap f) (data.productMap_fst f)

/-- If every slice morphism between products factors through a base-field
morphism, then the product functor is full. -/
theorem productFunctor_full {diagram : Iut.SourceSemiGraphOfAnabelioids.{u}}
    {root : diagram.base.Vertex} {Yddot : ConnectedTemperedCover diagram root}
    {model : BaseFieldCoverModel diagram root}
    (data : ThetaProductData diagram root Yddot model)
    (factorization : SliceFactorization data) :
    (productFunctor data).Full where
  map_surjective h := by
    obtain ⟨f, hf⟩ := factorization h
    exact ⟨f, hf.symm⟩

/-- The full subcategory `D_v^Θ` of the slice `(D_v)_{Yddot_v}` determined by
the products `Yddot_v × A`, modelled as the essential image of the product
functor.  Equivalently, it is the full subcategory of slice objects isomorphic
to some `Yddot_v × A` with `A` in the base-field full subcategory. -/
abbrev ThetaCoverSubcategory {diagram : Iut.SourceSemiGraphOfAnabelioids.{u}}
    {root : diagram.base.Vertex} {Yddot : ConnectedTemperedCover diagram root}
    {model : BaseFieldCoverModel diagram root}
    (data : ThetaProductData diagram root Yddot model) :=
  (productFunctor data).EssImageSubcategory

/-- The natural equivalence `D_v^⊢ ~→ D_v^Θ` of IUT I, Example 3.2(v),
conditional on the base-field slice factorization.

The functor is `A ↦ Yddot_v × A`; its target is the essential image
`ThetaCoverSubcategory`.  The proof uses fullness (from `SliceFactorization`)
and faithfulness (from epimorphicity of the second projection), together with
the general equivalence between a fully faithful functor and its essential
image. -/
noncomputable def thetaEquivalence
    {diagram : Iut.SourceSemiGraphOfAnabelioids.{u}}
    {root : diagram.base.Vertex} {Yddot : ConnectedTemperedCover diagram root}
    {model : BaseFieldCoverModel diagram root}
    (data : ThetaProductData diagram root Yddot model)
    (factorization : SliceFactorization data) :
    BaseCover model ≌ ThetaCoverSubcategory data := by
  letI := productFunctor_full data factorization
  exact (productFunctor data).toEssImage.asEquivalence

/-! ## The base isomorphism `Yddot_v × B(K_v)^0 ≅ Yddot_v` -/

/-- The formal shadow of the paper's assertion that the base field of
`Yddot_v` is `K_v`: the product of `Yddot_v` with the distinguished base
object is isomorphic to the identity slice over `Yddot_v`.

This is an explicit datum of the model.  It is not derived from a real curve,
and it is not an axiom: it is a field of a structure that a caller of the
theory must supply. -/
structure BaseFieldProductIdentification {diagram : Iut.SourceSemiGraphOfAnabelioids.{u}}
    {root : diagram.base.Vertex} {Yddot : ConnectedTemperedCover diagram root}
    {model : BaseFieldCoverModel diagram root}
    (data : ThetaProductData diagram root Yddot model) where
  /-- The isomorphism `Yddot_v × B(K_v)^0 ≅ Yddot_v` in the slice over
  `Yddot_v`. -/
  baseProductIso : Over.mk (data.fst (baseCoverObject model)) ≅ Over.mk (𝟙 Yddot)

/-- Any slice object whose projection to `Yddot_v` is an isomorphism is
isomorphic to the identity slice `Over.mk (𝟙 Yddot_v)`.  This is pure slice
category theory and does not use any base-field hypothesis. -/
noncomputable def sliceObjectIsoIdentityOfIsIsoHom
    {diagram : Iut.SourceSemiGraphOfAnabelioids.{u}}
    {root : diagram.base.Vertex} {Yddot : ConnectedTemperedCover diagram root}
    (object : YddotSlice diagram root Yddot) (h : IsIso object.hom) :
    object ≅ Over.mk (𝟙 Yddot) :=
  Over.isoMk (hl := @asIso _ _ _ _ object.hom h) (by
    change (@asIso _ _ _ _ object.hom h).hom ≫ 𝟙 Yddot = object.hom
    rw [Category.comp_id]
    rfl)

/-- If the base product `Yddot_v × B(K_v)^0` is the identity slice, then every
slice object whose projection is an isomorphism lies in the essential image of
the product functor, i.e. in `D_v^Θ`.  This is the precise form of the
observation in IUT I, Example 3.2(v), that a slice object with projection
isomorphic to `Yddot_v` is isomorphic to a product. -/
theorem thetaCover_mem_of_isIso_hom
    {diagram : Iut.SourceSemiGraphOfAnabelioids.{u}}
    {root : diagram.base.Vertex} {Yddot : ConnectedTemperedCover diagram root}
    {model : BaseFieldCoverModel diagram root}
    (data : ThetaProductData diagram root Yddot model)
    (identification : BaseFieldProductIdentification data)
    (object : YddotSlice diagram root Yddot) (h : IsIso object.hom) :
    (productFunctor data).essImage object := by
  refine ⟨baseCoverObject model, ⟨?_⟩⟩
  exact identification.baseProductIso.trans
    (sliceObjectIsoIdentityOfIsIsoHom object h).symm

/-! ## Empty and disconnected tempered covers -/

/-- Temperedness is vacuous on a cover with no geometric point: the defining
condition quantifies over all geometric points.  Thus `TemperedCover` does not
by itself exclude empty covers. -/
theorem isTempered_of_isEmpty_geometricPoint
    {diagram : Iut.SourceSemiGraphOfAnabelioids.{u}}
    {root : diagram.base.Vertex} {target : diagram.CovObject}
    (empty : IsEmpty (AssociatedQuotient.GeometricPoint target)) :
    IsTempered diagram root target :=
  fun point => (empty.false point).elim

/-- A cover with no geometric point cannot be geometrically connected.  Hence
the connected full subcategory `ConnectedTemperedCover` excludes precisely the
pointless tempered covers on which `IsTempered` is vacuous. -/
theorem not_isGeometricallyConnected_of_isEmpty_geometricPoint
    {diagram : Iut.SourceSemiGraphOfAnabelioids.{u}}
    {target : diagram.CovObject}
    (empty : IsEmpty (AssociatedQuotient.GeometricPoint target)) :
    ¬ AssociatedQuotient.IsGeometricallyConnected target := by
  rintro ⟨basePoint, _⟩
  exact empty.false basePoint

/-- A cover with no geometric point, if one exists, is tempered but not
connected.  Consequently the inclusion `ConnectedTemperedCover → TemperedCover`
can be strict on pointless objects; we do not construct such a cover here, and
the paper's `D_v` is the connected subcategory rather than all of
`TemperedCover`. -/
theorem isTempered_and_not_isGeometricallyConnected_of_isEmpty
    {diagram : Iut.SourceSemiGraphOfAnabelioids.{u}}
    {root : diagram.base.Vertex} {target : diagram.CovObject}
    (empty : IsEmpty (AssociatedQuotient.GeometricPoint target)) :
    IsTempered diagram root target ∧
      ¬ AssociatedQuotient.IsGeometricallyConnected target :=
  ⟨isTempered_of_isEmpty_geometricPoint empty,
    not_isGeometricallyConnected_of_isEmpty_geometricPoint empty⟩

end ThetaLinkSourceCover

end CovObject

end SourceSemiGraphOfAnabelioids

end Iut
