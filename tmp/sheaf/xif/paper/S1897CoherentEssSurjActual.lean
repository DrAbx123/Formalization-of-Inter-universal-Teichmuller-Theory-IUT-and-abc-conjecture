/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors / S1897
-/
import tmp.sheaf.xif.paper.S1878CoherentAffineBridgeActual
import tmp.sheaf.xif.paper.S1419D6NonterminalStackActual
import tmp.sheaf.xif.paper.S1742TwoYonedaActual

/-!
# S1897: the inverse (extension) construction for `S1878EssSurj`

## The question

S1878 proved that the canonical comparison

    S1878Functor : S1878CoherentCategory ⤳ FiniteEtaleCover (Spec R')

from the coherent covers (S1852) to the finite etale covers of `Spec R'` is fully
faithful, and that it is an equivalence **iff**

    S1878EssSurj : forall C : FiniteEtaleCover (Spec R'), exists coherent A,
                     S1816Obj A.cover ~= C.

The remaining statement is the *inverse/extension construction*: given a finite
etale cover `C` of `Spec R'`, construct a coherent cover of the S1726 D6
orbicurve whose identity-point base change is isomorphic to `C`.

## What is constructed here

1. `S1897CoverScheme`, `S1897CoverOver`: the cover `C` as a scheme over `Spec F'`
   together with its structure morphism `C -> Spec R'` as a morphism over
   `Spec F'`.  Both are definitional unfoldings of the S1816 datum (the composite
   with `S1726AffineOver.hom`); no data is chosen.

2. `S1897RepresentableIsStack`: **the representable etale pseudofunctor of any
   scheme over `F'` is an etale stack.**  S1419's discrete-descent theorem
   (`DiscreteSheafStack.discretePseudo_isStack`) plus subcanonicality of the
   etale topology give this for every `T : SchemeOverField F'`; S1726 only
   needed the case `T = Spec R'`.  This is what allows the extension cover to be
   a cover at all: its source stack is the representable stack `y(C.carrier)`.

3. `S1897ExtSource`, `S1897ExtMap`: **the inverse/extension cover of `C`**

       source := y(C.carrier)        (the representable etale stack of the cover)
       map    := y(C -> Spec R')    (S1742's strong transformation of the map).

   This is the only candidate that can work: its identity-point base change is
   `C` itself, and its other base changes are the scheme pullbacks of `C` along
   the test points (see `S1897ExtensionData` below).

4. `S1897TrianglePresentation`: **the identity-point presentation of the
   extension cover is complete, unconditionally.**  The square

       y(C.carrier) --1----> y(C.carrier) --y(f)--> y(Spec R')
       y(C.carrier) --y(f)--> y(Spec R')   --1----> y(Spec R')

   is a genuine base-change presentation: `S1897TriangleWitness` constructs the
   full two-pullback witness (a cone's lift is its first leg; the three
   coherence fields are equalities of 2-cells into a representable stack, hence
   subsingleton by `S1897Modification_subsingleton_representable`), and
   `S1897Triangle_coneEssSurj` proves S1852's full 2-universal property for it.
   Nothing about the identity point is missing.

5. `S1897ExtensionData C`: the exact remaining datum of the extension
   construction at `C` -- a strong finite-etale structure on `S1897ExtMap C`
   whose identity-point presentation *is* the triangle presentation of item 4.
   `S1897FirstMissing` is the statement that this datum exists for every `C`.

6. `S1897EssSurj_of_extensionData`: **`S1878EssSurj` follows from
   `S1897FirstMissing`, unconditionally in everything else.**  The coherent
   cover is the extension cover, its unit 2-cell is S1852's
   (`S1852Unit_of_strong`), and because the identity-point presentation is the
   triangle one its affine model is *literally* `C`
   (`S1733Model = S1897CoverScheme C`, `S1733ModelOver = S1897CoverOver C`),
   hence `S1816Obj` of it is `C` itself.

7. `S1897EssSurj_iff_modelForm`: the object-level content of `S1878EssSurj`,
   unwrapped: every finite etale cover of `Spec R'` is isomorphic *over*
   `Spec R'` to the affine model of a coherent cover.  The coherent-category
   packaging of S1878 adds no content at the object level.

## Why item 5 is the exact first missing, and what its geometric content is

The only field of `CoherentCover` that is not derived from `C` is the family of
base-change presentations of the extension map `y(f)` at the remaining test
schemes and points:

    baseChange : forall (T : SchemeOverField F') (q : y(T) -> y(Spec R')),
                   EtaleStackBaseChangePresentation y(f) T q.

By S1742 (`S1742HomOfStrongTrans`, `S1742Key`) every point `q` is the strong
transformation of a scheme morphism `q~ : T -> Spec R'`, and the canonical
presentation of `y(f)` at `q` is the square of representable stacks induced by
the scheme pullback square

    T x_{Spec R'} C.carrier ----> C.carrier
              |                       |
              v                       v
              T ----------------> Spec R' .

Two independent pieces of mathematics are needed for that presentation.

* **Finite etaleness of the projection.**  This is available: the projection is
  `Limits.pullback.snd f q~`, and `FiniteEtaleCover.finiteEtale_pullback`
  (Mathlib's stability of `Etale` and `IsFinite` under base change) proves it
  finite and etale.  No gap.

* **The representable two-pullback theorem.**  The square of representable
  pseudofunctors induced by a scheme pullback square must be a *bicategorical*
  pullback (`EtalePseudofunctorSquare.TwoPullbackWitness`) *together with* its
  full 2-universal property (S1852's `S1852ConeEssSurj`): for every etale stack
  `W`, every cone over the square and every 1-cell into the pullback whose two
  projections are 2-isomorphic to the cone's projections, that 1-cell is
  2-isomorphic to the cone's lift.  Equivalently: the Yoneda embedding
  `scheme |-> y(scheme)` sends scheme pullback squares to bicategorical
  pullback squares, and the cone comparison is essentially surjective on
  1-cells.  This is *not* in Mathlib and *not* in this tree: `TwoPullbackWitness`
  is only ever constructed here for trivial squares (`S1762IdWitness`,
  `S1852IdStrongBc`, and `S1897TriangleWitness` below), never for a square
  produced by a genuine fibre product.  The descent theorem of S1419 is the
  *stack* property (gluing along covers), which is a different statement: it
  does not identify a pseudo-pullback of representables with the representable
  of the scheme pullback.

The finite-etaleness half and the triangle (identity-point) half are therefore
discharged here; the representable two-pullback theorem is the exact remaining
input, and `S1897ExtensionData` is exactly the data whose construction from it
is then formal (assemble the presentations, apply
`FiniteEtaleCover.finiteEtale_pullback`, and use the triangle presentation at
the identity point).

## Honest boundary

* `S1878EssSurj` is **not** proved, and no equivalence is asserted.  What is
  proved is the implication `S1897FirstMissing -> S1878EssSurj` with everything
  else unconditional, together with the unconditional triangle presentation and
  its full 2-universal property.
* `S1897FirstMissing` is not shown to be *necessary* for `S1878EssSurj`: a
  coherent cover whose affine model is `C` need not be the extension cover.  It
  is the missing input of the inverse construction, not an equivalent
  reformulation of the target.
* No new axiom, no `sorry`, no `Shrink`/`ULift`/`PUnit`, no fake functor, no
  fake equivalence, and no existing definition is modified.  The axiom footprint
  is checked at the end.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1897CoherentEssSurjActual

open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1816OrbicurveCoversToAffineActual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1878CoherentAffineBridgeActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

/-! ## 1. The cover as a scheme over `Spec F'` -/

/-- The carrier of a finite etale cover `C` of `Spec R'`, regarded as a scheme over
`Spec F'` through the structure morphism `Spec R' -> Spec F'`. -/
noncomputable def S1897CoverScheme (C : S1816Target) : Iut.SchemeOverField S1726K :=
  Over.mk (C.obj.hom ≫ S1726AffineOver.hom)

/-- The underlying scheme of `S1897CoverScheme C` is the carrier of `C`. -/
@[simp] theorem S1897CoverScheme_left (C : S1816Target) :
    (S1897CoverScheme C).left = FiniteEtaleCover.carrier C := rfl

/-- The structure morphism of `S1897CoverScheme C` over `Spec F'`. -/
@[simp] theorem S1897CoverScheme_hom (C : S1816Target) :
    (S1897CoverScheme C).hom = FiniteEtaleCover.structureMap C ≫ S1726AffineOver.hom := rfl

/-- The structure morphism `C -> Spec R'` as a morphism of schemes over `Spec F'`. -/
noncomputable def S1897CoverOver (C : S1816Target) :
    S1897CoverScheme C ⟶ S1726AffineOver :=
  Over.homMk C.obj.hom (by rfl)

/-- The underlying scheme morphism of `S1897CoverOver C` is the structure map of `C`. -/
@[simp] theorem S1897CoverOver_left (C : S1816Target) :
    (S1897CoverOver C).left = FiniteEtaleCover.structureMap C := rfl

/-! ## 2. Representable etale stacks of arbitrary schemes over `F'` -/

/-- **Every representable etale pseudofunctor over `F'` is an etale stack.**  S1419's
discrete-descent theorem (a sheaf of types gives a stack for its discrete-category
pseudofunctor) plus subcanonicality of the etale topology.  S1726 recorded the case
`T = Spec R'` only; the extension construction needs it for the carrier of an
arbitrary cover. -/
theorem S1897RepresentableIsStack (T : Iut.SchemeOverField S1726K) :
    (Iut.schemeRepresentableEtalePseudofunctor S1726K T).IsStack
      (Iut.SchemeOverField.etaleTopology S1726K) := by
  have hP : Presieve.IsSheaf (Iut.SchemeOverField.etaleTopology S1726K)
      (yoneda.obj T) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      (LeanFormal.IUT.N8Closure.RepresentableStackIsStackConstructed.representableEtalePresheaf_isSheaf
        (F := S1726K) T)
  change (LeanFormal.IUT.N8Closure.DiscreteSheafIsStack.discretePseudo
    (C := Iut.SchemeOverField S1726K) (yoneda.obj T)).IsStack
      (Iut.SchemeOverField.etaleTopology S1726K)
  exact DiscreteSheafStack.discretePseudo_isStack (P := yoneda.obj T) hP

/-! ## 3. The inverse/extension construction -/

/-- The source stack of the extension cover: the representable etale stack of the
carrier of `C`. -/
noncomputable def S1897ExtSource (C : S1816Target) : EtaleStackOverField S1726K where
  fiber := Iut.schemeRepresentableEtalePseudofunctor S1726K (S1897CoverScheme C)
  isStack := S1897RepresentableIsStack (S1897CoverScheme C)

/-- The fibre of the extension source is the representable stack of the carrier. -/
@[simp] theorem S1897ExtSource_fiber (C : S1816Target) :
    (S1897ExtSource C).fiber =
      Iut.schemeRepresentableEtalePseudofunctor S1726K (S1897CoverScheme C) := rfl

/-- The structure map of the extension cover: the strong transformation induced by
the scheme morphism `C -> Spec R'` (S1742). -/
noncomputable def S1897ExtMap (C : S1816Target) :
    (S1897ExtSource C).Hom S1726Orbicurve.stack :=
  S1742StrongTransOfHom (S1897CoverOver C)

/-- The extension map is the Yoneda image of `C -> Spec R'`. -/
theorem S1897ExtMap_eq (C : S1816Target) :
    S1897ExtMap C =
      S1742StrongTransOfHom (S1897CoverOver C) := rfl

/-- The Yoneda inverse of the extension map is the structure morphism of `C`
(S1742's round trip on scheme morphisms). -/
theorem S1897HomOfExtMap (C : S1816Target) :
    S1742HomOfStrongTrans (S1897ExtMap C) = S1897CoverOver C :=
  S1742HomOfStrongTrans_strongTransOfHom (S1897CoverOver C)

/-! ## 4. 2-cells into a representable stack are subsingletons -/

/-- Natural transformations between functors into a discrete category are
subsingletons. -/
theorem S1897NatTrans_discrete_subsingleton {D : Type*} [Category D] {alpha : Type}
    (F G : D ⥤ Discrete alpha) : Subsingleton (F ⟶ G) := by
  constructor
  intro a b
  apply CategoryTheory.NatTrans.ext
  funext Z
  exact Subsingleton.elim _ _

/-- **Modifications between strong transformations into a representable etale stack
are subsingletons.**  Every component lands in a discrete category. -/
theorem S1897Modification_subsingleton_representable
    {W : EtaleStackPseudofunctor S1726K} {T : Iut.SchemeOverField S1726K}
    (L L' : W ⟶ Iut.schemeRepresentableEtalePseudofunctor S1726K T) :
    Subsingleton (L ⟶ L') := by
  constructor
  intro a b
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro U
  apply CategoryTheory.Cat.Hom₂.ext
  haveI : Subsingleton ((L.app U).toFunctor ⟶ (L'.app U).toFunctor) :=
    S1897NatTrans_discrete_subsingleton _ _
  exact Subsingleton.elim _ _

/-! ## 5. The identity-point presentation of the extension cover -/

/-- The comparison 2-isomorphism of the triangle square:
`1 ; y(f) ~= y(f) ; 1`. -/
noncomputable def S1897TriangleCommutes (C : S1816Target) :
    Iso (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.id
            (Iut.schemeRepresentableEtalePseudofunctor S1726K (S1897CoverScheme C)))
          (S1897ExtMap C))
        (Pseudofunctor.StrongTrans.vcomp (S1897ExtMap C)
          (Pseudofunctor.StrongTrans.id S1726Orbicurve.stack.fiber)) :=
  (Pseudofunctor.StrongTrans.leftUnitor (S1897ExtMap C)).trans
    (Pseudofunctor.StrongTrans.rightUnitor (S1897ExtMap C)).symm

/-- The triangle square of the extension cover at the identity point. -/
noncomputable def S1897TriangleSquare (C : S1816Target) :
    EtalePseudofunctorSquare
      (Iut.schemeRepresentableEtalePseudofunctor S1726K (S1897CoverScheme C))
      (Iut.schemeRepresentableEtalePseudofunctor S1726K (S1897CoverScheme C))
      (Iut.schemeRepresentableEtalePseudofunctor S1726K S1726AffineOver)
      (Iut.schemeRepresentableEtalePseudofunctor S1726K S1726AffineOver) :=
  EtalePseudofunctorSquare.mk
    (P := Iut.schemeRepresentableEtalePseudofunctor S1726K (S1897CoverScheme C))
    (X := Iut.schemeRepresentableEtalePseudofunctor S1726K (S1897CoverScheme C))
    (Y := Iut.schemeRepresentableEtalePseudofunctor S1726K S1726AffineOver)
    (Z := Iut.schemeRepresentableEtalePseudofunctor S1726K S1726AffineOver)
    (Pseudofunctor.StrongTrans.id _) (S1897ExtMap C) (S1897ExtMap C)
    (Pseudofunctor.StrongTrans.id S1726Orbicurve.stack.fiber)
    (S1897TriangleCommutes C)

/-- **The triangle square is a bicategorical pullback.**  A cone's lift is its first
leg (`P = X` in this square); the three coherence fields are equalities of 2-cells
into a representable stack, hence subsingleton. -/
noncomputable def S1897TriangleWitness (C : S1816Target) :
    (S1897TriangleSquare C).TwoPullbackWitness where
  lift _ cone := cone.toX
  liftToX _ cone := Pseudofunctor.StrongTrans.rightUnitor cone.toX
  liftToY _ cone := cone.commutes.trans (Pseudofunctor.StrongTrans.rightUnitor cone.toY)
  liftTwoCell _ _ _ morphism := morphism.toX
  liftTwoCell_toX := by
    intro W source target morphism
    haveI : Subsingleton
        ((Pseudofunctor.StrongTrans.vcomp source.toX (S1897TriangleSquare C).toX) ⟶
          (Pseudofunctor.StrongTrans.vcomp target.toX (S1897TriangleSquare C).toX)) :=
      S1897Modification_subsingleton_representable _ _
    exact Subsingleton.elim _ _
  liftTwoCell_toY := by
    intro W source target morphism
    haveI : Subsingleton
        ((Pseudofunctor.StrongTrans.vcomp source.toX (S1897TriangleSquare C).toY) ⟶
          (Pseudofunctor.StrongTrans.vcomp target.toX (S1897TriangleSquare C).toY)) :=
      S1897Modification_subsingleton_representable _ _
    exact Subsingleton.elim _ _
  twoCell_ext := by
    intro W first second alpha beta h1 h2
    exact (S1897Modification_subsingleton_representable first second).elim alpha beta

/-- **The identity-point base-change presentation of the extension cover.**  The
pullback scheme is the carrier of `C` itself, the projection is the structure
morphism of `C`, and the square is the triangle square. -/
noncomputable def S1897TrianglePresentation (C : S1816Target) :
    EtaleStackBaseChangePresentation (S1897ExtMap C) S1726AffineOver S1733BasePoint where
  pullbackScheme := S1897CoverScheme C
  projection := S1897CoverOver C
  projectionMap :=
    { transformation := S1742StrongTransOfHom (S1897CoverOver C)
      app_eq := fun _ => rfl }
  toSource := Pseudofunctor.StrongTrans.id _
  commutes := S1897TriangleCommutes C
  isPullback := S1897TriangleWitness C

/-- Its pullback scheme is the carrier of `C` over `Spec F'`. -/
@[simp] theorem S1897TrianglePresentation_pullbackScheme (C : S1816Target) :
    (S1897TrianglePresentation C).pullbackScheme = S1897CoverScheme C := rfl

/-- Its projection is the structure morphism of `C`. -/
@[simp] theorem S1897TrianglePresentation_projection (C : S1816Target) :
    (S1897TrianglePresentation C).projection = S1897CoverOver C := rfl

/-- **The full 2-universal property holds at the identity point, unconditionally.**
Any 1-cell into the extension cover whose first projection is 2-isomorphic to the
cone's first leg is 2-isomorphic to the cone's lift, because the target is a
representable stack. -/
theorem S1897Triangle_coneEssSurj (C : S1816Target) :
    S1852ConeEssSurj (S1897TrianglePresentation C) := by
  intro W c phi hX _hY
  obtain ⟨eX⟩ := hX
  exact ⟨(Pseudofunctor.StrongTrans.rightUnitor phi).symm.trans eX⟩

/-- **The identity-point base change of the extension map carries a *strong*
presentation** (S1852): the triangle presentation together with its full
2-universal property.  Thus nothing at the identity point is missing from the inverse
construction. -/
noncomputable def S1897TriangleStrong (C : S1816Target) :
    StrongEtaleStackBaseChangePresentation (S1897ExtMap C) S1726AffineOver S1733BasePoint where
  toWeak := S1897TrianglePresentation C
  coneEssSurj := S1897Triangle_coneEssSurj C

/-! ## 6. The extension datum and the main implication -/

/-- **The extension datum at a cover `C`.**  A strong finite-etale structure on the
extension map whose identity-point presentation is the triangle presentation of
`S1897TrianglePresentation`, i.e. whose affine model is `C` itself.  Its only
non-trivial field is `strong`; the matching condition `idPresentation` is exactly
what a canonical fibre-product construction gives, since the identity-point
pullback of `C` along `1 : Spec R' -> Spec R'` is `C`. -/
structure S1897ExtensionData (C : S1816Target) where
  /-- The strong finite-etale structure on the extension map. -/
  strong : StrongEtaleStackFiniteEtaleMorphism (S1897ExtMap C)
  /-- The identity-point presentation is the triangle presentation. -/
  idPresentation : strong.toWeak.baseChange S1726AffineOver S1733BasePoint =
    S1897TrianglePresentation C

/-- The extension datum exists at every finite etale cover of `Spec R'`.  This is the
exact first missing input of the inverse construction; see the module docstring. -/
def S1897FirstMissing : Prop := ∀ C : S1816Target, Nonempty (S1897ExtensionData C)

/-- The recorded cover underlying the extension construction at `C`. -/
noncomputable def S1897ExtCover (C : S1816Target)
    (M : StrongEtaleStackFiniteEtaleMorphism (S1897ExtMap C)) : S1728Cover where
  source := S1897ExtSource C
  map := S1897ExtMap C
  finiteEtale := M.toWeak

/-- The coherent cover of the extension construction at `C`.  Its unit 2-cell is
derived from the full 2-universal property, by S1852. -/
noncomputable def S1897ExtCoherent (C : S1816Target)
    (M : StrongEtaleStackFiniteEtaleMorphism (S1897ExtMap C)) : CoherentCover :=
  CoherentCover.ofStrong
    { source := S1897ExtSource C, map := S1897ExtMap C, finiteEtale := M }

/-- The underlying recorded cover of the coherent extension cover is the extension
cover. -/
@[simp] theorem S1897ExtCoherent_cover (C : S1816Target)
    (M : StrongEtaleStackFiniteEtaleMorphism (S1897ExtMap C)) :
    (S1897ExtCoherent C M).cover = S1897ExtCover C M := rfl

/-- Its finite-etale structure is the weak image of the strong structure. -/
@[simp] theorem S1897ExtCoherent_finiteEtale (C : S1816Target)
    (M : StrongEtaleStackFiniteEtaleMorphism (S1897ExtMap C)) :
    (S1897ExtCover C M).finiteEtale = M.toWeak := rfl

/-- **The affine model of the coherent extension cover is `C` itself**, from the
triangle presentation. -/
theorem S1897ExtCoherent_model (C : S1816Target)
    (d : S1897ExtensionData C) :
    S1733Model (S1897ExtCoherent C d.strong).cover = S1897CoverScheme C := by
  show (d.strong.toWeak.baseChange S1726AffineOver S1733BasePoint).pullbackScheme =
    S1897CoverScheme C
  rw [d.idPresentation]
  rfl

/-- The affine model of a base-change presentation, as an object of `Over (Spec R')`.
It is written through `Over.mk` of the projection, so that it depends on the
presentation only through a *nondependent* expression: the type of `Over.mk m` does
not depend on the source scheme of `m`.  This is what makes the transport along an
equality of presentations available below. -/
noncomputable def S1897ModelOfPresentation (C : S1816Target)
    (P : EtaleStackBaseChangePresentation (S1897ExtMap C) S1726AffineOver S1733BasePoint) :
    Over S1816Base :=
  Over.mk P.projection.left

/-- **The model of the triangle presentation is `C` itself.** -/
theorem S1897ModelOfPresentation_triangle (C : S1816Target) :
    S1897ModelOfPresentation C (S1897TrianglePresentation C) = C.obj := rfl

/-- **The affine model of the coherent extension cover is `C` itself.**  The only
input is the identity-point presentation of the extension datum. -/
theorem S1897ExtCoherent_modelOver (C : S1816Target) (d : S1897ExtensionData C) :
    S1897ModelOfPresentation C
        ((S1897ExtCoherent C d.strong).cover.finiteEtale.baseChange S1726AffineOver
          S1733BasePoint) = C.obj := by
  rw [show (S1897ExtCoherent C d.strong).cover.finiteEtale.baseChange S1726AffineOver
    S1733BasePoint = S1897TrianglePresentation C from d.idPresentation]
  exact S1897ModelOfPresentation_triangle C

/-- **`S1878EssSurj` follows from the inverse/extension construction.**
Every finite etale cover of `Spec R'` is the affine model of a coherent cover. -/
theorem S1897EssSurj_of_extensionData (h : S1897FirstMissing) : S1878EssSurj := by
  intro C
  obtain ⟨d⟩ := h C
  have hmodel := S1897ExtCoherent_modelOver C d
  refine ⟨S1897ExtCoherent C d.strong, ⟨ObjectProperty.isoMk
    (P := fun X : Over S1816Base => IsFiniteEtaleHom X.hom) ?_⟩⟩
  show (S1878Obj (S1897ExtCoherent C d.strong)).obj ≅ C.obj
  exact eqToIso hmodel

/-- The canonical comparison functor is an equivalence, from the extension
construction (S1878's criterion: full and faithful are unconditional). -/
theorem S1897Functor_isEquivalence_of_extensionData (h : S1897FirstMissing) :
    S1878Functor.IsEquivalence :=
  S1878Functor_isEquivalence_iff_essSurj.mpr (S1897EssSurj_of_extensionData h)

/-- Consequently the composite comparison with the affine slice is an equivalence. -/
theorem S1897FunctorToSlice_isEquivalence_of_extensionData (h : S1897FirstMissing) :
    S1878FunctorToSlice.IsEquivalence :=
  S1878FunctorToSlice_isEquivalence_iff_essSurj.mpr (S1897EssSurj_of_extensionData h)

/-! ## 7. The object-level form of the target -/

/-- **The object-level content of `S1878EssSurj`**: every finite etale cover of
`Spec R'` is isomorphic, over `Spec R'`, to the affine model of a coherent cover. -/
def S1897ModelEssSurj : Prop :=
  ∀ C : S1816Target, ∃ A : CoherentCover,
    Nonempty ((S1816Obj A.cover).obj ≅ C.obj)

/-- `S1878EssSurj` is exactly its object-level model form: the coherent-category
packaging of S1878 adds no content at the level of objects. -/
theorem S1897_essSurj_iff_modelForm : S1878EssSurj ↔ S1897ModelEssSurj := by
  constructor
  · intro h C
    obtain ⟨A, ⟨e⟩⟩ := h C
    exact ⟨A, ⟨(FiniteEtaleCover.forgetOver S1816Base).mapIso e⟩⟩
  · intro h C
    obtain ⟨A, ⟨e⟩⟩ := h C
    exact ⟨A, ⟨ObjectProperty.isoMk _ e⟩⟩

/-! ## 8. The exact missing geometric input, named

The results above reduce `S1878EssSurj` to `S1897FirstMissing`: a strong
finite-etale structure on the representable extension map, with the identity-point
presentation fixed to the triangle presentation (which is constructed here,
unconditionally, together with its full 2-universal property).  The geometric content
of `S1897FirstMissing` is the following single statement about representable etale
stacks: the Yoneda embedding `scheme |-> y(scheme)` carries scheme pullback squares
to bicategorical pullback squares *with* the full 2-universal property.  It is
recorded here as a named proposition so that it can be attacked independently; it is
not assumed anywhere in this file. -/

/-- The representable etale stack of a scheme over `F'`. -/
noncomputable abbrev S1897Y (T : Iut.SchemeOverField S1726K) :
    EtaleStackPseudofunctor S1726K :=
  Iut.schemeRepresentableEtalePseudofunctor S1726K T

/-- **The exact missing geometric input.**  For every pullback square of schemes over
`F'`, the induced square of representable etale stacks is a bicategorical pullback
(a two-pullback witness) whose cone comparison is essentially surjective on 1-cells,
i.e. it satisfies S1852's full 2-universal property.  The legs of the square are
required to be the Yoneda images of the scheme morphisms. -/
def S1897RepresentableTwoPullback : Prop :=
  ∀ (X Y Z P : Iut.SchemeOverField S1726K) (f : X ⟶ Z) (g : Y ⟶ Z)
    (pX : P ⟶ X) (pY : P ⟶ Y)
    (sq : EtalePseudofunctorSquare (S1897Y P) (S1897Y X) (S1897Y Y) (S1897Y Z)),
    sq.toX = S1742StrongTransOfHom pX →
    sq.toY = S1742StrongTransOfHom pY →
    sq.xToBase = S1742StrongTransOfHom f →
    sq.yToBase = S1742StrongTransOfHom g →
    ∃ w : sq.TwoPullbackWitness,
      ∀ (W : EtaleStackPseudofunctor S1726K) (c : sq.Cone W)
        (phi : Pseudofunctor.StrongTrans W (S1897Y P)),
        Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp phi sq.toX) c.toX) →
        Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp phi sq.toY) c.toY) →
        Nonempty (Iso phi (w.lift W c))

/-! ## 9. Checks and axiom footprint -/

#check S1897CoverScheme
#check S1897CoverOver
#check S1897RepresentableIsStack
#check S1897ExtSource
#check S1897ExtMap
#check S1897HomOfExtMap
#check S1897Modification_subsingleton_representable
#check S1897TriangleCommutes
#check S1897TriangleSquare
#check S1897TriangleWitness
#check S1897TrianglePresentation
#check S1897Triangle_coneEssSurj
#check S1897TriangleStrong
#check S1897ExtensionData
#check S1897FirstMissing
#check S1897ExtCover
#check S1897ExtCoherent
#check S1897ExtCoherent_model
#check S1897ModelOfPresentation
#check S1897ModelOfPresentation_triangle
#check S1897ExtCoherent_modelOver
#check S1897EssSurj_of_extensionData
#check S1897Functor_isEquivalence_of_extensionData
#check S1897FunctorToSlice_isEquivalence_of_extensionData
#check S1897ModelEssSurj
#check S1897_essSurj_iff_modelForm
#check S1897Y
#check S1897RepresentableTwoPullback

#print axioms S1897RepresentableIsStack
#print axioms S1897ExtSource
#print axioms S1897ExtMap
#print axioms S1897Modification_subsingleton_representable
#print axioms S1897TriangleWitness
#print axioms S1897TrianglePresentation
#print axioms S1897Triangle_coneEssSurj
#print axioms S1897TriangleStrong
#print axioms S1897ExtCoherent
#print axioms S1897ExtCoherent_model
#print axioms S1897EssSurj_of_extensionData
#print axioms S1897_essSurj_iff_modelForm

end LeanFormal.IUT.XiFPaper.S1897CoherentEssSurjActual
