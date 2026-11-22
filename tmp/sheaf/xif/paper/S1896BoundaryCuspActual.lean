/-
# S1896: the cusp's compactification / representable open immersion

S1887 reduced the D9 cusp exactly to 'Nonempty (Iut.OrbicurveBoundaryCusp S.cK)' and
exposed its first field (the compactification stack) and its first hard field, the
representable open immersion 'Iut.EtaleStackOpenImmersion'.  It recorded that *no*
inhabitant of 'EtaleStackRepresentableMorphismProperty' (hence of
'EtaleStackOpenImmersion') exists anywhere in the tree, so the representability
machinery was itself an open obligation.

This file does two things.

## 1. The representable open immersion of the identity is constructed

For *any* etale stack 'Y' over 'F', the identity morphism 'Y.stack ⟶ Y.stack' is
representably an open immersion:

    S1896IdentityOpenImmersion (Y) : Iut.EtaleStackOpenImmersion (𝟙 Y.fiber).

This is a genuine construction, not an assumption.  For every test scheme 'T' and
every scheme-valued point 'point : h_T ⟶ Y.fiber' of 'Y', the base change is the
2-pullback of '(𝟙, point)', whose apex is the test scheme itself (the "apex = the
scheme" model of S1804's item 2, where the actual 2-pullback of '(A.map, id)' is the
source; here the actual 2-pullback of '(𝟙, point)' is 'h_T'):

    S1896IdentityBaseChange Y T point : EtaleStackBaseChangePresentation (𝟙 Y.fiber) T point

with 'pullbackScheme = T', 'projection = 𝟙 T', 'toSource = point' and a *full*
'TwoPullbackWitness' ('S1896IdentityPullback'): lift = the test-scheme leg of the
cone, the two comparison 2-cells from the cone's own 2-commuting square and the unit
2-isomorphism of the 2-Yoneda projection, lift on 2-cells = the test-scheme leg, and
2-cell extensionality because every 2-cell between strong transformations into a
represented stack has discrete components.  The only auxiliary inputs are

    S1896YonedaOneIso (T) : S1742StrongTransOfHom (𝟙 T) ≅ 𝟙 (h_T),

the unit comparison of the 2-Yoneda 1-cell of '𝟙 T' with the identity, proved from
'Category.comp_id' on the discrete category of sections, and the bicategorical unit
and exchange laws in the explicitly instantiated form used throughout the tree
('S1896RightUnitorIso', 'S1896WhiskerLeftIso', 'S1896WhiskerRightId',
'S1896WhiskerExchange', 'S1896WhiskerRightIff').

No schematic fiber product beyond the test scheme is needed here, because the
2-pullback of '(𝟙, point)' is computed on the nose; for a *proper* compactification
'Z' of 'X' the same fields must be filled by the schematic fiber product
'T ×_Z X' inside 'Z', which is exactly what does not exist in the tree.

## 2. The exact first missing of the D9 cusp, and why the identity does not fill it

The boundary condition of a cusp is incompatible with the identity open map: the
boundary point of the compactification would be isomorphic to itself, so the very
object that must avoid the open orbicurve lies in its image
('S1896Id_not_boundary').  Consequently the cusp's own base-change presentation at
its boundary point forces the open map to fail to be essentially surjective at the
residue scheme ('S1896Cusp_openMap_app_not_essSurj'), while the identity's open map
*is* essentially surjective at every scheme ('S1896Id_app_essSurj').

Hence the constructed 'S1896IdentityOpenImmersion' is *not* the cusp's open
immersion: it can never be, for any candidate compactification equal to 'X.stack'
and any candidate boundary point.  The cusp datum is exactly
(the compactification stack, a representable open immersion of 'X.stack' into it,
a residue scheme, a point of its fiber, and the separation condition)
('S1896CuspEquivOpenData'), and the construction of the middle object for the D9
'C_K' is the first missing datum: a compactification stack of 'S.cK' strictly
extending it, with an open immersion that is *not* levelwise essentially surjective
at the boundary point ('S1896FirstMissing_structure').

No 'True', 'PUnit', fake cusp, fake open immersion, 'sorry', 'admit' or new axiom is
used.  The identity open immersion is a theorem about the identity; it is not
offered as the cusp of anything.
-/

import tmp.sheaf.xif.paper.S1887D9CuspActual
import tmp.sheaf.xif.paper.S1742TwoYonedaActual

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1896BoundaryCuspActual

open CategoryTheory
open CategoryTheory.Bicategory
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1887D9CuspActual
open LeanFormal.IUT.XiFPaper.S1881D9D7bActual
open LeanFormal.IUT.XiFPaper.S1732SourceAssemblyActual

variable {F : Type} [Field F]

/-! ## 0. Bicategorical 2-isomorphism calculus at the instantiated bicategory -/

/-- Left whiskering of a 2-isomorphism of strong transformations. -/
noncomputable def S1896WhiskerLeftIso {A B C : EtaleStackPseudofunctor F}
    (f : Pseudofunctor.StrongTrans A B) (g g' : Pseudofunctor.StrongTrans B C)
    (e : Iso g g') :
    Iso (Pseudofunctor.StrongTrans.vcomp f g) (Pseudofunctor.StrongTrans.vcomp f g') := by
  let Bicat := EtaleStackPseudofunctor F
  letI : Bicategory Bicat := inferInstance
  let source : Bicat := A
  let mid : Bicat := B
  let target : Bicat := C
  let fmap : source ⟶ mid := f
  let gmap : mid ⟶ target := g
  let gmap' : mid ⟶ target := g'
  exact @Bicategory.whiskerLeftIso Bicat _ source mid target fmap gmap gmap' e

/-- Right whiskering of a 2-isomorphism of strong transformations. -/
noncomputable def S1896WhiskerRightIso {A B C : EtaleStackPseudofunctor F}
    (f f' : Pseudofunctor.StrongTrans A B) (g : Pseudofunctor.StrongTrans B C)
    (e : Iso f f') :
    Iso (Pseudofunctor.StrongTrans.vcomp f g) (Pseudofunctor.StrongTrans.vcomp f' g) := by
  let Bicat := EtaleStackPseudofunctor F
  letI : Bicategory Bicat := inferInstance
  let source : Bicat := A
  let mid : Bicat := B
  let target : Bicat := C
  let fmap : source ⟶ mid := f
  let fmap' : source ⟶ mid := f'
  let gmap : mid ⟶ target := g
  exact @Bicategory.whiskerRightIso Bicat _ source mid target fmap fmap' e gmap

/-- The left unitor of a strong transformation. -/
noncomputable def S1896LeftUnitorIso {A B : EtaleStackPseudofunctor F}
    (f : Pseudofunctor.StrongTrans A B) :
    Iso (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.id A) f) f := by
  let Bicat := EtaleStackPseudofunctor F
  letI : Bicategory Bicat := inferInstance
  let source : Bicat := A
  let target : Bicat := B
  let fmap : source ⟶ target := f
  exact @Bicategory.leftUnitor Bicat _ source target fmap

/-- The right unitor of a strong transformation. -/
noncomputable def S1896RightUnitorIso {A B : EtaleStackPseudofunctor F}
    (f : Pseudofunctor.StrongTrans A B) :
    Iso (Pseudofunctor.StrongTrans.vcomp f (Pseudofunctor.StrongTrans.id B)) f := by
  let Bicat := EtaleStackPseudofunctor F
  letI : Bicategory Bicat := inferInstance
  let source : Bicat := A
  let target : Bicat := B
  let fmap : source ⟶ target := f
  exact @Bicategory.rightUnitor Bicat _ source target fmap

/-- The right-whiskering unit law, in instantiated form. -/
theorem S1896WhiskerRightId {A B : EtaleStackPseudofunctor F}
    {f g : Pseudofunctor.StrongTrans A B} (eta : f ⟶ g) :
    Pseudofunctor.StrongTrans.whiskerRight eta (Pseudofunctor.StrongTrans.id B) =
      (S1896RightUnitorIso f).hom ≫ eta ≫ (S1896RightUnitorIso g).inv := by
  let Bicat := EtaleStackPseudofunctor F
  letI : Bicategory Bicat := inferInstance
  let source : Bicat := A
  let target : Bicat := B
  let fmap : source ⟶ target := f
  let gmap : source ⟶ target := g
  exact @Bicategory.whiskerRight_id Bicat _ source target fmap gmap eta

/-- The exchange law, in instantiated form. -/
theorem S1896WhiskerExchange {A B C : EtaleStackPseudofunctor F}
    {f g : Pseudofunctor.StrongTrans A B} {h k : Pseudofunctor.StrongTrans B C}
    (eta : f ⟶ g) (theta : h ⟶ k) :
    Pseudofunctor.StrongTrans.whiskerLeft f theta ≫
        Pseudofunctor.StrongTrans.whiskerRight eta k =
      Pseudofunctor.StrongTrans.whiskerRight eta h ≫
        Pseudofunctor.StrongTrans.whiskerLeft g theta := by
  let Bicat := EtaleStackPseudofunctor F
  letI : Bicategory Bicat := inferInstance
  let source : Bicat := A
  let mid : Bicat := B
  let target : Bicat := C
  let fmap : source ⟶ mid := f
  let gmap : source ⟶ mid := g
  let hmap : mid ⟶ target := h
  let kmap : mid ⟶ target := k
  exact @Bicategory.whisker_exchange Bicat _ source mid target fmap gmap hmap kmap eta theta

/-- Right-whiskering by an identity 1-cell is injective on 2-cells. -/
theorem S1896WhiskerRightIff {A B : EtaleStackPseudofunctor F}
    {f g : Pseudofunctor.StrongTrans A B} (eta theta : f ⟶ g) :
    Pseudofunctor.StrongTrans.whiskerRight eta (Pseudofunctor.StrongTrans.id B) =
        Pseudofunctor.StrongTrans.whiskerRight theta (Pseudofunctor.StrongTrans.id B) ↔
      eta = theta := by
  let Bicat := EtaleStackPseudofunctor F
  letI : Bicategory Bicat := inferInstance
  let source : Bicat := A
  let target : Bicat := B
  let fmap : source ⟶ target := f
  let gmap : source ⟶ target := g
  exact @Bicategory.whiskerRight_iff Bicat _ source target fmap gmap eta theta

/-- 2-cells between strong transformations into a represented stack are unique:
every component lands in a discrete category. -/
theorem S1896Modification_subsingleton {A : EtaleStackPseudofunctor F}
    (S : SchemeOverField F) {f g : Pseudofunctor.StrongTrans A (S1742YS (F := F) S)}
    (alpha beta : f ⟶ g) : alpha = beta := by
  apply Pseudofunctor.StrongTrans.Hom.ext
  apply Pseudofunctor.StrongTrans.Modification.ext
  funext b
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext x
  apply ULift.ext
  exact Subsingleton.elim _ _


/-! ## 1. The 2-Yoneda 1-cell of the identity is the identity 1-cell -/

/-- The app component at any test object of the 2-Yoneda 1-cell of the identity
scheme map is the identity functor on the discrete category of sections. -/
theorem S1896App_one_eq_id (T : SchemeOverField F)
    (a : LocallyDiscrete (SchemeOverField F)ᵒᵖ) :
    S1742App (F := F) (𝟙 T) a = 𝟙 ((S1742YS (F := F) T).obj a) := by
  apply Cat.ext
  rw [Cat.Hom.id_toFunctor]
  apply Discrete.functor_ext
  intro P
  exact Discrete.ext (Category.comp_id P)

/-- **The unit comparison of the 2-Yoneda 1-cell of the identity.**  The strong
transformation induced by the identity of a test scheme is 2-isomorphic to the
identity strong transformation of the represented stack. -/
noncomputable def S1896YonedaOneIso (T : SchemeOverField F) :
    S1742StrongTransOfHom (F := F) (𝟙 T) ≅
      Pseudofunctor.StrongTrans.id (S1742YS (F := F) T) :=
  Pseudofunctor.StrongTrans.isoMk (fun a => eqToIso (S1896App_one_eq_id T a)) (by
    intro a b g
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    apply ULift.ext
    exact Subsingleton.elim _ _)

/-- The represented 1-cell of the identity scheme map evaluated at the scheme
itself is the identity section. -/
theorem S1896YonedaOneIso_app_one (T : SchemeOverField F) :
    ((S1742StrongTransOfHom (F := F) (𝟙 T)).app
        (LocallyDiscrete.mk (Opposite.op T))).toFunctor.obj (Discrete.mk (𝟙 T)) =
      Discrete.mk (𝟙 T) := by
  show Discrete.mk (𝟙 T ≫ 𝟙 T) = Discrete.mk (𝟙 T)
  exact Discrete.ext (Category.id_comp _)

/-! ## 2. The projection map of the identity test scheme -/

/-- The scheme-representable map of the identity of a scheme: the 2-Yoneda 1-cell of
the identity, with its app component pinned to postcomposition with the identity. -/
noncomputable def S1896IdentityProjectionMap (T : SchemeOverField F) :
    SchemeRepresentableMap (F := F) (𝟙 T) where
  transformation := S1742StrongTransOfHom (F := F) (𝟙 T)
  app_eq := fun U => rfl

/-! ## 3. The 2-pullback of the identity cospan -/

/-- The 2-commuting square of the identity base change at a scheme-valued point:
the source is the test scheme itself. -/
noncomputable def S1896IdentityCommutes (Y : EtaleStackOverField F) (T : SchemeOverField F)
    (point : Pseudofunctor.StrongTrans (S1742YS (F := F) T) Y.fiber) :
    Iso (Pseudofunctor.StrongTrans.vcomp point (Pseudofunctor.StrongTrans.id Y.fiber))
      (Pseudofunctor.StrongTrans.vcomp (S1742StrongTransOfHom (F := F) (𝟙 T)) point) :=
  (S1896RightUnitorIso point).trans
    ((S1896LeftUnitorIso point).symm.trans
      (S1896WhiskerRightIso (S1742StrongTransOfHom (F := F) (𝟙 T))
        (Pseudofunctor.StrongTrans.id (S1742YS (F := F) T)) point
        (S1896YonedaOneIso T)).symm)

/-- The identity base-change square as an etale-pseudofunctor square. -/
noncomputable def S1896IdentitySquare (Y : EtaleStackOverField F) (T : SchemeOverField F)
    (point : Pseudofunctor.StrongTrans (S1742YS (F := F) T) Y.fiber) :
    EtalePseudofunctorSquare (S1742YS (F := F) T) Y.fiber
      (S1742YS (F := F) T) Y.fiber where
  toX := point
  toY := S1742StrongTransOfHom (F := F) (𝟙 T)
  xToBase := Pseudofunctor.StrongTrans.id Y.fiber
  yToBase := point
  commutes := S1896IdentityCommutes Y T point

/-- **The identity base-change square is a full 2-pullback.**  The apex is the test
scheme; the lift of a cone is its test-scheme leg, the two comparison 2-cells are
the cone's own 2-commuting square and the unit comparison of the 2-Yoneda 1-cell,
and the two 2-cell laws are the right-whiskering unit law together with the exchange
law (the second is automatic because the represented stack has discrete
components). -/
noncomputable def S1896IdentityPullback (Y : EtaleStackOverField F) (T : SchemeOverField F)
    (point : Pseudofunctor.StrongTrans (S1742YS (F := F) T) Y.fiber) :
    (S1896IdentitySquare Y T point).TwoPullbackWitness where
  lift _ cone := cone.toY
  liftToX _ cone := cone.commutes.symm.trans (S1896RightUnitorIso cone.toX)
  liftToY _ cone :=
    (S1896WhiskerLeftIso cone.toY (S1742StrongTransOfHom (F := F) (𝟙 T))
      (Pseudofunctor.StrongTrans.id (S1742YS (F := F) T))
      (S1896YonedaOneIso T)).trans (S1896RightUnitorIso cone.toY)
  liftTwoCell _ _ _ m := m.toY
  liftTwoCell_toX _ source target m := by
    have hsq : Pseudofunctor.StrongTrans.whiskerRight m.toX
        (Pseudofunctor.StrongTrans.id Y.fiber) =
        (S1896RightUnitorIso source.toX).hom ≫ m.toX ≫
          (S1896RightUnitorIso target.toX).inv :=
      S1896WhiskerRightId m.toX
    have hcompat : Pseudofunctor.StrongTrans.whiskerRight m.toX
          (Pseudofunctor.StrongTrans.id Y.fiber) ≫ target.commutes.hom =
        source.commutes.hom ≫ Pseudofunctor.StrongTrans.whiskerRight m.toY point :=
      m.compatibility
    have h1 : Pseudofunctor.StrongTrans.whiskerRight m.toY point =
        source.commutes.inv ≫ (source.commutes.hom ≫
          Pseudofunctor.StrongTrans.whiskerRight m.toY point) := by
      rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    have key : Pseudofunctor.StrongTrans.whiskerRight m.toY point =
        (source.commutes.symm.trans (S1896RightUnitorIso source.toX)).hom ≫ m.toX ≫
          ((target.commutes.symm.trans (S1896RightUnitorIso target.toX)).inv) := by
      rw [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv]
      rw [h1, ← hcompat, hsq]
      simp only [Category.assoc]
      rfl
    exact key
  liftTwoCell_toY _ source target m :=
    S1896Modification_subsingleton T _ _
  twoCell_ext _ first second alpha beta hX hY :=
    S1896Modification_subsingleton T _ _

/-! ## 4. The representable open immersion of the identity -/

/-- **The identity base-change presentation.**  For every scheme-valued point of an
etale stack, the base change of the identity morphism along that point is the test
scheme itself, with the point as the comparison 1-cell and the full 2-pullback of
Section 3. -/
noncomputable def S1896IdentityBaseChange (Y : EtaleStackOverField F)
    (T : SchemeOverField F)
    (point : Pseudofunctor.StrongTrans (S1742YS (F := F) T) Y.fiber) :
    EtaleStackBaseChangePresentation
      (Pseudofunctor.StrongTrans.id Y.fiber) T point where
  pullbackScheme := T
  projection := 𝟙 T
  projectionMap := S1896IdentityProjectionMap T
  toSource := point
  commutes := S1896IdentityCommutes Y T point
  isPullback := S1896IdentityPullback Y T point

/-- **The identity morphism of an etale stack is representably an open immersion.**
This is a genuine inhabitant of the representable-open-immersion property: every base
change is the identity of the test scheme, which is an open immersion. -/
noncomputable def S1896IdentityOpenImmersion (Y : EtaleStackOverField F) :
    EtaleStackOpenImmersion (source := Y) (target := Y)
      (Pseudofunctor.StrongTrans.id Y.fiber) where
  baseChange T point := S1896IdentityBaseChange Y T point
  hasProperty T point := by
    show AlgebraicGeometry.IsOpenImmersion
      (S1896IdentityBaseChange Y T point).projection.left
    rw [show (S1896IdentityBaseChange Y T point).projection = 𝟙 T from rfl,
      Over.id_left]
    exact AlgebraicGeometry.IsOpenImmersion.of_isIso (𝟙 T.left)

/-! ## 5. The identity open map is never a boundary cusp -/

/-- The component of the identity strong transformation is essentially surjective
at every scheme. -/
theorem S1896Id_app_essSurj (Y : EtaleStackOverField F) (T : SchemeOverField F) :
    Functor.EssSurj
      ((Pseudofunctor.StrongTrans.id Y.fiber).app
        (LocallyDiscrete.mk (Opposite.op T))).toFunctor := by
  refine ⟨fun Z => ⟨Z, ⟨Iso.refl Z⟩⟩⟩

/-- **The identity open map can never be the open map of a boundary cusp.**  For any
candidate boundary point of the compactification, the boundary separation condition
fails: the boundary point is an object of the compactification fiber and the identity
map carries it to itself. -/
theorem S1896Id_not_boundary (X : HyperbolicOrbicurve F) (R : SchemeOverField F)
    (point : Pseudofunctor.StrongTrans (S1742YS (F := F) R) X.stack.fiber) :
    ¬ (∀ object : X.stack.fiber.obj (LocallyDiscrete.mk (Opposite.op R)),
        IsEmpty
          (((Pseudofunctor.StrongTrans.id X.stack.fiber).app
              (LocallyDiscrete.mk (Opposite.op R))).toFunctor.obj object ≅
            OrbicurveFiniteEtaleCover.pointObject R point)) := by
  intro h
  have hiso :
      ((Pseudofunctor.StrongTrans.id X.stack.fiber).app
          (LocallyDiscrete.mk (Opposite.op R))).toFunctor.obj
          (OrbicurveFiniteEtaleCover.pointObject R point) ≅
        OrbicurveFiniteEtaleCover.pointObject R point := by
    rw [show (Pseudofunctor.StrongTrans.id X.stack.fiber).app
        (LocallyDiscrete.mk (Opposite.op R)) = 𝟙 _ from rfl, Cat.Hom.id_toFunctor]
    exact Iso.refl _
  exact (h _).false hiso

/-- **A cusp's open map is not essentially surjective at its boundary residue
scheme.**  Hence the cusp's open immersion is genuinely non-surjective there and the
compactification genuinely gains the boundary point. -/
theorem S1896Cusp_openMap_app_not_essSurj {X : HyperbolicOrbicurve F}
    (C : OrbicurveBoundaryCusp X) :
    ¬ Functor.EssSurj
      (C.openMap.app (LocallyDiscrete.mk (Opposite.op C.residueScheme))).toFunctor := by
  intro h
  obtain ⟨object, he⟩ := h.mem_essImage
    (OrbicurveFiniteEtaleCover.pointObject C.residueScheme C.point)
  exact (C.isBoundary object).false he.some

/-! ## 6. The exact first missing datum of the D9 cusp -/

/-- The compactification/open-immersion part of a boundary cusp: a compactification
stack and a representably open immersion of the orbicurve into it. -/
abbrev S1896CuspOpenData (X : HyperbolicOrbicurve F) : Type 1 :=
  Sigma fun Z : EtaleStackOverField F =>
    Sigma fun m : X.stack.Hom Z => EtaleStackOpenImmersion m

/-- The boundary point datum over a compactification/open-immersion datum: a residue
scheme, a point of the compactification fiber, and the separation condition. -/
structure S1896CuspPointData {X : HyperbolicOrbicurve F} (D : S1896CuspOpenData X) where
  /-- The residue scheme of the boundary point. -/
  residueScheme : SchemeOverField F
  /-- The point of the compactification fiber. -/
  point : Pseudofunctor.StrongTrans
    (S1742YS (F := F) residueScheme) D.1.fiber
  /-- No point of the open orbicurve at the residue scheme is isomorphic to the
  boundary point. -/
  isBoundary : forall object :
      X.stack.fiber.obj (LocallyDiscrete.mk (Opposite.op residueScheme)),
      IsEmpty
        (((D.2.1).app
            (LocallyDiscrete.mk (Opposite.op residueScheme))).toFunctor.obj object ≅
          OrbicurveFiniteEtaleCover.pointObject residueScheme point)

/-- The compactification datum of a cusp. -/
def S1896CuspOpenDataOfCusp {X : HyperbolicOrbicurve F}
    (C : OrbicurveBoundaryCusp X) : S1896CuspOpenData X :=
  ⟨C.compactification, C.openMap, C.openImmersion⟩

/-- **The cusp is exactly its compactification/open-immersion datum plus its
boundary point datum.**  The first factor is the compactification stack with its
representable open immersion; the second is the boundary point. -/
noncomputable def S1896CuspEquivOpenData (X : HyperbolicOrbicurve F) :
    OrbicurveBoundaryCusp X ≃
      Sigma fun D : S1896CuspOpenData X => S1896CuspPointData D where
  toFun C :=
    ⟨S1896CuspOpenDataOfCusp C,
      { residueScheme := C.residueScheme
        point := C.point
        isBoundary := C.isBoundary }⟩
  invFun p :=
    { compactification := p.1.1
      openMap := p.1.2.1
      openImmersion := p.1.2.2
      residueScheme := p.2.residueScheme
      point := p.2.point
      isBoundary := p.2.isBoundary }
  left_inv C := by
    cases C
    rfl
  right_inv p := by
    rcases p with ⟨⟨Z, m, oi⟩, ⟨R, pt, hb⟩⟩
    rfl

/-- **Nonemptiness form of the decomposition**: a boundary cusp exists exactly when
a compactification stack with a representable open immersion and a boundary point
outside the image exists. -/
theorem S1896Cusp_nonempty_iff_openData (X : HyperbolicOrbicurve F) :
    Nonempty (OrbicurveBoundaryCusp X) ↔
      ∃ D : S1896CuspOpenData X, Nonempty (S1896CuspPointData D) :=
  ⟨fun ⟨C⟩ => ⟨S1896CuspOpenDataOfCusp C, ⟨(S1896CuspEquivOpenData X C).2⟩⟩,
    fun ⟨D, ⟨P⟩⟩ => ⟨(S1896CuspEquivOpenData X).symm ⟨D, P⟩⟩⟩

/-- **The exact first missing field of the D9 cusp over a D9 orbicurve slot.**  The
S1887 first missing datum is exactly: a compactification stack of the K-core
orbicurve, a representable open immersion into it, and a point that is not in the
image of the open orbicurve. -/
theorem S1896FirstMissing_structure (l : PrimeGeFive) (S : S1881D9OrbicurveSlot l) :
    Nonempty (S1887D9CuspFirstMissing l S) ↔
      ∃ D : S1896CuspOpenData S.cK, Nonempty (S1896CuspPointData D) :=
  S1896Cusp_nonempty_iff_openData S.cK

/-- **The identity open immersion does not fill the D9 cusp.**  The constructed
identity open immersion is representably open, but it can never satisfy the boundary
condition: at every candidate residue scheme and point it maps the boundary point
onto itself.  Hence the D9 cusp needs a compactification strictly extending the
K-core orbicurve, and that geometric input is not in the tree. -/
theorem S1896D9Cusp_identity_not_openImmersion (l : PrimeGeFive)
    (S : S1881D9OrbicurveSlot l) (R : SchemeOverField (S1732A l).K)
    (point : Pseudofunctor.StrongTrans
      (S1742YS (F := (S1732A l).K) R) S.cK.stack.fiber) :
    ¬ (∀ object : S.cK.stack.fiber.obj
          (LocallyDiscrete.mk (Opposite.op R)),
        IsEmpty
          (((Pseudofunctor.StrongTrans.id S.cK.stack.fiber).app
              (LocallyDiscrete.mk (Opposite.op R))).toFunctor.obj object ≅
            OrbicurveFiniteEtaleCover.pointObject R point)) :=
  S1896Id_not_boundary S.cK R point

/-! ## 7. Axiom footprint -/

#print axioms S1896WhiskerLeftIso
#print axioms S1896WhiskerRightIso
#print axioms S1896LeftUnitorIso
#print axioms S1896RightUnitorIso
#print axioms S1896WhiskerRightId
#print axioms S1896WhiskerExchange
#print axioms S1896WhiskerRightIff
#print axioms S1896Modification_subsingleton
#print axioms S1896App_one_eq_id
#print axioms S1896YonedaOneIso
#print axioms S1896YonedaOneIso_app_one
#print axioms S1896IdentityProjectionMap
#print axioms S1896IdentityCommutes
#print axioms S1896IdentitySquare
#print axioms S1896IdentityPullback
#print axioms S1896IdentityBaseChange
#print axioms S1896IdentityOpenImmersion
#print axioms S1896Id_app_essSurj
#print axioms S1896Id_not_boundary
#print axioms S1896Cusp_openMap_app_not_essSurj
#print axioms S1896CuspOpenDataOfCusp
#print axioms S1896CuspEquivOpenData
#print axioms S1896Cusp_nonempty_iff_openData
#print axioms S1896FirstMissing_structure
#print axioms S1896D9Cusp_identity_not_openImmersion

end LeanFormal.IUT.XiFPaper.S1896BoundaryCuspActual
