import tmp.sheaf.xif.paper.S1802BicategoricalYonedaActual
import tmp.sheaf.xif.paper.S1803AffineSectionsActual
import tmp.sheaf.xif.paper.S1780GeometricFiberFintypeActual
import tmp.sheaf.xif.paper.S1742TwoYonedaActual

/-!
# S1829: the S1802 bicategorical Yoneda coherence, and the fibre-covered gap

## What is unconditional

S1802 constructed the data `toObj`, `ofApp`, `ofNat` of the bicategorical
Yoneda comparison for a represented pseudofunctor `Y S` and an arbitrary
category-valued pseudofunctor `G`, and reduced the inverse direction to two
explicit coherence fields `IdCoherence` and `CompCoherence`.

This file proves both fields, componentwise at a section `P` of `S`, using
exactly the pseudofunctor coherence of `G` (`mapComp_id_right_hom`,
`mapComp_assoc_right_hom`) transported through the discrete/strict bookkeeping
of `Y S`.  It then assembles the inverse strong transformation `ofObjY` and
records its evaluation on the identity section.

## What is *not* obtained

The second S1780 gap `S1780FiberCovered cover = Function.Surjective
(S1780SectionToFiber cover)` is a *strict* statement about the object type of
the literal geometric fibre `CostructuredArrow (cover.map.app site).toFunctor
(pointObject)`.  The two-pullback universal property of the base-change square
gives a comparison *morphism* from a section image to every geometric-fibre
object (`S1829Section_covers_morphism`, unconditional), but not a strict
equality.  Since the source stack `cover.source` is an arbitrary etale stack
(its value at a scheme need not be a discrete category), a morphism in that
value category need not be an equality, and `Function.Surjective` cannot be
derived from the available data.  The exact additional input used below is the
discreteness of the source value at the actual base site, isolated as
`S1829FiberDiscrete`.  Under it the argument closes; without it the statement
remains the same gap as S1756/S1743 (the cover source is not known to be
representable by a scheme).

The strict object-level form of the gap is isolated as
`S1829StrictSectionCover`; `S1780FiberCovered_iff_strictSectionCover` proves
that it is *equivalent* to `S1780FiberCovered`.  The unconditional comparison
morphism is `S1829Section_covers_morphism`.  The theorems that conclude
`S1780FiberCovered`, `S1780FirstMissing` or `S1735GeometricFiberFintypeRequired`
are explicitly conditional on `S1829FiberDiscrete`; no unconditional form of
those three targets is claimed.  No `sorry` and no new axiom is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S1829FiberCoveredYonedaActual

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT.XiFPaper.S1802BicategoricalYonedaActual
open LeanFormal.IUT.XiFPaper.S1780GeometricFiberFintypeActual
open LeanFormal.IUT.XiFPaper.S1735GeometricFiberActual
open LeanFormal.IUT.XiFPaper.S1735GeometricFiberActual.Paper
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open Iut

universe u

variable {F : Type u} [Field F]
variable {S : Iut.SchemeOverField F}
variable (G : Iut.EtaleStackPseudofunctor F)

/-! ## 1. Discrete bookkeeping for the represented side -/

/-- In a locally discrete bicategory, a `map₂` of an equality 2-cell is the
corresponding `eqToHom` of the functor action. -/
lemma map₂_eqToHom {B : Type*} [Bicategory B] [Bicategory.IsLocallyDiscrete B]
    (H : B ⥤ᵖ Cat.{u, u}) {a b : B} {f g : a ⟶ b} (h : f = g) :
    H.map₂ (eqToHom h) = eqToHom (congrArg H.map h) := by
  cases h
  simp

/-- The action of `ofApp` on the (unique) morphisms of the discrete value
category of the represented pseudofunctor. -/
lemma ofApp_map (x : G.obj (site S)) (a : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ)
    {P Q : Discrete (Opposite.unop a.as ⟶ S)} (f : P ⟶ Q) :
    (ofApp G x a).toFunctor.map f =
      eqToHom (congrArg (fun R : Opposite.unop a.as ⟶ S =>
        (G.map (Quiver.Hom.toLoc R.op)).toFunctor.obj x) (Discrete.eq_of_hom f)) := by
  obtain ⟨⟨h⟩⟩ := f
  rfl

/-- Components of the right unitor of `Cat` are identities (the endpoints are
definitionally equal because `Cat` is a strict bicategory). -/
lemma cat_rightUnitor_inv_app_eq_id {C D : Cat.{u, u}} (F : C ⟶ D) (X : C) :
    (ρ_ F).inv.toNatTrans.app X = 𝟙 _ := by
  rw [CategoryTheory.Cat.rightUnitor_inv_app]
  exact eqToHom_refl _ _

/-- Components of the left unitor of `Cat` are identities. -/
lemma cat_leftUnitor_hom_app_eq_id {C D : Cat.{u, u}} (F : C ⟶ D) (X : C) :
    (λ_ F).hom.toNatTrans.app X = 𝟙 _ := by
  rw [CategoryTheory.Cat.leftUnitor_hom_app]
  exact eqToHom_refl _ _

/-! ## 2. The two S1802 coherence fields -/

/-- The unitality coherence of the candidate inverse strong transformation. -/
theorem idCoherence (x : G.obj (site S)) : IdCoherence G x := by
  intro a
  apply CategoryTheory.Cat.Hom₂.ext
  apply CategoryTheory.NatTrans.ext
  funext P
  obtain ⟨P⟩ := P
  simp only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerLeft_app,
    CategoryTheory.Cat.whiskerRight_app, CategoryTheory.Cat.leftUnitor_hom_app,
    CategoryTheory.Cat.rightUnitor_inv_app, CategoryTheory.Cat.rightUnitor_hom_app,
    CategoryTheory.Cat.leftUnitor_inv_app, CategoryTheory.Cat.eqToHom_app,
    CategoryTheory.Cat.Hom₂.eqToHom_toNatTrans, ofNat_hom_app]
  rw [ofApp_map]
  dsimp only [CategoryTheory.Cat.Hom.toNatIso]
  rw [G.mapComp_id_right_hom]
  have hρ : (ρ_ (Quiver.Hom.toLoc P.op)).hom =
      eqToHom (LocallyDiscrete.eq_of_hom (ρ_ (Quiver.Hom.toLoc P.op)).hom) :=
    Subsingleton.elim _ _
  rw [hρ, map₂_eqToHom]
  simp only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerLeft_app,
    CategoryTheory.Cat.whiskerRight_app, CategoryTheory.Cat.eqToHom_app,
    CategoryTheory.Cat.Hom₂.eqToHom_toNatTrans, eqToHom_refl, Category.id_comp,
    Category.comp_id, CategoryTheory.Cat.Hom.inv_hom_id_toNatTrans_app]
  simp only [cat_rightUnitor_inv_app_eq_id, Category.id_comp, ofApp_obj,
    CategoryTheory.Cat.Hom.inv_hom_id_toNatTrans_app]
  erw [Category.id_comp]
  erw [CategoryTheory.Cat.Hom.inv_hom_id_toNatTrans_app]
  rfl

/-- The associativity coherence of the candidate inverse strong transformation. -/
theorem compCoherence (x : G.obj (site S)) : CompCoherence G x := by
  intro a b c f g
  apply CategoryTheory.Cat.Hom₂.ext
  apply CategoryTheory.NatTrans.ext
  funext P
  obtain ⟨P⟩ := P
  simp only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerLeft_app,
    CategoryTheory.Cat.whiskerRight_app, CategoryTheory.Cat.leftUnitor_hom_app,
    CategoryTheory.Cat.rightUnitor_inv_app, CategoryTheory.Cat.rightUnitor_hom_app,
    CategoryTheory.Cat.leftUnitor_inv_app, CategoryTheory.Cat.associator_hom_app,
    CategoryTheory.Cat.associator_inv_app, CategoryTheory.Cat.eqToHom_app,
    CategoryTheory.Cat.Hom₂.eqToHom_toNatTrans, ofNat_hom_app]
  rw [ofApp_map]
  dsimp only [CategoryTheory.Cat.Hom.toNatIso]
  have hL : (G.mapComp (Quiver.Hom.toLoc P.op) (f ≫ g)).hom.toNatTrans.app x ≫
      (G.mapComp f g).hom.toNatTrans.app ((ofApp G x a).toFunctor.obj (Discrete.mk P)) =
      ((G.mapComp (Quiver.Hom.toLoc P.op) (f ≫ g)).hom ≫
        G.map (Quiver.Hom.toLoc P.op) ◁ (G.mapComp f g).hom).toNatTrans.app x := by
    rw [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerLeft_app]
    rfl
  rw [hL]
  rw [G.mapComp_assoc_right_hom (Quiver.Hom.toLoc P.op) f g]
  have hα : (α_ (Quiver.Hom.toLoc P.op) f g).inv =
      eqToHom (LocallyDiscrete.eq_of_hom (α_ (Quiver.Hom.toLoc P.op) f g).inv) :=
    Subsingleton.elim _ _
  rw [hα, map₂_eqToHom]
  simp only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerLeft_app,
    CategoryTheory.Cat.whiskerRight_app, CategoryTheory.Cat.eqToHom_app,
    CategoryTheory.Cat.Hom₂.eqToHom_toNatTrans, eqToHom_refl, Category.id_comp,
    Category.comp_id, CategoryTheory.Cat.associator_hom_app,
    CategoryTheory.Cat.associator_inv_app, CategoryTheory.Cat.leftUnitor_hom_app,
    CategoryTheory.Cat.rightUnitor_inv_app]
  erw [Category.id_comp]
  rfl

/-! ## 3. The inverse Yoneda direction -/

/-- The inverse direction of the bicategorical Yoneda comparison: an object
`x` of `G` at the representing object gives a strong transformation
`Y S ⟶ G`, with no remaining coherence obligations. -/
noncomputable def ofObjY (x : G.obj (site S)) :
    Pseudofunctor.StrongTrans (Y S) G :=
  ofObj G x (idCoherence G x) (compCoherence G x)

/-- The app components of `ofObjY` are `ofApp`. -/
@[simp] lemma ofObjY_app (x : G.obj (site S))
    (a : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) :
    (ofObjY G x).app a = ofApp G x a := rfl

/-- The strong naturality 2-isomorphisms of `ofObjY` are `ofNat`. -/
@[simp] lemma ofObjY_naturality (x : G.obj (site S))
    {a b : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ} (h : a ⟶ b) :
    (ofObjY G x).naturality h = ofNat G x h := rfl

/-- Evaluation of `ofObjY` at the identity section. -/
lemma toObj_ofObjY (x : G.obj (site S)) :
    toObj G (ofObjY G x) =
      (G.map (Quiver.Hom.toLoc (𝟙 S).op)).toFunctor.obj x := rfl

/-- The object-side round trip: the inverse Yoneda direction sends `x` to a
transformation whose evaluation is isomorphic to `x`, via `G.mapId`. -/
theorem toObj_ofObjY_iso (x : G.obj (site S)) :
    Nonempty (toObj G (ofObjY G x) ≅ x) := by
  rw [toObj_ofObjY]
  exact ⟨(Cat.Hom.toNatIso (G.mapId (site S))).app x⟩

/-- The packaged Yoneda comparison: the forward direction and the inverse
direction are inverse on objects up to the pseudofunctor unitality isomorphism,
and the inverse direction satisfies both strong-transformation coherence
fields. -/
theorem yonedaComparison_summary :
    (∀ eta : Pseudofunctor.StrongTrans (Y S) G,
        toObj G eta = (eta.app (site S)).toFunctor.obj (Discrete.mk (𝟙 S))) ∧
      (∀ x : G.obj (site S), Nonempty (toObj G (ofObjY G x) ≅ x)) :=
  ⟨toObj_def G, toObj_ofObjY_iso G⟩


/-! ## 4. The two-pullback comparison at the actual point (0,0)

The rest of the file uses the inverse Yoneda direction of section 3 to compare
the literal geometric fibre at the actual point with the scheme sections of the
base-change model.  The only step that is not supplied by the two-pullback
universal property is the passage from a comparison *morphism* in the source
stack value to an *equality* of objects; that is isolated as
`S1829FiberDiscrete`.
-/

section FiberComparison

variable (cover : S1735Cover)

/-- The represented pseudofunctor of the actual base scheme. -/
noncomputable abbrev S1829BaseStack : EtaleStackPseudofunctor S1735K :=
  schemeRepresentableEtalePseudofunctor S1735K S1735BaseScheme

/-- The base-change presentation at the actual point (0,0). -/
noncomputable abbrev S1829BaseChange :
    EtaleStackBaseChangePresentation cover.map S1735BaseScheme S1735BasePoint :=
  S1780BaseChange cover

/-- The square of the actual-point base change. -/
noncomputable abbrev S1829Square : EtalePseudofunctorSquare
    (schemeRepresentableEtalePseudofunctor S1735K (S1780Model cover))
    cover.source.fiber
    (schemeRepresentableEtalePseudofunctor S1735K S1735BaseScheme)
    S1735Orbicurve.stack.fiber :=
  EtalePseudofunctorSquare.mk (S1780BaseChange cover).toSource
    (S1780BaseChange cover).projectionMap.transformation cover.map S1735BasePoint
    (S1780BaseChange cover).commutes

/-- The inverse Yoneda transformation attached to a geometric-fibre object. -/
noncomputable def S1829Sigma (x : S1735Fiber cover) :
    Pseudofunctor.StrongTrans S1829BaseStack cover.source.fiber :=
  ofObjY (G := cover.source.fiber) x.left

/-- The first leg to the represented target. -/
noncomputable def S1829Eta1 (x : S1735Fiber cover) :
    Pseudofunctor.StrongTrans S1829BaseStack S1735Orbicurve.stack.fiber :=
  Pseudofunctor.StrongTrans.vcomp (S1829Sigma cover x) cover.map

/-- The second leg to the represented target. -/
noncomputable def S1829Eta2 (x : S1735Fiber cover) :
    Pseudofunctor.StrongTrans S1829BaseStack S1735Orbicurve.stack.fiber :=
  Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.id S1829BaseStack)
    S1735BasePoint

/-- The two evaluations at the identity section coincide, because the target is
the represented stack and the geometric-fibre morphism is a morphism in a
discrete category. -/
theorem S1829Hom_eq (x : S1735Fiber cover) :
    S1742HomOfStrongTrans (S1829Eta1 cover x) =
      S1742HomOfStrongTrans (S1829Eta2 cover x) := by
  dsimp [S1829Eta1, S1829Eta2, S1829Sigma, S1742HomOfStrongTrans]
  have hmor : (cover.map.app S1780Site).toFunctor.obj
        ((cover.source.fiber.map (𝟙 S1780Site)).toFunctor.obj (x.left)) =
      S1780PointObject := by
    let mId : (cover.source.fiber.map (𝟙 S1780Site)).toFunctor.obj (x.left) ⟶
        x.left :=
      (cover.source.fiber.mapId S1780Site).hom.toNatTrans.app (x.left)
    let m : (cover.map.app S1780Site).toFunctor.obj
          ((cover.source.fiber.map (𝟙 S1780Site)).toFunctor.obj (x.left)) ⟶
        S1780PointObject :=
      (cover.map.app S1780Site).toFunctor.map mId ≫ x.hom
    haveI : IsDiscrete ((S1735Orbicurve.stack.fiber).obj S1780Site) := by
      change IsDiscrete (Discrete (S1735BaseScheme ⟶ S1726AffineOver))
      infer_instance
    exact IsDiscrete.eq_of_hom m
  change ((cover.map.app S1780Site).toFunctor.obj
        ((cover.source.fiber.map (𝟙 S1780Site)).toFunctor.obj (x.left))).as =
      S1780PointObject.as
  exact congrArg (fun Z => Z.as) hmor

/-- The 2-isomorphism comparing the two legs of the cone. -/
noncomputable def S1829ConeCommutes (x : S1735Fiber cover) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S1829Sigma cover x) cover.map)
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.id S1829BaseStack) S1735BasePoint) :=
  (S1742StrongTransIsoOfHom (S1829Eta1 cover x)).symm ≪≫
    eqToIso (congrArg S1742StrongTransOfHom (S1829Hom_eq cover x)) ≪≫
      S1742StrongTransIsoOfHom (S1829Eta2 cover x)

/-- The cone from the represented base to the actual-point base-change square. -/
noncomputable def S1829Cone (x : S1735Fiber cover) :
    EtalePseudofunctorSquare.Cone (S1829Square cover) S1829BaseStack :=
  { toX := S1829Sigma cover x
    toY := Pseudofunctor.StrongTrans.id S1829BaseStack
    commutes := S1829ConeCommutes cover x }

/-- The lift of the cone through the two-pullback universal property. -/
noncomputable def S1829Lift (x : S1735Fiber cover) :
    Pseudofunctor.StrongTrans S1829BaseStack
      (schemeRepresentableEtalePseudofunctor S1735K (S1780Model cover)) :=
  (S1780BaseChange cover).isPullback.lift S1829BaseStack (S1829Cone cover x)

/-- The scheme section attached to a geometric-fibre object. -/
noncomputable def S1829Section (x : S1735Fiber cover) :
    S1735BaseScheme ⟶ S1780Model cover :=
  S1742HomOfStrongTrans (S1829Lift cover x)

/-- The lift returns the identity section at the representing object. -/
theorem S1829Lift_app_id (x : S1735Fiber cover) :
    ((S1829Lift cover x).app S1780Site).toFunctor.obj
        (Discrete.mk (𝟙 S1735BaseScheme)) =
      Discrete.mk (S1829Section cover x) := by
  apply Discrete.ext
  rw [S1742Key (S1829Lift cover x) S1780Site (𝟙 S1735BaseScheme)]
  exact Category.id_comp _

/-- The comparison morphism in the source stack value, from the section object to
the given geometric-fibre object.  It is built from the unit of the pullback
comparison and the pseudofunctor unitality of the cover source. -/
noncomputable def S1829SectionMorphism (x : S1735Fiber cover) :
    ((S1780BaseChange cover).toSource.app S1780Site).toFunctor.obj
        (Discrete.mk (S1829Section cover x)) ⟶ x.left := by
  let e := (S1780BaseChange cover).isPullback.liftToX S1829BaseStack
    (S1829Cone cover x)
  let m1 : ((Pseudofunctor.StrongTrans.vcomp (S1829Lift cover x)
        (S1780BaseChange cover).toSource).app S1780Site).toFunctor.obj
        (Discrete.mk (𝟙 S1735BaseScheme)) ⟶
      ((S1829Sigma cover x).app S1780Site).toFunctor.obj
        (Discrete.mk (𝟙 S1735BaseScheme)) :=
    (e.hom.as.app S1780Site).toNatTrans.app (Discrete.mk (𝟙 S1735BaseScheme))
  let m2 : ((S1829Sigma cover x).app S1780Site).toFunctor.obj
        (Discrete.mk (𝟙 S1735BaseScheme)) ⟶ x.left :=
    (cover.source.fiber.mapId S1780Site).hom.toNatTrans.app (x.left)
  exact m1 ≫ m2

/-- Unconditional comparison: every geometric-fibre object receives a morphism
from a section image.  This is the essential-surjectivity content of the
two-pullback universal property, before any strictness assumption. -/
theorem S1829Section_covers_morphism (x : S1735Fiber cover) :
    ∃ s : S1735BaseScheme ⟶ S1780Model cover,
      Nonempty (S1780SectionToFiber cover s ⟶ x) := by
  haveI : IsDiscrete ((S1735Orbicurve.stack.fiber).obj S1780Site) := by
    change IsDiscrete (Discrete (S1735BaseScheme ⟶ S1726AffineOver))
    infer_instance
  exact ⟨S1829Section cover x,
    ⟨CostructuredArrow.homMk (S1829SectionMorphism cover x)
      (Subsingleton.elim _ _)⟩⟩



/-- Under discreteness of the source stack value, the section attached to a
geometric-fibre object strictly recovers its underlying object. -/
theorem S1829Section_source_eq (x : S1735Fiber cover)
    [IsDiscrete ((cover.source.fiber).obj S1780Site)] :
    ((S1780BaseChange cover).toSource.app S1780Site).toFunctor.obj
        (Discrete.mk (S1829Section cover x)) = x.left :=
  IsDiscrete.eq_of_hom (S1829SectionMorphism cover x)

/-- Two costructured arrows with equal left objects into a discrete target are
equal. -/
lemma S1829CostructuredArrow_eq_of_left_eq {C D : Type*} [Category C] [Category D]
    [IsDiscrete D] {F : C ⥤ D} {T : D} {X Y : CostructuredArrow F T}
    (h : X.left = Y.left) : X = Y := by
  cases X with
  | mk xl xr xh =>
  cases Y with
  | mk yl yr yh =>
  subst h
  have hr : xr = yr := Subsingleton.elim _ _
  have hh : xh = yh := Subsingleton.elim _ _
  subst hr
  subst hh
  rfl

/-- The exact object-level strict coverage statement: every geometric-fibre
object is literally the image of a section of the base-change model. -/
def S1829StrictSectionCover (cover : S1735Cover) : Prop :=
  ∀ x : S1735Fiber cover,
    ∃ s : S1735BaseScheme ⟶ S1780Model cover,
      ((S1780BaseChange cover).toSource.app S1780Site).toFunctor.obj
        (Discrete.mk s) = x.left

/-- (`S1780FiberCovered cover`) is equivalent to strict object-level coverage;
the second components live in the discrete represented target and cause no
further obstruction. -/
theorem S1780FiberCovered_iff_strictSectionCover (cover : S1735Cover) :
    S1780FiberCovered cover ↔ S1829StrictSectionCover cover := by
  constructor
  · intro h x
    obtain ⟨s, hs⟩ := h x
    exact ⟨s, by
      have hleft := congrArg CostructuredArrow.left hs
      simpa [S1780SectionToFiber, S1780SectionStackObject] using hleft⟩
  · intro h x
    obtain ⟨s, hs⟩ := h x
    haveI : IsDiscrete ((S1735Orbicurve.stack.fiber).obj S1780Site) := by
      change IsDiscrete (Discrete (S1735BaseScheme ⟶ S1726AffineOver))
      infer_instance
    exact ⟨s, S1829CostructuredArrow_eq_of_left_eq hs⟩

/-- The strict object-level coverage follows from discreteness of the source
value. -/
theorem S1829StrictSectionCover_of_fiberDiscrete (cover : S1735Cover)
    [IsDiscrete ((cover.source.fiber).obj S1780Site)] :
    S1829StrictSectionCover cover :=
  fun x => ⟨S1829Section cover x, S1829Section_source_eq cover x⟩


/-- A costructured-arrow category into a discrete target over a discrete source
is discrete. -/
instance S1829IsDiscreteCostructuredArrow {C D : Type*} [Category C] [Category D]
    [IsDiscrete C] [IsDiscrete D] (F : C ⥤ D) (T : D) :
    IsDiscrete (CostructuredArrow F T) where
  subsingleton X Y := ⟨fun f g => by
    apply CostructuredArrow.hom_ext
    exact Subsingleton.elim _ _⟩
  eq_of_hom {X Y} f := by
    cases X with
    | mk xl xr xh =>
    cases Y with
    | mk yl yr yh =>
    have h : xl = yl := IsDiscrete.eq_of_hom f.left
    subst h
    have hr : xr = yr := Subsingleton.elim _ _
    have hh : xh = yh := Subsingleton.elim _ _
    subst hr
    subst hh
    rfl

/-- **The second S1780 gap under source discreteness.**  If the source stack
value at the actual base site is a discrete category, the section map is
strictly surjective on objects. -/
theorem S1829FiberCovered_of_isDiscrete (cover : S1735Cover)
    [IsDiscrete ((cover.source.fiber).obj S1780Site)] :
    S1780FiberCovered cover := by
  intro x
  refine ⟨S1829Section cover x, ?_⟩
  haveI : IsDiscrete ((S1735Orbicurve.stack.fiber).obj S1780Site) := by
    change IsDiscrete (Discrete (S1735BaseScheme ⟶ S1726AffineOver))
    infer_instance
  haveI : IsDiscrete (S1735Fiber cover) :=
    S1829IsDiscreteCostructuredArrow (cover.map.app S1780Site).toFunctor
      S1780PointObject
  apply IsDiscrete.eq_of_hom
  refine CostructuredArrow.homMk (S1829SectionMorphism cover x) ?_
  exact Subsingleton.elim _ _

/-- The exact remaining input, isolated as a proposition.  It is the strict
counterpart of S1756/S1743: each cover source must have a discrete value at the
actual base scheme.  It would follow if the source were literally the
representable pseudofunctor of a scheme (not merely quasi-equivalent to one),
but this is not available from the finite-etale base-change data alone. -/
def S1829FiberDiscrete : Prop :=
  ∀ cover : S1735Cover, IsDiscrete ((cover.source.fiber).obj S1780Site)

/-- Under `S1829FiberDiscrete`, the second S1780 gap holds for every cover. -/
theorem S1780FiberCovered_of_fiberDiscrete (h : S1829FiberDiscrete)
    (cover : S1735Cover) : S1780FiberCovered cover :=
  @S1829FiberCovered_of_isDiscrete cover (h cover)

/-- Under `S1829FiberDiscrete`, the packaged S1780 first missing input holds;
the section-finiteness half is the unconditional S1803 theorem. -/
theorem S1780FirstMissing_of_fiberDiscrete (h : S1829FiberDiscrete) :
    S1780FirstMissing :=
  ⟨fun cover =>
      LeanFormal.IUT.XiFPaper.S1803AffineSectionsActual.S1803_sectionFintype cover,
    fun cover => S1780FiberCovered_of_fiberDiscrete h cover⟩

/-- Under `S1829FiberDiscrete`, the S1735 geometric-fibre finiteness
requirement follows from the S1780 reduction. -/
theorem S1735GeometricFiberFintypeRequired_of_fiberDiscrete
    (h : S1829FiberDiscrete) : S1735GeometricFiberFintypeRequired :=
  S1780FintypeRequired_of_firstMissing (S1780FirstMissing_of_fiberDiscrete h)

end FiberComparison

/-! ## 5. Axiom footprint -/

#print axioms idCoherence
#print axioms compCoherence
#print axioms ofObjY
#print axioms toObj_ofObjY_iso
#print axioms yonedaComparison_summary
#print axioms S1829Hom_eq
#print axioms S1829Section_covers_morphism
#print axioms S1829Section_source_eq
#print axioms S1829StrictSectionCover_of_fiberDiscrete
#print axioms S1829CostructuredArrow_eq_of_left_eq
#print axioms S1780FiberCovered_iff_strictSectionCover
#print axioms S1829FiberCovered_of_isDiscrete
#print axioms S1780FiberCovered_of_fiberDiscrete
#print axioms S1780FirstMissing_of_fiberDiscrete
#print axioms S1735GeometricFiberFintypeRequired_of_fiberDiscrete

end LeanFormal.IUT.XiFPaper.S1829FiberCoveredYonedaActual