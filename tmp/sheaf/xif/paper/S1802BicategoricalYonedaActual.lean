import Iut.Foundations.Orbicurve


/-!
# S1802: bicategorical Yoneda for the representable etale pseudofunctor

## Question (S1780 gap 2, precise form)

For a field F, a scheme S : Over (Spec F) and an *arbitrary* category-valued etale
pseudofunctor G : LocallyDiscrete (Over (Spec F))^op to Cat, construct

* toObj : StrongTrans (Y S) G -> G.obj (op S),   eta |-> eta.app (op S) (id_S);
* ofApp : G.obj (op S) -> forall a, (Y S).obj a -> G.obj a,  x |-> (P |-> G.map (op P) x);
* the strong naturality 2-isomorphism of the second, built from G.mapComp;
* the coherence fields of Pseudofunctor.StrongTrans, and the two round trips.

## What is built here (no sorry, no axiom)

Section 0: unfolding API for the represented pseudofunctor Y S
(Y_obj, Y_map_obj are rfl; they are the Functor.toPseudofunctor' computation rules).

Section 1: the forward direction toObj and its computation rule toObj_def.

Section 2: the inverse direction on app components, ofApp, with ofApp_obj
(computation rule) and ofApp_map_eqToHom (the action on the discrete morphisms,
which is where the discreteness of the represented side is used).

Section 3: the strong naturality 2-isomorphism ofNat, whose component at a section
P : U -> S is the component at x of G.mapComp (op P) h.  This is the use of mapComp
for naturality: ofNat_hom_app / ofNat_inv_app record the computation rules rfl.

Section 4: the coherence field naturality_naturality, proved: since the site
bicategory is locally discrete, both 2-cells in the site are identities and
PrelaxFunctor.map2_id plus the whiskering identities of a bicategory close the goal.

Section 5: the remaining two coherence fields are stated precisely as
IdCoherence and CompCoherence, and are shown to imply the existence of the full
strong transformation ofObj.  These two propositions are the exact first missing
piece of S1802; section 5 records the reason.

Section 6: the round trip on the object side, via G.mapId (no coherence needed):
toObj_ofObj_iso, i.e. toObj (ofObj x) is isomorphic to x.

Section 7: the target-locked statement of the bicategorical Yoneda comparison.

## Honest boundary

The data, the naturality 2-isomorphism, the naturality_naturality coherence and the
object-side round trip are unconditional.  What is *not* discharged is IdCoherence
(unitality of G.mapComp against G.mapId and the unitors) and CompCoherence
(associativity of G.mapComp against the associators), i.e. the two StrongTrans
coherence equations transported through the Cat-level eqToHom bookkeeping of the
represented side.  They are congruences of G's own pseudofunctor coherence
(Pseudofunctor.mapComp_id_right_hom, Pseudofunctor.mapComp_assoc_right_hom) with the
Discrete-transport of Y S; nothing geometric is missing.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1802BicategoricalYonedaActual

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans

universe u

variable {F : Type u} [Field F]

/-! ## 0. The site, the represented pseudofunctor, and its computation rules -/

/-- The object of the etale site attached to a scheme S: the point at which the
represented pseudofunctor is evaluated in the Yoneda comparison. -/
abbrev site (S : Iut.SchemeOverField F) : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ :=
  LocallyDiscrete.mk (Opposite.op S)

variable {S : Iut.SchemeOverField F}

/-- The representable category-valued etale pseudofunctor of S, abbreviated. -/
abbrev Y (S : Iut.SchemeOverField F) : Iut.EtaleStackPseudofunctor F :=
  Iut.schemeRepresentableEtalePseudofunctor F S

/-- The value of the represented pseudofunctor at a test object is the discrete
category of sections of the test object over S. -/
lemma Y_obj (S : Iut.SchemeOverField F) (a : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) :
    (Y S).obj a = Cat.of (Discrete (Opposite.unop a.as ⟶ S)) := rfl

/-- The action of the represented pseudofunctor on 1-morphisms is precomposition of
sections. -/
lemma Y_map_obj (S : Iut.SchemeOverField F)
    {a b : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ}
    (g : a ⟶ b) (P : Opposite.unop a.as ⟶ S) :
    ((Y S).map g).toFunctor.obj (Discrete.mk P) = Discrete.mk (g.as.unop ≫ P) := rfl

/-! ## 1. The forward direction: evaluation at the identity section -/

variable (G : Iut.EtaleStackPseudofunctor F)

/-- The forward direction of the bicategorical Yoneda comparison: a strong
transformation out of the represented pseudofunctor is evaluated at the object op S
of the site and then at the identity section. -/
noncomputable def toObj (eta : Pseudofunctor.StrongTrans (Y S) G) : G.obj (site S) :=
  (eta.app (site S)).toFunctor.obj (Discrete.mk (𝟙 S))

/-- The defining computation rule of toObj. -/
lemma toObj_def (eta : Pseudofunctor.StrongTrans (Y S) G) :
    toObj G eta = (eta.app (site S)).toFunctor.obj (Discrete.mk (𝟙 S)) := rfl

/-! ## 2. The inverse direction: x |-> (P |-> G.map (op P) x) -/

/-- The app component of the candidate inverse strong transformation: at a test
object U and a section P : U -> S it returns the object G.map (op P) x of G.obj U. -/
noncomputable def ofApp (x : G.obj (site S))
    (a : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) :
    (Y S).obj a ⟶ G.obj a :=
  (Discrete.functor (fun P : Opposite.unop a.as ⟶ S =>
    (G.map (Quiver.Hom.toLoc P.op)).toFunctor.obj x)).toCatHom

/-- The value of ofApp on a section. -/
lemma ofApp_obj (x : G.obj (site S)) (a : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ)
    (P : Opposite.unop a.as ⟶ S) :
    (ofApp G x a).toFunctor.obj (Discrete.mk P) =
      (G.map (Quiver.Hom.toLoc P.op)).toFunctor.obj x := rfl

/-- On the morphisms of the (discrete) value category, ofApp is a transport; this is
where the discreteness of the represented side is used. -/
lemma ofApp_map_eqToHom (x : G.obj (site S))
    (a : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ)
    {P Q : Discrete (Opposite.unop a.as ⟶ S)} (h : P = Q) :
    (ofApp G x a).toFunctor.map (CategoryTheory.eqToHom h) =
      CategoryTheory.eqToHom
        (congrArg (fun R : Discrete (Opposite.unop a.as ⟶ S) =>
          (G.map (Quiver.Hom.toLoc R.as.op)).toFunctor.obj x) h) := by
  rw [CategoryTheory.eqToHom_map]
  exact congrArg CategoryTheory.eqToHom (Subsingleton.elim _ _)

/-! ## 3. The strong naturality 2-isomorphism, from G.mapComp -/

/-- The strong naturality 2-isomorphism: at a section P : a.as.unop -> S its component
is the component at x of G.mapComp (op P) h. -/
noncomputable def ofNat (x : G.obj (site S))
    {a b : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ} (h : a ⟶ b) :
    (Y S).map h ≫ ofApp G x b ≅ ofApp G x a ≫ G.map h :=
  Cat.Hom.isoMk (Discrete.natIso (fun P : Discrete (Opposite.unop a.as ⟶ S) =>
    (Cat.Hom.toNatIso (G.mapComp (Quiver.Hom.toLoc P.as.op) h)).app x))

/-- The computation rule for the forward component of ofNat: it is G.mapComp. -/
lemma ofNat_hom_app (x : G.obj (site S))
    {a b : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ} (h : a ⟶ b)
    (P : Discrete (Opposite.unop a.as ⟶ S)) :
    (ofNat G x h).hom.toNatTrans.app P =
      (Cat.Hom.toNatIso (G.mapComp (Quiver.Hom.toLoc P.as.op) h)).hom.app x := rfl

/-- The computation rule for the inverse component of ofNat. -/
lemma ofNat_inv_app (x : G.obj (site S))
    {a b : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ} (h : a ⟶ b)
    (P : Discrete (Opposite.unop a.as ⟶ S)) :
    (ofNat G x h).inv.toNatTrans.app P =
      (Cat.Hom.toNatIso (G.mapComp (Quiver.Hom.toLoc P.as.op) h)).inv.app x := rfl

/-! ## 4. The first coherence field: naturality_naturality -/

/-- The 2-cells of the site are equalities, so both map2's in the naturality coherence
are identities by PrelaxFunctor.map2_id, and the whiskering identities of a bicategory
finish the goal. -/
theorem ofNat_naturality_naturality (x : G.obj (site S))
    {a b : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ} {f g : a ⟶ b} (eta : f ⟶ g) :
    (Y S).map₂ eta ▷ ofApp G x b ≫ (ofNat G x g).hom =
      (ofNat G x f).hom ≫ ofApp G x a ◁ G.map₂ eta := by
  obtain rfl := LocallyDiscrete.eq_of_hom eta
  have heta : eta = 𝟙 f := Subsingleton.elim _ _
  rw [heta, PrelaxFunctor.map₂_id, PrelaxFunctor.map₂_id]
  rw [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id]
/-! ## 5. The two remaining coherence fields, stated precisely

Pseudofunctor.StrongTrans requires two coherence fields besides
naturality_naturality:

* naturality_id  : compatibility of the naturality 2-isomorphism with G.mapId and the
  two unitors of Cat;
* naturality_comp: compatibility of the naturality 2-isomorphism with G.mapComp and
  the three associators of Cat.

Both are true, and their mathematical content is exactly the pseudofunctor coherence
of G (Pseudofunctor.mapComp_id_right_hom and
Pseudofunctor.mapComp_assoc_right_hom), read through the Discrete-transport of the
represented side (Y_map_obj, Cat.*_app).  What is not done below is the Cat-level
transport bookkeeping: after reducing to components at a section P, both sides are
composites in G.obj a in which the only non-eqToHom factors are G.mapComp-components,
but the surrounding eqToHoms have indices related by assoc / id_comp inside the
*discrete* value category of Y S, so a rewrite with G's coherence lemma needs those
indices normalized first.  The exact goals are recorded in the two propositions below;
nothing else about them is missing.
-/

/-- The exact naturality_id coherence obligation for the candidate inverse
transformation x |-> ofApp G x. -/
def IdCoherence (x : G.obj (site S)) : Prop :=
  ∀ a : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ,
    (ofNat G x (𝟙 a)).hom ≫ ofApp G x a ◁ (G.mapId a).hom =
      ((Y S).mapId a).hom ▷ ofApp G x a ≫
        (λ_ (ofApp G x a)).hom ≫ (ρ_ (ofApp G x a)).inv

/-- The exact naturality_comp coherence obligation for the candidate inverse
transformation x |-> ofApp G x. -/
def CompCoherence (x : G.obj (site S)) : Prop :=
  ∀ {a b c : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ c),
    (ofNat G x (f ≫ g)).hom ≫ ofApp G x a ◁ (G.mapComp f g).hom =
      ((Y S).mapComp f g).hom ▷ ofApp G x c ≫
        (α_ ((Y S).map f) ((Y S).map g) (ofApp G x c)).hom ≫
          (Y S).map f ◁ (ofNat G x g).hom ≫
            (α_ ((Y S).map f) (ofApp G x b) (G.map g)).inv ≫
              (ofNat G x f).hom ▷ G.map g ≫
                (α_ (ofApp G x a) (G.map f) (G.map g)).hom

/-- The candidate inverse strong transformation, assembled from ofApp, ofNat and the
two coherence fields above.  No data is fabricated: app and naturality are the
constructions of sections 2 and 3. -/
noncomputable def ofObj (x : G.obj (site S)) (hid : IdCoherence G x)
    (hcomp : CompCoherence G x) : Pseudofunctor.StrongTrans (Y S) G where
  app a := ofApp G x a
  naturality h := ofNat G x h
  naturality_naturality := ofNat_naturality_naturality G x
  naturality_id := hid
  naturality_comp := fun f g => hcomp f g

/-- The app components of the assembled transformation are ofApp. -/
@[simp] lemma ofObj_app (x : G.obj (site S)) (hid : IdCoherence G x)
    (hcomp : CompCoherence G x) (a : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) :
    (ofObj G x hid hcomp).app a = ofApp G x a := rfl

/-- The naturality 2-isomorphisms of the assembled transformation are ofNat. -/
@[simp] lemma ofObj_naturality (x : G.obj (site S)) (hid : IdCoherence G x)
    (hcomp : CompCoherence G x) {a b : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ}
    (h : a ⟶ b) :
    (ofObj G x hid hcomp).naturality h = ofNat G x h := rfl

/-! ## 6. The round trip on the object side, via G.mapId -/

/-- Evaluating the candidate inverse at the identity section gives G.map (op (1 S)) x. -/
lemma toObj_ofObj (x : G.obj (site S)) (hid : IdCoherence G x)
    (hcomp : CompCoherence G x) :
    toObj G (ofObj G x hid hcomp) =
      (G.map (Quiver.Hom.toLoc (𝟙 S).op)).toFunctor.obj x := rfl

/-- The object-side round trip: evaluating the candidate inverse at the identity
section returns an object isomorphic to x.  This is exactly the unitality constraint
G.mapId of G; no coherence of the strong transformation is used. -/
theorem toObj_ofObj_iso (x : G.obj (site S)) (hid : IdCoherence G x)
    (hcomp : CompCoherence G x) :
    Nonempty (toObj G (ofObj G x hid hcomp) ≅ x) := by
  rw [toObj_ofObj]
  exact ⟨(Cat.Hom.toNatIso (G.mapId (site S))).app x⟩

/-! ## 7. The target-locked statement of the bicategorical Yoneda comparison -/

/-- The bicategorical Yoneda statement in the form S1780 needs: the category of strong
transformations out of the represented pseudofunctor is equivalent to the value of G
at the representing object. -/
def YonedaComparison : Prop :=
  Nonempty (CategoryTheory.Equivalence (Pseudofunctor.StrongTrans (Y S) G)
    (G.obj (site S)))

example : Pseudofunctor.StrongTrans (Y S) G → G.obj (site S) := toObj G

example : G.obj (site S) → ∀ a, (Y S).obj a ⟶ G.obj a := fun x a => ofApp G x a

example (x : G.obj (site S)) (hid : IdCoherence G x) (hcomp : CompCoherence G x) :
    Pseudofunctor.StrongTrans (Y S) G := ofObj G x hid hcomp

/-- What is proved unconditionally: the forward direction, the app and naturality data
of the inverse, the naturality_naturality coherence, and the object-side round trip
through G.mapId. -/
theorem summary :
    (∀ eta : Pseudofunctor.StrongTrans (Y S) G,
        toObj G eta = (eta.app (site S)).toFunctor.obj (Discrete.mk (𝟙 S))) ∧
      (∀ (x : G.obj (site S)) (a : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ)
          (P : Opposite.unop a.as ⟶ S),
        (ofApp G x a).toFunctor.obj (Discrete.mk P) =
          (G.map (Quiver.Hom.toLoc P.op)).toFunctor.obj x) ∧
      (∀ (x : G.obj (site S)) {a b : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ}
          {f g : a ⟶ b} (eta : f ⟶ g),
        (Y S).map₂ eta ▷ ofApp G x b ≫ (ofNat G x g).hom =
          (ofNat G x f).hom ≫ ofApp G x a ◁ G.map₂ eta) ∧
      (∀ (x : G.obj (site S)) (hid : IdCoherence G x) (hcomp : CompCoherence G x),
        Nonempty (toObj G (ofObj G x hid hcomp) ≅ x)) :=
  ⟨toObj_def G, fun x a P => ofApp_obj G x a P,
    fun x => ofNat_naturality_naturality G x,
    fun x hid hcomp => toObj_ofObj_iso G x hid hcomp⟩

#check @toObj
#check @ofApp
#check @ofNat
#check @ofNat_naturality_naturality
#check @IdCoherence
#check @CompCoherence
#check @ofObj
#check @toObj_ofObj_iso
#check @YonedaComparison

end LeanFormal.IUT.XiFPaper.S1802BicategoricalYonedaActual
