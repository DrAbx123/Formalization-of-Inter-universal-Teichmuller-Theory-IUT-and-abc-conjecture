import tmp.sheaf.xif.paper.S1802BicategoricalYonedaActual

/-!
# S1824: the two remaining StrongTrans coherence fields for the bicategorical
# Yoneda comparison of S1802

S1802 constructs, for a field `F`, a scheme `S` over `F` and an arbitrary
category-valued etale pseudofunctor `G`:

* `toObj  : StrongTrans (Y S) G -> G.obj (site S)`;
* `ofApp  : G.obj (site S) -> (a : site) -> (Y S).obj a --> G.obj a`;
* `ofNat`, the strong naturality 2-isomorphism of `ofApp`, built from `G.mapComp`;
* the `naturality_naturality` field;
* the object-side round trip `toObj_ofObj_iso`, using `G.mapId`.

It left open exactly the two coherence fields `IdCoherence` and `CompCoherence`.
This file proves them, with no `sorry`, no new axiom and no extra hypothesis:

* `idCoherence`: `(ofNat (1 a)).hom >> app a ◁ (G.mapId a).hom` equals the
  unitors of `Cat`;
* `compCoherence`: the associativity of the naturality isomorphisms against
  `G.mapComp`.

The proof is the one diagnosed in S1802 section 5: reduce (via `Cat.Hom₂.ext`,
`NatTrans.ext`, `funext` and the `Cat` computation rules) to the component at a
section `P`; rewrite `G`'s comparison with `Pseudofunctor.mapComp_id_right_hom`
(resp. `mapComp_assoc_right_hom`); use that the site is locally discrete to turn
`G.map₂` of its unitors/associators into `eqToHom` (`map₂_eqToHom`); then merge
the resulting `eqToHom`s (`eqToHom_trans`).  The `let b := mk (op (unop a.as))`
normalisation makes the object indices produced by `mapComp` and by the goal
syntactically equal.

## Status of the comparison

The two coherence fields are proved unconditionally below, hence
`ofObjFull x := ofObj G x (idCoherence G x) (compCoherence G x)` is an actual
strong transformation for every `x : G.obj (site S)`, and `toObj (ofObjFull x)`
is isomorphic to `x` (`counitIso` / `toObj_ofObjFull_iso`).

The forward and inverse functors `toObjFunctor`, `ofObjFunctor` and the counit
`ofObjFunctor ⋙ toObjFunctor ≅ 1` are built unconditionally.  The remaining
input for the full equivalence `YonedaComparison` is the unit natural
isomorphism `1 ≅ toObjFunctor ⋙ ofObjFunctor`; its component isomorphisms are
`unitNat`, and the precise component coherence they must satisfy is stated as
`UnitCoherence`.  `unitIsoOf` produces the unit modification from that
coherence, and `yonedaComparisonOfUnitIso` assembles the equivalence from an
arbitrary unit natural isomorphism.  `UnitCoherence` itself is not proved here.

-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S1824YonedaCoherenceActual

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT.XiFPaper.S1802BicategoricalYonedaActual

universe u

variable {F : Type u} [Field F]
variable {S : Iut.SchemeOverField F}
variable (G : Iut.EtaleStackPseudofunctor F)

/-! ## Auxiliary lemmas -/

/-- On the discrete category of sections, the functor `ofApp` sends every
morphism to an `eqToHom`; this is the computation rule used in the coherences. -/
lemma ofApp_map (x : G.obj (site S)) (a : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ)
    {P Q : Discrete (Opposite.unop a.as ⟶ S)} (f : P ⟶ Q) :
    (ofApp G x a).toFunctor.map f =
      eqToHom (congrArg (fun R : Opposite.unop a.as ⟶ S =>
        (G.map (Quiver.Hom.toLoc R.op)).toFunctor.obj x) (Discrete.eq_of_hom f)) := by
  obtain ⟨⟨h⟩⟩ := f
  rfl

/-- `map₂` of a discrete `eqToHom` is an `eqToHom` of the images. -/
lemma map₂_eqToHom {B : Type*} [Bicategory B] [Bicategory.IsLocallyDiscrete B]
    (H : B ⥤ᵖ Cat.{u, u}) {a b : B} {f g : a ⟶ b} (h : f = g) :
    H.map₂ (eqToHom h) = eqToHom (congrArg H.map h) := by
  cases h
  simp

/-! ## The two coherence fields -/

theorem idCoherence (x : G.obj (site S)) : IdCoherence G x := by
  intro a
  let b : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ := LocallyDiscrete.mk (Opposite.op (Opposite.unop a.as))
  change (ofNat G x (𝟙 b)).hom ≫ ofApp G x b ◁ (G.mapId b).hom =
    ((Y S).mapId b).hom ▷ ofApp G x b ≫ (λ_ (ofApp G x b)).hom ≫ (ρ_ (ofApp G x b)).inv
  apply CategoryTheory.Cat.Hom₂.ext
  apply CategoryTheory.NatTrans.ext
  funext P
  obtain ⟨P⟩ := P
  simp only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerLeft_app,
    CategoryTheory.Cat.whiskerRight_app, CategoryTheory.Cat.leftUnitor_hom_app,
    CategoryTheory.Cat.rightUnitor_inv_app, CategoryTheory.Cat.rightUnitor_hom_app,
    CategoryTheory.Cat.leftUnitor_inv_app, CategoryTheory.Cat.eqToHom_app,
    CategoryTheory.Cat.Hom₂.eqToHom_toNatTrans,
    CategoryTheory.Cat.Hom.toNatIso_hom, ofNat_hom_app]
  simp only [ofApp_obj]
  have hcomp : (G.mapComp (Quiver.Hom.toLoc P.op) (𝟙 b)).hom =
      G.map₂ (ρ_ (Quiver.Hom.toLoc P.op)).hom ≫ (ρ_ (G.map (Quiver.Hom.toLoc P.op))).inv ≫
        G.map (Quiver.Hom.toLoc P.op) ◁ (G.mapId b).inv := by
    rw [Pseudofunctor.mapComp_id_right_hom]
  have hC : (G.map (Quiver.Hom.toLoc P.op) ◁ (G.mapId b).inv) ≫
      (G.map (Quiver.Hom.toLoc P.op) ◁ (G.mapId b).hom) = 𝟙 _ := by
    rw [← Bicategory.whiskerLeft_comp, Iso.inv_hom_id, Bicategory.whiskerLeft_id]
  have hcoh : (G.mapComp (Quiver.Hom.toLoc P.op) (𝟙 b)).hom ≫
      G.map (Quiver.Hom.toLoc P.op) ◁ (G.mapId b).hom =
      G.map₂ (ρ_ (Quiver.Hom.toLoc P.op)).hom ≫ (ρ_ (G.map (Quiver.Hom.toLoc P.op))).inv := by
    rw [hcomp]
    calc
      (G.map₂ (ρ_ (Quiver.Hom.toLoc P.op)).hom ≫ (ρ_ (G.map (Quiver.Hom.toLoc P.op))).inv ≫
          G.map (Quiver.Hom.toLoc P.op) ◁ (G.mapId b).inv) ≫
          G.map (Quiver.Hom.toLoc P.op) ◁ (G.mapId b).hom
          = G.map₂ (ρ_ (Quiver.Hom.toLoc P.op)).hom ≫
              ((ρ_ (G.map (Quiver.Hom.toLoc P.op))).inv ≫
                ((G.map (Quiver.Hom.toLoc P.op) ◁ (G.mapId b).inv) ≫
                  G.map (Quiver.Hom.toLoc P.op) ◁ (G.mapId b).hom)) := by
            simp only [Category.assoc]
      _ = G.map₂ (ρ_ (Quiver.Hom.toLoc P.op)).hom ≫
              ((ρ_ (G.map (Quiver.Hom.toLoc P.op))).inv ≫ 𝟙 _) := by rw [hC]
      _ = G.map₂ (ρ_ (Quiver.Hom.toLoc P.op)).hom ≫ (ρ_ (G.map (Quiver.Hom.toLoc P.op))).inv := by
            simpa only [Category.assoc] using
              (Category.comp_id (obj := (G.obj (site S) ⟶ G.obj b))
                (f := (G.map₂ (ρ_ (Quiver.Hom.toLoc P.op)).hom ≫ (ρ_ (G.map (Quiver.Hom.toLoc P.op))).inv)))
  rw [← CategoryTheory.Cat.whiskerLeft_app]
  rw [← CategoryTheory.Cat.Hom₂.comp_app]
  rw [hcoh]
  simp only [CategoryTheory.Cat.Hom₂.comp_app]
  have hρ : (ρ_ (Quiver.Hom.toLoc P.op)).hom = eqToHom (LocallyDiscrete.eq_of_hom (ρ_ (Quiver.Hom.toLoc P.op)).hom) :=
    Subsingleton.elim _ _
  rw [hρ]
  rw [map₂_eqToHom]
  simp only [CategoryTheory.Cat.eqToHom_app, CategoryTheory.Cat.rightUnitor_inv_app]
  rw [ofApp_map]
  simp only [CategoryTheory.eqToHom_trans]

theorem compCoherence (x : G.obj (site S)) : CompCoherence G x := by
  intro a b c f g
  let a' : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ := LocallyDiscrete.mk (Opposite.op (Opposite.unop a.as))
  let b' : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ := LocallyDiscrete.mk (Opposite.op (Opposite.unop b.as))
  let c' : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ := LocallyDiscrete.mk (Opposite.op (Opposite.unop c.as))
  let f' : a' ⟶ b' := f
  let g' : b' ⟶ c' := g
  change (ofNat G x (f' ≫ g')).hom ≫ ofApp G x a' ◁ (G.mapComp f' g').hom =
    ((Y S).mapComp f' g').hom ▷ ofApp G x c' ≫
      (α_ ((Y S).map f') ((Y S).map g') (ofApp G x c')).hom ≫
        (Y S).map f' ◁ (ofNat G x g').hom ≫
          (α_ ((Y S).map f') (ofApp G x b') (G.map g')).inv ≫
            (ofNat G x f').hom ▷ G.map g' ≫
              (α_ (ofApp G x a') (G.map f') (G.map g')).hom
  apply CategoryTheory.Cat.Hom₂.ext
  apply CategoryTheory.NatTrans.ext
  funext P
  obtain ⟨P⟩ := P
  simp only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerLeft_app,
    CategoryTheory.Cat.whiskerRight_app, CategoryTheory.Cat.leftUnitor_hom_app,
    CategoryTheory.Cat.rightUnitor_inv_app, CategoryTheory.Cat.rightUnitor_hom_app,
    CategoryTheory.Cat.leftUnitor_inv_app, CategoryTheory.Cat.eqToHom_app,
    CategoryTheory.Cat.Hom₂.eqToHom_toNatTrans,
    CategoryTheory.Cat.Hom.toNatIso_hom, ofNat_hom_app,
    CategoryTheory.Cat.associator_hom_app, CategoryTheory.Cat.associator_inv_app]
  simp only [ofApp_obj]
  have hassoc : (G.mapComp (Quiver.Hom.toLoc P.op) (f' ≫ g')).hom ≫
      G.map (Quiver.Hom.toLoc P.op) ◁ (G.mapComp f' g').hom =
      G.map₂ (α_ (Quiver.Hom.toLoc P.op) f' g').inv ≫
        (G.mapComp (Quiver.Hom.toLoc P.op ≫ f') g').hom ≫
          (G.mapComp (Quiver.Hom.toLoc P.op) f').hom ▷ G.map g' ≫
            (α_ (G.map (Quiver.Hom.toLoc P.op)) (G.map f') (G.map g')).hom := by
    rw [Pseudofunctor.mapComp_assoc_right_hom]
  rw [← CategoryTheory.Cat.whiskerLeft_app]
  rw [← CategoryTheory.Cat.Hom₂.comp_app]
  rw [hassoc]
  simp only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerRight_app,
    CategoryTheory.Cat.whiskerLeft_app]
  have hα : (α_ (Quiver.Hom.toLoc P.op) f' g').inv =
      eqToHom (LocallyDiscrete.eq_of_hom (α_ (Quiver.Hom.toLoc P.op) f' g').inv) := Subsingleton.elim _ _
  rw [hα]
  rw [map₂_eqToHom]
  simp only [CategoryTheory.Cat.eqToHom_app, CategoryTheory.Cat.associator_hom_app]
  rw [ofApp_map]
  have hX : (G.mapComp (Quiver.Hom.toLoc P.op ≫ f') g').hom.toNatTrans.app x =
      (G.mapComp (Quiver.Hom.toLoc ((((Y S).map f').toFunctor.obj { as := P }).as.op)) g').hom.toNatTrans.app x := rfl
  rw [hX]
  simp
  exact (Category.id_comp _).symm


/-! ## The strong transformation attached to an object of `G` -/

/-- The inverse direction of the comparison, as an actual strong transformation,
using the two coherence fields proved above.  No data is fabricated. -/
noncomputable def ofObjFull (x : G.obj (site S)) : Pseudofunctor.StrongTrans (Y S) G :=
  ofObj G x (idCoherence G x) (compCoherence G x)

@[simp] lemma ofObjFull_app (x : G.obj (site S))
    (a : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) :
    (ofObjFull G x).app a = ofApp G x a := rfl

@[simp] lemma ofObjFull_naturality (x : G.obj (site S))
    {a b : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ} (f : a ⟶ b) :
    (ofObjFull G x).naturality f = ofNat G x f := rfl

/-- The object-side round trip: `toObj (ofObjFull x)` is isomorphic to `x`,
via `G.mapId` at the representing object. -/
theorem toObj_ofObjFull_iso (x : G.obj (site S)) :
    Nonempty (toObj G (ofObjFull G x) ≅ x) :=
  toObj_ofObj_iso G x (idCoherence G x) (compCoherence G x)


/-! ## The unit of the comparison: component isomorphisms and the precise
remaining coherence -/

/-- The component at a section of the candidate unit natural isomorphism
`eta ≅ ofObjFull (toObj eta)`: at a section `P` it is the strong naturality
isomorphism of `eta` at `toLoc P.op`, evaluated at the identity section, with
the discreteness transport `P ≫ 1 S = P`. -/
noncomputable def unitNat (eta : Pseudofunctor.StrongTrans (Y S) G)
    (a : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) :
    eta.app a ≅ ofApp G (toObj G eta) a :=
  CategoryTheory.Cat.Hom.isoMk (Discrete.natIso (fun P : Discrete (Opposite.unop a.as ⟶ S) => by
    refine (eqToIso (congrArg (fun Q : Discrete (Opposite.unop a.as ⟶ S) =>
        (eta.app a).toFunctor.obj Q) (Discrete.ext (Category.comp_id P.as)))).symm ≪≫ ?_
    exact (CategoryTheory.Cat.Hom.toNatIso (eta.naturality (Quiver.Hom.toLoc P.as.op))).app (Discrete.mk (𝟙 S))))

/-- Computation rule for the unit component. -/
lemma unitNat_hom_app (eta : Pseudofunctor.StrongTrans (Y S) G)
    (a : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ)
    (P : Discrete (Opposite.unop a.as ⟶ S)) :
    (unitNat G eta a).hom.toNatTrans.app P =
      eqToHom (congrArg (fun Q : Discrete (Opposite.unop a.as ⟶ S) =>
        (eta.app a).toFunctor.obj Q) (Discrete.ext (Category.comp_id P.as))).symm ≫
        (CategoryTheory.Cat.Hom.toNatIso (eta.naturality (Quiver.Hom.toLoc P.as.op))).hom.app (Discrete.mk (𝟙 S)) := rfl

/-! The precise remaining coherence: the modification naturality of the unit.
It is the transported form of `eta.naturality_comp` against the comparison
2-isomorphism `G.mapComp`.  The *object* map and the *component* isomorphisms of
the reverse round trip are constructed above; what is recorded here is the exact
equation that the modification `eta ⟶ ofObjFull (toObj eta)` must satisfy. -/
def UnitCoherence (S : Iut.SchemeOverField F)
    (G : Iut.EtaleStackPseudofunctor F) : Prop :=
  ∀ (eta : Pseudofunctor.StrongTrans (Y S) G)
    {a b : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ} (f : a ⟶ b),
    (Y S).map f ◁ (unitNat G eta b).hom ≫ ((ofObjFull G (toObj G eta)).naturality f).hom =
      (eta.naturality f).hom ≫ (unitNat G eta a).hom ▷ G.map f

/-- Conditional form of the reverse round trip: assuming the exact missing
coherence, the unit modification is an isomorphism of strong transformations. -/
noncomputable def unitIsoOf (h : UnitCoherence S G)
    (eta : Pseudofunctor.StrongTrans (Y S) G) :
    eta ≅ ofObjFull G (toObj G eta) :=
  Pseudofunctor.StrongTrans.isoMk (app := fun a => unitNat G eta a)
    (naturality := fun {a b} f => h eta f)



/-! ## The two functors of the comparison -/

/-- The action on a morphism `x ⟶ y` of `G` of the candidate inverse functor:
componentwise it is the image under `G.map (toLoc P.op)`. -/
noncomputable def ofMapNat (x y : G.obj (site S)) (k : x ⟶ y)
    (a : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) : ofApp G x a ⟶ ofApp G y a :=
  NatTrans.toCatHom₂ (Discrete.natTrans (fun P : Discrete (Opposite.unop a.as ⟶ S) =>
    (G.map (Quiver.Hom.toLoc P.as.op)).toFunctor.map k))

lemma ofMapNat_app (x y : G.obj (site S)) (k : x ⟶ y)
    (a : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ)
    (P : Discrete (Opposite.unop a.as ⟶ S)) :
    (ofMapNat G x y k a).toNatTrans.app P =
      (G.map (Quiver.Hom.toLoc P.as.op)).toFunctor.map k := rfl

/-- The modification induced by `k : x ⟶ y`; its naturality is the naturality
square of `G.mapComp`. -/
noncomputable def ofMapMod (x y : G.obj (site S)) (k : x ⟶ y) :
    Pseudofunctor.StrongTrans.Modification (ofObjFull G x) (ofObjFull G y) where
  app a := ofMapNat G x y k a
  naturality f := by
    apply CategoryTheory.Cat.Hom₂.ext
    apply CategoryTheory.NatTrans.ext
    funext P
    obtain ⟨P⟩ := P
    simp only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerLeft_app,
      CategoryTheory.Cat.whiskerRight_app, ofNat_hom_app, ofObjFull_naturality,
      ofMapNat_app]
    exact (CategoryTheory.Cat.Hom.toNatIso (G.mapComp (Quiver.Hom.toLoc P.op) f)).hom.naturality k

/-- The morphism of strong transformations induced by `k : x ⟶ y`. -/
noncomputable def ofMapHom (x y : G.obj (site S)) (k : x ⟶ y) :
    ofObjFull G x ⟶ ofObjFull G y :=
  ⟨ofMapMod G x y k⟩

/-- The inverse functor of the comparison, on objects and morphisms. -/
noncomputable def ofObjFunctor : G.obj (site S) ⥤ Pseudofunctor.StrongTrans (Y S) G where
  obj x := ofObjFull G x
  map k := ofMapHom G _ _ k
  map_id x := by
    apply Pseudofunctor.StrongTrans.homCategory.ext
    intro a
    apply CategoryTheory.Cat.Hom₂.ext
    apply CategoryTheory.NatTrans.ext
    funext P
    obtain ⟨P⟩ := P
    change ((ofMapMod G x x (𝟙 x)).app a).toNatTrans.app (Discrete.mk P) =
      ((Pseudofunctor.StrongTrans.Modification.id (ofObjFull G x)).app a).toNatTrans.app (Discrete.mk P)
    simp only [ofMapMod, ofMapNat_app, Pseudofunctor.StrongTrans.Modification.id_app,
      CategoryTheory.Cat.Hom₂.id_app, ofApp_obj, ofObjFull_app, CategoryTheory.Functor.map_id]
  map_comp k l := by
    rename_i X Y Z
    apply Pseudofunctor.StrongTrans.homCategory.ext
    intro a
    apply CategoryTheory.Cat.Hom₂.ext
    apply CategoryTheory.NatTrans.ext
    funext P
    obtain ⟨P⟩ := P
    change ((ofMapMod G X Z (k ≫ l)).app a).toNatTrans.app (Discrete.mk P) =
      (((ofMapMod G X Y k).vcomp (ofMapMod G Y Z l)).app a).toNatTrans.app (Discrete.mk P)
    simp only [ofMapMod, Pseudofunctor.StrongTrans.Modification.vcomp_app,
      CategoryTheory.Cat.Hom₂.comp_app, ofMapNat_app, CategoryTheory.Functor.map_comp,
      ofApp_obj, ofObjFull_app]

/-- The forward functor of the comparison, evaluating a strong transformation at
the identity section. -/
noncomputable def toObjFunctor : Pseudofunctor.StrongTrans (Y S) G ⥤ G.obj (site S) where
  obj eta := toObj G eta
  map m := (m.as.app (site S)).toNatTrans.app (Discrete.mk (𝟙 S))
  map_id eta := by
    change ((Pseudofunctor.StrongTrans.Modification.id eta).app (site S)).toNatTrans.app (Discrete.mk (𝟙 S)) =
      𝟙 ((eta.app (site S)).toFunctor.obj (Discrete.mk (𝟙 S)))
    simp
  map_comp m n := by
    change (((m.as).vcomp (n.as)).app (site S)).toNatTrans.app (Discrete.mk (𝟙 S)) =
      (m.as.app (site S)).toNatTrans.app (Discrete.mk (𝟙 S)) ≫ (n.as.app (site S)).toNatTrans.app (Discrete.mk (𝟙 S))
    simp

/-- The counit of the comparison: `toObj (ofObjFull x) ≅ x`, given by `G.mapId`
at the representing object.  This is the unconditional round trip. -/
noncomputable def counitIso : ofObjFunctor G ⋙ toObjFunctor G ≅ 𝟭 (G.obj (site S)) :=
  CategoryTheory.Cat.Hom.toNatIso (G.mapId (site S))

/-! ## The target statement and its precise remaining input -/

/-- The bicategorical Yoneda comparison for `G`: the category of strong
transformations out of the represented pseudofunctor is equivalent to the value
of `G` at the representing object. -/
def YonedaComparison (S : Iut.SchemeOverField F)
    (G : Iut.EtaleStackPseudofunctor F) : Prop :=
  Nonempty (CategoryTheory.Equivalence (Pseudofunctor.StrongTrans (Y S) G) (G.obj (site S)))

/-- Conditional assembly of the Yoneda comparison from a unit natural
isomorphism.  The functors and the counit `ofObjFunctor ⋙ toObjFunctor ≅ 1` are
unconditional (they are built above); the only missing datum is the unit
natural isomorphism `1 ≅ toObjFunctor ⋙ ofObjFunctor`, whose component
coherence is recorded precisely as `UnitCoherence`. -/
theorem yonedaComparisonOfUnitIso
    (u : 𝟭 (Pseudofunctor.StrongTrans (Y S) G) ≅ toObjFunctor G ⋙ ofObjFunctor G) :
    YonedaComparison S G :=
  ⟨CategoryTheory.Equivalence.mk (toObjFunctor G) (ofObjFunctor G) u (counitIso G)⟩

end LeanFormal.IUT.XiFPaper.S1824YonedaCoherenceActual