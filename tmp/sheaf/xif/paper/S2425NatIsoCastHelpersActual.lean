/-
Copyright (c) 2026 The IUT project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D9 worker (S2425)
-/
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fin.Basic

/-!
# Cast and pointwise-naturality helpers for Type-valued (pre)sheaves

This file collects reusable, project-independent lemmas which are needed when a natural
isomorphism between Type-valued presheaves has to be assembled from *objectwise*
isomorphisms whose naturality is only available as a pointwise equality of elements.
The typical downstream shape (see e.g. S2427PsubNatIsoConditionalActual) is

  F G : Cᵒᵖ ⥤ Type
  e X : F.obj X ≃ G.obj X
  h : ∀ {X Y} (f : X ⟶ Y) (x : F.obj X), e Y (F.map f x) = G.map f (e X x)
  ⊢ F ≅ G

The main results are

* natIsoOfPointwiseEquiv and natIsoOfPointwiseIso: the construction above (for an
  arbitrary index category, hence in particular for a presheaf category Cᵒᵖ);
* presheafNatIsoOfPointwiseEquiv / presheafNatIsoOfPointwiseIso: the same construction
  stated for presheaves Cᵒᵖ ⥤ Type;
* eqToIso bookkeeping: eqToIso_symm, eqToIso_congr, the composition laws
  eqToIso_hom_trans / eqToIso_self_symm, naturality of eqToIso with
  respect to a functor (mapIso_eqToIso), the component formula for an equality of functors
  (eqToIso_app), and the evaluation formula in Type (eqToIso_hom_apply,
  eqToIso_inv_apply);
* subtype extensionality: subtype_funext, subtype_eq_of_forall_iff (type equality of
  subtypes from a pointwise iff), cast_subtype_mk / subtype_eqToIso_apply (the value
  computation of the induced eqToIso on subtype elements).

Every result below is checked by the kernel; no placeholder proofs and no extra assumptions are used.
-/

noncomputable section

set_option linter.unusedVariables false

open CategoryTheory

universe u v w u₁ v₁

namespace LeanFormal.IUT.XiFPaper.S2425NatIsoCastHelpersActual

/-! ## 1. eqToIso bookkeeping -/

section EqToIso

variable {C : Type u} [Category.{w} C]

/-- eqToIso commutes with Iso.symm: the inverse of the cast along h is the cast along
h.symm. -/
theorem eqToIso_symm {X Y : C} (h : X = Y) : eqToIso h.symm = (eqToIso h).symm := by
  cases h
  rfl

/-- eqToIso depends only on the two objects, not on the chosen proof of their equality. -/
theorem eqToIso_congr {X Y : C} (h₁ h₂ : X = Y) : eqToIso h₁ = eqToIso h₂ := by
  rw [Subsingleton.elim h₁ h₂]

/-- The hom-level composition law for eqToIso. -/
theorem eqToIso_hom_trans {X Y Z : C} (p : X = Y) (q : Y = Z) :
    (eqToIso p).hom ≫ (eqToIso q).hom = (eqToIso (p.trans q)).hom := by
  rw [← Iso.trans_hom, eqToIso_trans]

/-- Casting along an equality and then along its inverse is the identity. -/
theorem eqToIso_self_symm {X Y : C} (p : X = Y) :
    eqToIso p ≪≫ eqToIso p.symm = Iso.refl X := by
  cases p
  simp

/-- eqToIso is natural with respect to any functor. -/
theorem mapIso_eqToIso {D : Type u₁} [Category.{v₁} D] (F : C ⥤ D) {X Y : C} (h : X = Y) :
    F.mapIso (eqToIso h) = eqToIso (congrArg F.obj h) := by
  cases h
  simp

/-- The component of the isomorphism of functors induced by an equality of functors. -/
theorem eqToIso_app {D : Type u₁} [Category.{v₁} D] {F G : C ⥤ D} (h : F = G) (X : C) :
    (eqToIso h).hom.app X = eqToHom (congrArg (fun K : C ⥤ D => K.obj X) h) := by
  cases h
  simp

end EqToIso

/-! ## 2. eqToIso in the category of types -/

section TypeCast

variable {X Y : Type u}

/-- In Type, the forward map of eqToIso h is the transport cast h. -/
theorem eqToIso_hom_apply (h : X = Y) (x : X) : (eqToIso h).hom x = cast h x := by
  cases h
  rfl

/-- In Type, the inverse map of eqToIso h is the transport cast h.symm. -/
theorem eqToIso_inv_apply (h : X = Y) (y : Y) : (eqToIso h).inv y = cast h.symm y := by
  cases h
  rfl

end TypeCast

/-! ## 3. Subtype extensionality and subtype casts -/

section Subtype

/-- Extensionality for functions into a subtype: it suffices to compare the underlying
values. -/
theorem subtype_funext {α β : Type u} {p : β → Prop} {f g : α → Subtype p}
    (h : ∀ a, (f a : β) = (g a : β)) : f = g :=
  funext fun a => Subtype.ext (h a)

/-- Two subtypes of the same ambient type are equal as soon as their defining predicates
are pointwise equivalent (uses propext). -/
theorem subtype_eq_of_forall_iff {α : Type u} {p q : α → Prop} (h : ∀ a, p a ↔ q a) :
    Subtype p = Subtype q :=
  congrArg Subtype (funext fun a => propext (h a))

/-- Casting a subtype element along an equality of defining predicates does not change the
underlying value. -/
theorem cast_subtype_mk {α : Type u} {p q : α → Prop} (h : p = q) (a : α) (ha : p a) :
    (cast (congrArg Subtype h) (⟨a, ha⟩ : Subtype p) : Subtype q) = ⟨a, h ▸ ha⟩ := by
  cases h
  rfl

/-- The underlying value of a subtype element is preserved by the cast of
cast_subtype_mk. -/
theorem cast_subtype_val {α : Type u} {p q : α → Prop} (h : p = q) (a : α) (ha : p a) :
    ((cast (congrArg Subtype h) (⟨a, ha⟩ : Subtype p) : Subtype q) : α) = a := by
  cases h
  rfl

/-- Evaluation of the eqToIso cast on a subtype element: the underlying value is unchanged
and the proof component is transported. -/
theorem subtype_eqToIso_apply {α : Type u} {p q : α → Prop} (h : ∀ a, p a ↔ q a)
    (a : α) (ha : p a) :
    (eqToIso (subtype_eq_of_forall_iff h)).hom (⟨a, ha⟩ : Subtype p) =
      (⟨a, (h a).1 ha⟩ : Subtype q) := by
  have hEq : subtype_eq_of_forall_iff h =
      congrArg Subtype (funext fun a => propext (h a)) := Subsingleton.elim _ _
  rw [hEq, eqToIso_hom_apply]
  exact cast_subtype_mk (funext fun a => propext (h a)) a ha

end Subtype

/-! ## 4. Natural isomorphisms from pointwise natural objectwise isomorphisms -/

section PointwiseNatIso

variable {C : Type u} [Category.{w} C] {F G : C ⥤ Type v}

/-- Build a natural isomorphism F ≅ G from objectwise isomorphisms c X : F.obj X ≅ G.obj X
whose naturality square only commutes pointwise (i.e. on elements). -/
def natIsoOfPointwiseIso (c : ∀ X, F.obj X ≅ G.obj X)
    (h : ∀ {X Y : C} (f : X ⟶ Y) (x : F.obj X),
      (c Y).hom (F.map f x) = G.map f ((c X).hom x)) : F ≅ G :=
  NatIso.ofComponents c fun {X Y} f => by
    ext x
    exact h f x

@[simp]
theorem natIsoOfPointwiseIso_hom_app (c : ∀ X, F.obj X ≅ G.obj X)
    (h : ∀ {X Y : C} (f : X ⟶ Y) (x : F.obj X),
      (c Y).hom (F.map f x) = G.map f ((c X).hom x)) (X : C) :
    (natIsoOfPointwiseIso c h).hom.app X = (c X).hom :=
  rfl

@[simp]
theorem natIsoOfPointwiseIso_inv_app (c : ∀ X, F.obj X ≅ G.obj X)
    (h : ∀ {X Y : C} (f : X ⟶ Y) (x : F.obj X),
      (c Y).hom (F.map f x) = G.map f ((c X).hom x)) (X : C) :
    (natIsoOfPointwiseIso c h).inv.app X = (c X).inv :=
  rfl

/-- Pointwise naturality of the inverse components, derived from the forward direction. -/
theorem natIsoOfPointwiseIso_inv_natural (c : ∀ X, F.obj X ≅ G.obj X)
    (h : ∀ {X Y : C} (f : X ⟶ Y) (x : F.obj X),
      (c Y).hom (F.map f x) = G.map f ((c X).hom x))
    {X Y : C} (f : X ⟶ Y) (y : G.obj X) :
    F.map f ((c X).inv y) = (c Y).inv (G.map f y) := by
  have key : (c Y).hom (F.map f ((c X).inv y)) = G.map f y := by
    rw [h f ((c X).inv y), Iso.inv_hom_id_apply]
  calc F.map f ((c X).inv y)
      = (c Y).inv ((c Y).hom (F.map f ((c X).inv y))) := by
        rw [Iso.hom_inv_id_apply]
    _ = (c Y).inv (G.map f y) := by rw [key]

/-- Build a natural isomorphism F ≅ G from objectwise equivalences of types whose
naturality square only commutes pointwise. -/
def natIsoOfPointwiseEquiv (e : ∀ X, F.obj X ≃ G.obj X)
    (h : ∀ {X Y : C} (f : X ⟶ Y) (x : F.obj X), e Y (F.map f x) = G.map f (e X x)) :
    F ≅ G :=
  natIsoOfPointwiseIso (fun X => (e X).toIso) fun {X Y} f x => h f x

@[simp]
theorem natIsoOfPointwiseEquiv_hom_app (e : ∀ X, F.obj X ≃ G.obj X)
    (h : ∀ {X Y : C} (f : X ⟶ Y) (x : F.obj X), e Y (F.map f x) = G.map f (e X x))
    (X : C) :
    (natIsoOfPointwiseEquiv e h).hom.app X = (e X).toIso.hom :=
  rfl

@[simp]
theorem natIsoOfPointwiseEquiv_hom_app_apply (e : ∀ X, F.obj X ≃ G.obj X)
    (h : ∀ {X Y : C} (f : X ⟶ Y) (x : F.obj X), e Y (F.map f x) = G.map f (e X x))
    (X : C) (x : F.obj X) :
    (natIsoOfPointwiseEquiv e h).hom.app X x = e X x := by
  rw [natIsoOfPointwiseEquiv_hom_app]
  rfl

/-- Pointwise naturality of the inverse equivalences, in the form needed for casts. -/
theorem natIsoOfPointwiseEquiv_inv_apply (e : ∀ X, F.obj X ≃ G.obj X)
    (h : ∀ {X Y : C} (f : X ⟶ Y) (x : F.obj X), e Y (F.map f x) = G.map f (e X x))
    {X Y : C} (f : X ⟶ Y) (y : G.obj X) :
    (e Y).symm (G.map f y) = F.map f ((e X).symm y) :=
  congrFun (FunctorToTypes.naturality_symm e (fun {_ _} f => funext fun x => h f x) f) y

/-- Build a natural isomorphism F ≅ G from objectwise equalities of types (the shape in
which eqToIso components usually arise) whose induced maps are natural pointwise. -/
def natIsoOfPointwiseEqToIso (w : ∀ X, F.obj X = G.obj X)
    (h : ∀ {X Y : C} (f : X ⟶ Y) (x : F.obj X),
      (eqToIso (w Y)).hom (F.map f x) = G.map f ((eqToIso (w X)).hom x)) : F ≅ G :=
  natIsoOfPointwiseIso (fun X => eqToIso (w X)) h

@[simp]
theorem natIsoOfPointwiseEqToIso_hom_app (w : ∀ X, F.obj X = G.obj X)
    (h : ∀ {X Y : C} (f : X ⟶ Y) (x : F.obj X),
      (eqToIso (w Y)).hom (F.map f x) = G.map f ((eqToIso (w X)).hom x)) (X : C) :
    (natIsoOfPointwiseEqToIso w h).hom.app X = eqToHom (w X) :=
  rfl

end PointwiseNatIso

/-! ## 5. Presheaf form -/

section Presheaf

variable {C : Type u} [Category.{w} C] {F G : Cᵒᵖ ⥤ Type v}

/-- Pointwise natural objectwise isomorphisms of presheaves give a natural isomorphism. -/
def presheafNatIsoOfPointwiseIso (c : ∀ X, F.obj X ≅ G.obj X)
    (h : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : F.obj X),
      (c Y).hom (F.map f x) = G.map f ((c X).hom x)) : F ≅ G :=
  natIsoOfPointwiseIso c h

/-- Pointwise natural objectwise equivalences of presheaves give a natural isomorphism. -/
def presheafNatIsoOfPointwiseEquiv (e : ∀ X, F.obj X ≃ G.obj X)
    (h : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : F.obj X), e Y (F.map f x) = G.map f (e X x)) :
    F ≅ G :=
  natIsoOfPointwiseEquiv e h

@[simp]
theorem presheafNatIsoOfPointwiseEquiv_hom_app (e : ∀ X, F.obj X ≃ G.obj X)
    (h : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : F.obj X), e Y (F.map f x) = G.map f (e X x))
    (X : Cᵒᵖ) :
    (presheafNatIsoOfPointwiseEquiv e h).hom.app X = (e X).toIso.hom :=
  rfl

end Presheaf

/-! ## 6. A small abstract test: the walking arrow -/

/-- Objects of the walking arrow (the poset a < b). -/
inductive S2425Two : Type
  | a
  | b

/-- Morphisms of the walking arrow: identities and a single arrow a ⟶ b. -/
inductive S2425TwoHom : S2425Two → S2425Two → Type
  | id : (X : S2425Two) → S2425TwoHom X X
  | step : S2425TwoHom S2425Two.a S2425Two.b

namespace S2425TwoHom

/-- Composition of morphisms of the walking arrow. -/
def comp : {X Y Z : S2425Two} → S2425TwoHom X Y → S2425TwoHom Y Z → S2425TwoHom X Z
  | _, _, _, .id _, g => g
  | _, _, _, .step, .id _ => .step

/-- The map part of the test functor S2425F. -/
def mapF : {X Y : S2425Two} → S2425TwoHom X Y → (Fin 2 ⟶ Fin 2)
  | _, _, _ => 𝟙 (Fin 2)

/-- The map part of the test functor S2425G: the identity on the identities and the swap
on the unique arrow. -/
def mapG : {X Y : S2425Two} → S2425TwoHom X Y → (Fin 2 ⟶ Fin 2)
  | _, _, .id _ => 𝟙 (Fin 2)
  | _, _, .step => TypeCat.ofHom (Equiv.swap (0 : Fin 2) (1 : Fin 2))

instance : CategoryTheory.Category S2425Two where
  Hom := S2425TwoHom
  comp := fun {X Y Z} f g => S2425TwoHom.comp f g
  id := S2425TwoHom.id
  id_comp f := by cases f <;> rfl
  comp_id f := by cases f <;> rfl
  assoc f g h := by cases f <;> cases g <;> cases h <;> rfl

end S2425TwoHom

open S2425TwoHom

/-- The constant functor at Fin 2 whose action on the arrow is the identity. -/
def S2425F : S2425Two ⥤ Type where
  obj _ := Fin 2
  map {X Y} f := S2425TwoHom.mapF f
  map_id X := rfl
  map_comp {X Y Z} f g := by
    change (𝟙 (Fin 2) : Fin 2 ⟶ Fin 2) = 𝟙 (Fin 2) ≫ 𝟙 (Fin 2)
    rw [Category.id_comp]

/-- The constant functor at Fin 2 whose action on the arrow is the swap 0 ↔ 1. -/
def S2425G : S2425Two ⥤ Type where
  obj _ := Fin 2
  map {X Y} f := S2425TwoHom.mapG f
  map_id X := rfl
  map_comp {X Y Z} f g := by
    cases f <;> cases g <;> rfl

/-- The objectwise equivalences of the test example: the identity on a, the swap on b. -/
def S2425E : (X : S2425Two) → (Fin 2 ≃ Fin 2)
  | .a => Equiv.refl (Fin 2)
  | .b => Equiv.swap (0 : Fin 2) (1 : Fin 2)

/-- Pointwise naturality of S2425E for the test functors S2425F and S2425G. -/
theorem S2425E_natural {X Y : S2425Two} (f : S2425TwoHom X Y) (x : Fin 2) :
    S2425E Y (S2425F.map f x) = S2425G.map f (S2425E X x) := by
  cases f with
  | id X =>
    change (S2425E X) ((𝟙 (Fin 2) : Fin 2 ⟶ Fin 2) x) =
      (𝟙 (Fin 2) : Fin 2 ⟶ Fin 2) ((S2425E X) x)
    rw [CategoryTheory.types_id_apply, CategoryTheory.types_id_apply]
  | step =>
    change (Equiv.swap (0 : Fin 2) (1 : Fin 2)) ((𝟙 (Fin 2) : Fin 2 ⟶ Fin 2) x) =
      TypeCat.ofHom (Equiv.swap (0 : Fin 2) (1 : Fin 2)) x
    rw [CategoryTheory.types_id_apply, TypeCat.ofHom_apply]

/-- The natural isomorphism produced by the pointwise construction on the test example. -/
def S2425TestIso : S2425F ≅ S2425G :=
  natIsoOfPointwiseEquiv S2425E S2425E_natural

/-- The component at a of the test isomorphism is the identity. -/
theorem S2425TestIso_app_a :
    S2425TestIso.hom.app S2425Two.a = 𝟙 (Fin 2) := by
  rw [S2425TestIso, natIsoOfPointwiseEquiv_hom_app]
  rfl

/-- The component at b of the test isomorphism is the swap. -/
theorem S2425TestIso_app_b_apply (x : Fin 2) :
    S2425TestIso.hom.app S2425Two.b x = Equiv.swap (0 : Fin 2) (1 : Fin 2) x := by
  rw [S2425TestIso, natIsoOfPointwiseEquiv_hom_app_apply]
  rfl

/-- The inverse components of the test isomorphism are the inverse equivalences. -/
theorem S2425TestIso_inv_app_b_apply (x : Fin 2) :
    S2425TestIso.inv.app S2425Two.b x = (Equiv.swap (0 : Fin 2) (1 : Fin 2)).symm x := by
  rw [S2425TestIso, natIsoOfPointwiseEquiv, natIsoOfPointwiseIso_inv_app]
  rfl

/-! ## 7. Tests of the cast and subtype lemmas -/

section CastTests

/-- Symmetry of eqToIso. -/
example {α β : Type} (h : α = β) : eqToIso h.symm = (eqToIso h).symm :=
  eqToIso_symm h

/-- The composition law of eqToIso on homs. -/
example {α β γ : Type} (h : α = β) (k : β = γ) :
    (eqToIso h).hom ≫ (eqToIso k).hom = (eqToIso (h.trans k)).hom :=
  eqToIso_hom_trans h k

/-- Transport in Type computed pointwise. -/
example {α β : Type} (h : α = β) (x : α) : (eqToIso h).hom x = cast h x :=
  eqToIso_hom_apply h x

/-- Naturality of eqToIso with respect to a functor. -/
example {C : Type u} [Category.{w} C] (F : C ⥤ Type) {X Y : C} (h : X = Y) :
    F.mapIso (eqToIso h) = eqToIso (congrArg F.obj h) :=
  mapIso_eqToIso F h

/-- Subtype equality from a pointwise iff, and the computation of the induced cast. -/
example :
    (eqToIso (subtype_eq_of_forall_iff (fun n : Nat => eq_comm))).hom
        (⟨0, rfl⟩ : Subtype (fun n : Nat => n = 0)) = ⟨0, rfl⟩ :=
  subtype_eqToIso_apply (p := fun n : Nat => n = 0) (q := fun n : Nat => 0 = n)
    (fun n : Nat => eq_comm) 0 rfl

end CastTests

end LeanFormal.IUT.XiFPaper.S2425NatIsoCastHelpersActual

end

#print axioms LeanFormal.IUT.XiFPaper.S2425NatIsoCastHelpersActual.eqToIso_hom_trans
#print axioms LeanFormal.IUT.XiFPaper.S2425NatIsoCastHelpersActual.eqToIso_self_symm
