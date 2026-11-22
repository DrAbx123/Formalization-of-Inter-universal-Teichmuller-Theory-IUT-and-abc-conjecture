/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors / S2666
-/
import tmp.sheaf.xif.paper.S2622TorsorSectionUniqueActual
import tmp.sheaf.xif.paper.S2620RepresentableSheafActual
import Mathlib.AlgebraicGeometry.Limits

/-!
# S2666: new-orientation G-torsor presheaf on the slice `(Over S)ᵒᵖ`: no-go and exact salvage

## Literal target transcription: first Lean errors

The literal transcription

```
noncomputable def S2666TorsorPresheafNewLiteral
    (S : SchemeOverField F) (M N : D.U ⟶ S) : (Over S)ᵒᵖ ⥤ Type u where
  obj T :=
    { g : ZMod l.value //
      ((D.rho g)⁻¹).hom ≫ (M ≫ T.unop.hom) = N ≫ T.unop.hom }
```

does not elaborate.  The first two errors (lean v4.32.2, serial compile) are:

* `failed to solve universe constraint u + 1 =?= 1` : the subtype
  `{ g : ZMod l.value // ... }` lives in `Type 0`, not in `Type u`;
  `ULift.{u,0}` is needed (as in `S2621TorsorPresheafActual.S2620TorsorPresheaf`,
  which uses `Type (u+1)` and `ULift.{u+1,0}`).
* `Application type mismatch: The argument (Opposite.unop T).hom has type
  (Opposite.unop T).left ⟶ S but is expected to have type S ⟶ ?m`, at
  `N ≫ T.unop.hom` (and symmetrically at `M ≫ T.unop.hom`): with
  `M N : D.U ⟶ S` and `T : (Over S)ᵒᵖ`, the composite `M ≫ T.unop.hom` is
  ill-typed, because `T.unop.hom : T.unop.left ⟶ S` is a map *into* `S`.

## The over-slice is impossible even after fixing the types

The natural type-correct over-slice rendering takes `M N : S ⟶ D.U`
(the `S2621Hom` orientation) and the inverse action by post-composition.
This file records that this presheaf is **not** a sheaf for
`(etaleTopology F).over S`, for *every* `S` and *every* `M N`:
the slice contains the empty object `∅ → S`, the empty sieve is a cover of
that object (`AlgebraicGeometry.Scheme.bot_mem_grothendieckTopology`), and at
the empty object the defining equation is vacuous, so the value is all of
`ZMod l.value`, which is not a subsingleton (`l.value` is prime and `≥ 5`).

Consequently no repair of the literal formula which keeps the over-slice site
and the subtype-of-`ZMod l.value` value can give `Presheaf.IsSheaf`.
A viable statement has to exclude the empty cover.  The exact salvage is
proved below: `S2666TorsorPresheafNew_isSheafFor_of_nonempty` shows that
`Presieve.IsSheafFor P R` holds for every covering sieve `R` that contains at
least one arrow.  (The proof uses separatedness of the representable sheaf
`S2620_representableHom_slice_isSheaf` and pullbacks in `Over S`.)  The only
part of `Presheaf.IsSheaf` that fails is the empty sieve on the empty object.
-/

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
open CategoryTheory
open CategoryTheory.Limits
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2619ActionGroupoidFiberSkeleton
open LeanFormal.IUT.XiFPaper.S2621TorsorPresheafActual
open LeanFormal.IUT.XiFPaper.S2622TorsorSectionUniqueActual
open LeanFormal.IUT.XiFPaper.S2620RepresentableSheafActual
open scoped SpecOfNotation
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.S2666NewTorsorSheafActual

universe u
variable {l : PrimeGeFive} {F : Type u} [Field F]

/-- The empty `F`-scheme, as an object of `SchemeOverField F`. -/
noncomputable def S2666EmptyBase : Iut.SchemeOverField F :=
  Over.mk (AlgebraicGeometry.Scheme.emptyTo (Spec(F)))

/-- The empty object of the slice `Over S`. -/
noncomputable def S2666EmptyObject (S : Iut.SchemeOverField F) : Over S :=
  Over.mk (Over.homMk (U := S2666EmptyBase (F := F)) (V := S)
    (AlgebraicGeometry.Scheme.emptyTo S.left) (AlgebraicGeometry.Scheme.empty_ext _ _))

theorem S2666EmptyObject_left_left (S : Iut.SchemeOverField F) :
    (S2666EmptyObject (F := F) S).left.left = (∅ : AlgebraicGeometry.Scheme) := rfl

instance S2666EmptyObject_isEmpty (S : Iut.SchemeOverField F) :
    IsEmpty (S2666EmptyObject (F := F) S).left.left := by
  rw [S2666EmptyObject_left_left]
  infer_instance

variable (D : S2622TorsorData (l := l) (F := F))

/-- The closest type-correct over-slice rendering of the requested presheaf:
`M N : S ⟶ D.U` and the inverse action is post-composition by
`((D.rho g)⁻¹).hom`.  Values are lifted to `Type u` because
`{ g : ZMod l.value // ... }` lives in `Type 0`. -/
noncomputable def S2666TorsorPresheafNew
    (S : Iut.SchemeOverField F)
    (M N : S ⟶ D.toS2619ActionGroupoidData.U) :
    (Over S)ᵒᵖ ⥤ Type u where
  obj T :=
    ULift.{u,0} { g : ZMod l.value //
      (T.unop.hom ≫ M) ≫ ((D.toS2619ActionGroupoidData.rho g)⁻¹).hom = T.unop.hom ≫ N }
  map {T T'} f :=
    ↾fun x => ⟨x.down.val, by
      have h := x.down.property
      rw [show (Opposite.unop T').hom = f.unop.left ≫ (Opposite.unop T).hom from
        (Over.w f.unop).symm]
      simp only [Category.assoc] at h ⊢
      rw [h]⟩
  map_id T := by
    ext x
    rfl
  map_comp f g := by
    ext x
    rfl

theorem S2666EmptyObject_hom_subsingleton
    (S : Iut.SchemeOverField F) :
    Subsingleton ((S2666EmptyObject (F := F) S).left ⟶
      D.toS2619ActionGroupoidData.U) :=
  ⟨fun f g => Over.OverMorphism.ext (AlgebraicGeometry.Scheme.empty_ext _ _)⟩

theorem S2666EmptyObject_predicate
    (S : Iut.SchemeOverField F) (M N : S ⟶ D.toS2619ActionGroupoidData.U)
    (g : ZMod l.value) :
    ((S2666EmptyObject (F := F) S).hom ≫ M) ≫
        ((D.toS2619ActionGroupoidData.rho g)⁻¹).hom =
      (S2666EmptyObject (F := F) S).hom ≫ N := by
  letI := S2666EmptyObject_hom_subsingleton (F := F) D S
  exact Subsingleton.elim _ _

theorem S2666EmptyObject_not_subsingleton
    (S : Iut.SchemeOverField F) (M N : S ⟶ D.toS2619ActionGroupoidData.U) :
    ¬ Subsingleton ((S2666TorsorPresheafNew (l := l) (F := F) D S M N).obj
      (Opposite.op (S2666EmptyObject (F := F) S))) := by
  letI : Fact (Nat.Prime l.value) := l.factPrime
  intro h
  let p0 : { g : ZMod l.value //
      ((S2666EmptyObject (F := F) S).hom ≫ M) ≫
        ((D.toS2619ActionGroupoidData.rho g)⁻¹).hom =
      (S2666EmptyObject (F := F) S).hom ≫ N } :=
    ⟨0, S2666EmptyObject_predicate (F := F) D S M N 0⟩
  let p1 : { g : ZMod l.value //
      ((S2666EmptyObject (F := F) S).hom ≫ M) ≫
        ((D.toS2619ActionGroupoidData.rho g)⁻¹).hom =
      (S2666EmptyObject (F := F) S).hom ≫ N } :=
    ⟨1, S2666EmptyObject_predicate (F := F) D S M N 1⟩
  have hEq : (ULift.up p0 :
      (S2666TorsorPresheafNew (l := l) (F := F) D S M N).obj
        (Opposite.op (S2666EmptyObject (F := F) S))) = ULift.up p1 := h.elim _ _
  have h01 : (0 : ZMod l.value) = 1 := by
    have hval := congrArg (fun x => x.down.val) hEq
    simp only [p0, p1] at hval
    exact hval
  exact zero_ne_one h01

theorem S2666EmptyObject_bot_mem (S : Iut.SchemeOverField F) :
    (⊥ : Sieve (S2666EmptyObject (F := F) S)) ∈
      ((Iut.SchemeOverField.etaleTopology F).over S)
        (S2666EmptyObject (F := F) S) := by
  rw [GrothendieckTopology.mem_over_iff]
  rw [GrothendieckTopology.mem_over_iff]
  rw [OrderIso.map_bot, OrderIso.map_bot]
  exact AlgebraicGeometry.Scheme.bot_mem_grothendieckTopology _

/-- **S2666 no-go.**  For every `S`, `M`, `N`, the closest type-correct
over-slice new-orientation torsor presheaf fails to be a sheaf for the etale
slice topology: the empty object is covered by the empty sieve, and there the
value is the whole (nontrivial) group `ZMod l.value`. -/
theorem S2666TorsorPresheafNew_not_isSheaf
    (S : Iut.SchemeOverField F) (M N : S ⟶ D.toS2619ActionGroupoidData.U) :
    ¬ Presheaf.IsSheaf ((Iut.SchemeOverField.etaleTopology F).over S)
      (S2666TorsorPresheafNew (l := l) (F := F) D S M N) := by
  intro h
  have hpre : Presieve.IsSheaf ((Iut.SchemeOverField.etaleTopology F).over S)
      (S2666TorsorPresheafNew (l := l) (F := F) D S M N) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp h
  have hfor := hpre (⊥ : Sieve (S2666EmptyObject (F := F) S))
    (S2666EmptyObject_bot_mem (F := F) S)
  let x : Presieve.FamilyOfElements (S2666TorsorPresheafNew (l := l) (F := F) D S M N)
      (⊥ : Presieve (S2666EmptyObject (F := F) S)) := fun _ _ hh => False.elim hh
  have hx : x.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomp
    exact False.elim h₁
  obtain ⟨t, ht, huniq⟩ := hfor x hx
  refine S2666EmptyObject_not_subsingleton (F := F) D S M N ⟨fun t₁ t₂ => ?_⟩
  exact (huniq t₁ (by intro Y f hf; exact False.elim hf)).trans
    (huniq t₂ (by intro Y f hf; exact False.elim hf)).symm

@[simp] theorem S2666TorsorPresheafNew_map_down (S : Iut.SchemeOverField F)
    (M N : S ⟶ D.toS2619ActionGroupoidData.U) {T T' : (Over S)ᵒᵖ}
    (f : T ⟶ T') (z : (S2666TorsorPresheafNew (l := l) (F := F) D S M N).obj T) :
    ((S2666TorsorPresheafNew (l := l) (F := F) D S M N).map f z).down.val = z.down.val :=
  rfl

theorem S2666TorsorPresheafNew_isSheafFor_of_nonempty
    (S : Iut.SchemeOverField F) (M N : S ⟶ D.toS2619ActionGroupoidData.U)
    (X : Over S) (R : Sieve X)
    (hR : R ∈ ((Iut.SchemeOverField.etaleTopology F).over S) X)
    (hne : ∃ (Y : Over S) (f : Y ⟶ X), R f) :
    Presieve.IsSheafFor (S2666TorsorPresheafNew (l := l) (F := F) D S M N) R.arrows := by
  classical
  haveI : HasPullbacks (Over S) := inferInstance
  have hFsheaf : Presheaf.IsSheaf ((Iut.SchemeOverField.etaleTopology F).over S)
      ((Over.forget S).op ⋙ yoneda.obj D.toS2619ActionGroupoidData.U) :=
    S2620_representableHom_slice_isSheaf (F := F) D.toS2619ActionGroupoidData.U S
  have hFpre : Presieve.IsSheaf ((Iut.SchemeOverField.etaleTopology F).over S)
      ((Over.forget S).op ⋙ yoneda.obj D.toS2619ActionGroupoidData.U) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp hFsheaf
  have hsep : Presieve.IsSeparatedFor
      ((Over.forget S).op ⋙ yoneda.obj D.toS2619ActionGroupoidData.U) R.arrows :=
    (Presieve.IsSheaf.isSeparated hFpre) R hR
  intro x hx
  obtain ⟨Y₀, f₀, h₀⟩ := hne
  set g : ZMod l.value := (x f₀ h₀).down.val with hgdef
  have hconst : ∀ {Y : Over S} (f : Y ⟶ X) (hf : R f), (x f hf).down.val = g := by
    intro Y f hf
    have hcomm := hx (pullback.fst f f₀) (pullback.snd f f₀) hf h₀
      (pullback.condition (f := f) (g := f₀))
    have hval := congrArg (fun z => z.down.val) hcomm
    simpa [S2666TorsorPresheafNew_map_down, hgdef] using hval
  have hpredY : ∀ {Y : Over S} (f : Y ⟶ X) (hf : R f),
      (Y.hom ≫ M) ≫ ((D.toS2619ActionGroupoidData.rho g)⁻¹).hom = Y.hom ≫ N := by
    intro Y f hf
    have h := (x f hf).down.property
    have hfv := hconst f hf
    rwa [hfv] at h
  have hpredX : (X.hom ≫ M) ≫ ((D.toS2619ActionGroupoidData.rho g)⁻¹).hom = X.hom ≫ N := by
    refine Presieve.IsSeparatedFor.ext hsep (fun Y f hf => ?_)
    show Over.Hom.left f ≫ ((X.hom ≫ M) ≫ ((D.toS2619ActionGroupoidData.rho g)⁻¹).hom)
      = Over.Hom.left f ≫ (X.hom ≫ N)
    have h1 : Over.Hom.left f ≫ ((X.hom ≫ M) ≫ ((D.toS2619ActionGroupoidData.rho g)⁻¹).hom)
        = (Y.hom ≫ M) ≫ ((D.toS2619ActionGroupoidData.rho g)⁻¹).hom := by
      rw [← Category.assoc, ← Category.assoc, Over.w f]
    have h2 : Over.Hom.left f ≫ (X.hom ≫ N) = Y.hom ≫ N := by
      rw [← Category.assoc, Over.w f]
    rw [h1, h2]
    exact hpredY f hf
  refine ⟨ULift.up ⟨g, hpredX⟩, ?_, ?_⟩
  · intro Y f hf
    apply ULift.ext
    apply Subtype.ext
    rw [S2666TorsorPresheafNew_map_down]
    exact (hconst f hf).symm
  · intro y hy
    have h1 : (S2666TorsorPresheafNew (l := l) (F := F) D S M N).map f₀.op y = x f₀ h₀ :=
      hy f₀ h₀
    have h2 : (S2666TorsorPresheafNew (l := l) (F := F) D S M N).map f₀.op
        (ULift.up ⟨g, hpredX⟩) = x f₀ h₀ := by
      apply ULift.ext
      apply Subtype.ext
      rw [S2666TorsorPresheafNew_map_down]
    have hval := congrArg (fun z => z.down.val) (h1.trans h2.symm)
    apply ULift.ext
    apply Subtype.ext
    simpa using hval

#print axioms S2666EmptyObject_not_subsingleton
#print axioms S2666EmptyObject_bot_mem
#print axioms S2666TorsorPresheafNew_not_isSheaf
#print axioms S2666TorsorPresheafNew_isSheafFor_of_nonempty

end LeanFormal.IUT.XiFPaper.S2666NewTorsorSheafActual
end