/-
Copyright (c) 2026 The IUT formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.Pullbacks

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace LeanFormal.IUT.XiFPaper.Mzk1SchemePullbackIsoSourceActual

/-!
# Absorbing an isomorphism of the first factor into a fibre product

Let `X X' Y Z` be schemes, let `e : X' ≅ X` be an isomorphism, and let
`f : X ⟶ Y`, `g : Z ⟶ Y` be morphisms.  Since `e.hom` is an isomorphism,
precomposing `f` with it does not change the fibre product over `Y`:

`pullback (e.hom ≫ f) g ≅ pullback f g`.

The comparison morphisms are the two lifts

* `pullback (e.hom ≫ f) g ⟶ pullback f g`, sending `(fst, snd)` to
  `(fst ≫ e.hom, snd)`;
* `pullback f g ⟶ pullback (e.hom ≫ f) g`, sending `(fst, snd)` to
  `(fst ≫ e.inv, snd)`;

which are mutually inverse by `pullback.hom_ext`.
-/

variable {X X' Y Z : Scheme}

/-- Absorb the isomorphism `e : X' ≅ X` through the first projection: the
pullback of `e.hom ≫ f` with `g` is canonically isomorphic to the pullback of
`f` with `g`. -/
noncomputable def pullbackCompIso (e : X' ≅ X) (f : X ⟶ Y) (g : Z ⟶ Y) :
    pullback (e.hom ≫ f) g ≅ pullback f g where
  hom :=
    pullback.lift (pullback.fst (e.hom ≫ f) g ≫ e.hom) (pullback.snd (e.hom ≫ f) g)
      (by rw [Category.assoc, pullback.condition])
  inv :=
    pullback.lift (pullback.fst f g ≫ e.inv) (pullback.snd f g)
      (by rw [Category.assoc, Iso.inv_hom_id_assoc, pullback.condition])
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        Iso.hom_inv_id, Category.comp_id, Category.id_comp]
    · simp only [Category.assoc, pullback.lift_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        Iso.inv_hom_id, Category.comp_id, Category.id_comp]
    · simp only [Category.assoc, pullback.lift_snd, Category.id_comp]

/-- Compatibility of the isomorphism with the first projection. -/
theorem pullbackCompIso_hom_fst (e : X' ≅ X) (f : X ⟶ Y) (g : Z ⟶ Y) :
    (pullbackCompIso e f g).hom ≫ pullback.fst f g
      = pullback.fst (e.hom ≫ f) g ≫ e.hom := by
  dsimp only [pullbackCompIso]
  rw [pullback.lift_fst]

/-- Compatibility of the isomorphism with the second projection. -/
theorem pullbackCompIso_hom_snd (e : X' ≅ X) (f : X ⟶ Y) (g : Z ⟶ Y) :
    (pullbackCompIso e f g).hom ≫ pullback.snd f g
      = pullback.snd (e.hom ≫ f) g := by
  dsimp only [pullbackCompIso]
  rw [pullback.lift_snd]

/-- Compatibility of the inverse isomorphism with the first projection. -/
theorem pullbackCompIso_inv_fst (e : X' ≅ X) (f : X ⟶ Y) (g : Z ⟶ Y) :
    (pullbackCompIso e f g).inv ≫ pullback.fst (e.hom ≫ f) g
      = pullback.fst f g ≫ e.inv := by
  dsimp only [pullbackCompIso]
  rw [pullback.lift_fst]

/-- Compatibility of the inverse isomorphism with the second projection. -/
theorem pullbackCompIso_inv_snd (e : X' ≅ X) (f : X ⟶ Y) (g : Z ⟶ Y) :
    (pullbackCompIso e f g).inv ≫ pullback.snd (e.hom ≫ f) g
      = pullback.snd f g := by
  dsimp only [pullbackCompIso]
  rw [pullback.lift_snd]

#print axioms pullbackCompIso
#print axioms pullbackCompIso_hom_fst
#print axioms pullbackCompIso_hom_snd
#print axioms pullbackCompIso_inv_fst
#print axioms pullbackCompIso_inv_snd

end LeanFormal.IUT.XiFPaper.Mzk1SchemePullbackIsoSourceActual
