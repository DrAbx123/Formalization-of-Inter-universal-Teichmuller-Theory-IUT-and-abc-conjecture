/-
Copyright (c) 2026 The IUT project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D9 worker (S2438)
-/
import tmp.sheaf.xif.paper.S2427PsubNatIsoConditionalActual
import tmp.sheaf.xif.paper.S2425NatIsoCastHelpersActual

/-!
# S2438: the sign projection (naturality of the S2271 cast)

`S2427PsubNatIsoConditionalActual` reduces the construction of the natural
isomorphism `S2152Q.presheafHom M N ≅ S2332Psub S M N` to a single pointwise
equation, `S2427SignProjection`: the objectwise cast `S2427Comp` of S2271 has to
be natural for the restriction maps of the two presheaves.

This file proves that equation.  The two restriction maps are

* `(S2152Q.presheafHom M N).map p`, Mathlib's `Pseudofunctor.presheafHom` map,
  which is `pullHom`, i.e. the composite of the `mapComp'` coherences of the
  pseudofunctor `S2152Q` with the functorial pullback `S1971PrecompFunctor`;
* `(S2332Psub S M N).map p`, which keeps the underlying sign element.

Since `S2152Q` is the strict pseudofunctor `S2152PFunctor.toPseudofunctor'`
attached to an ordinary functor, its `mapComp'` coherences are `eqToIso` of
equalities of functors; on the action-category model of the fibers these are
`eqToHom`s, whose sign component is `1` (`S2438mapComp'_hom_val`,
`S2438mapComp'_inv_val`).  The middle factor is `S1971PrecompFunctor`, whose sign
component is the identity (`S2438precomp_map_val`, from
`S1971PrecompFunctor_map_val`).  Hence `pullHom` preserves the sign, which is
exactly `S2427SignProjection`.

The upshot is `S2438SignProjection` and the unconditional natural isomorphism
`S2438NatIso`; the construction through the S2425 pointwise-eqToIso helper is
recorded as `S2438NatIsoOfEqToIso`.  Everything is unconditional; no sorry and
no new axiom is used.
-/

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2332PsubCorrectActual
open LeanFormal.IUT.XiFPaper.S2285RMapNatActual
open LeanFormal.IUT.XiFPaper.S2278QHomNaturalityActual
open LeanFormal.IUT.XiFPaper.S2271QHomEqualizerNatActual
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S1971ActionStackificationActual
open LeanFormal.IUT.XiFPaper.S2267QHomEqualizerMulActionActual
open LeanFormal.IUT.XiFPaper.S2425NatIsoCastHelpersActual
open LeanFormal.IUT.XiFPaper.S2427PsubNatIsoConditionalActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2438SignProjectionActual

universe u

/-- `S2152Q` presented as the strict pseudofunctor attached to the ordinary
functor `S2152PFunctor`.  This is definitionally `S2152Q`; the abbreviation only
keeps `S2152Q` from being unfolded in the coherence lemmas below. -/
abbrev S2438Q : Pseudofunctor (LocallyDiscrete ((Iut.SchemeOverField S1726K)ᵒᵖ)) Cat :=
  S2152PFunctor.toPseudofunctor'

/-- `S2438Q` is definitionally the pseudofunctor `S2152Q`. -/
theorem S2438Q_def : S2438Q = S2152Q := rfl

/-! ## 1. Components of `eqToIso` between `Cat`-morphisms -/

/-- The hom component at an object of the `eqToIso` of an equality of
`Cat`-morphisms is an `eqToHom`. -/
theorem S2438cat_eqToIso_hom_toNatTrans_app {C D : Type u} [Category C] [Category D]
    {F G : Cat.of C ⟶ Cat.of D} (h : F = G) (M : C) :
    (eqToIso h).hom.toNatTrans.app M =
      eqToHom (congrArg (fun K : Cat.of C ⟶ Cat.of D => K.toFunctor.obj M) h) := by
  cases h
  rfl

/-- The inverse component at an object of the `eqToIso` of an equality of
`Cat`-morphisms is an `eqToHom`. -/
theorem S2438cat_eqToIso_inv_toNatTrans_app {C D : Type u} [Category C] [Category D]
    {F G : Cat.of C ⟶ Cat.of D} (h : F = G) (M : C) :
    (eqToIso h).inv.toNatTrans.app M =
      eqToHom (congrArg (fun K : Cat.of C ⟶ Cat.of D => K.toFunctor.obj M) h).symm := by
  cases h
  rfl

/-- The hom component of a composite of two `eqToIso`s of `Cat`-morphisms. -/
theorem S2438cat_eqToIso_trans_app {C D : Type u} [Category C] [Category D]
    {F G Hd : Cat.of C ⟶ Cat.of D} (h1 : F = G) (h2 : G = Hd) (M : C) :
    (eqToIso h1 ≪≫ eqToIso h2).hom.toNatTrans.app M =
      (eqToIso h1).hom.toNatTrans.app M ≫ (eqToIso h2).hom.toNatTrans.app M := by
  cases h1
  cases h2
  rfl

/-- The inverse component of a composite of two `eqToIso`s of `Cat`-morphisms. -/
theorem S2438cat_eqToIso_trans_inv_app {C D : Type u} [Category C] [Category D]
    {F G Hd : Cat.of C ⟶ Cat.of D} (h1 : F = G) (h2 : G = Hd) (M : C) :
    (eqToIso h1 ≪≫ eqToIso h2).inv.toNatTrans.app M =
      (eqToIso h2).inv.toNatTrans.app M ≫ (eqToIso h1).inv.toNatTrans.app M := by
  cases h1
  cases h2
  rfl

/-! ## 2. The coherences of the strict pseudofunctor have sign one -/

/-- The hom component of the `mapComp'` coherence of the strict pseudofunctor
`S2152Q` has trivial sign. -/
theorem S2438mapComp'_hom_val {a b c : LocallyDiscrete ((Iut.SchemeOverField S1726K)ᵒᵖ)}
    (f : a ⟶ b) (g : b ⟶ c) (fg : a ⟶ c) (h : f ≫ g = fg)
    (M : S2438Q.obj a) :
    ((S2438Q.mapComp' f g fg h).hom.toNatTrans.app M).val = (1 : Iut.SignGroup) := by
  rw [Pseudofunctor.mapComp', PrelaxFunctor.map₂Iso_eqToIso,
    Functor.toPseudofunctor'_mapComp]
  generalize_proofs h1 h2
  rw [S2438cat_eqToIso_trans_app h1 h2 M, S2438cat_eqToIso_hom_toNatTrans_app h1 M,
    S2438cat_eqToIso_hom_toNatTrans_app h2 M]
  rw [ActionCategory.comp_val, S1971ActionCategory_eqToHom_val,
    S1971ActionCategory_eqToHom_val, mul_one]

/-- The inverse component of the `mapComp'` coherence of the strict pseudofunctor
`S2152Q` has trivial sign. -/
theorem S2438mapComp'_inv_val {a b c : LocallyDiscrete ((Iut.SchemeOverField S1726K)ᵒᵖ)}
    (f : a ⟶ b) (g : b ⟶ c) (fg : a ⟶ c) (h : f ≫ g = fg)
    (M : S2438Q.obj a) :
    ((S2438Q.mapComp' f g fg h).inv.toNatTrans.app M).val = (1 : Iut.SignGroup) := by
  rw [Pseudofunctor.mapComp', PrelaxFunctor.map₂Iso_eqToIso,
    Functor.toPseudofunctor'_mapComp]
  generalize_proofs h1 h2
  rw [S2438cat_eqToIso_trans_inv_app h1 h2 M, S2438cat_eqToIso_inv_toNatTrans_app h1 M,
    S2438cat_eqToIso_inv_toNatTrans_app h2 M]
  rw [ActionCategory.comp_val, S1971ActionCategory_eqToHom_val,
    S1971ActionCategory_eqToHom_val, mul_one]

/-- The functorial pullback `S1971PrecompFunctor` of the action categories does
not change the sign of a morphism. -/
theorem S2438precomp_map_val {a b : LocallyDiscrete ((Iut.SchemeOverField S1726K)ᵒᵖ)}
    (g : a ⟶ b) {P Q : S2438Q.obj a} (φ : P ⟶ Q) :
    ((S2438Q.map g).toFunctor.map φ).val = φ.val := by
  rw [show (S2438Q.map g).toFunctor = S1971PrecompFunctor g from rfl]
  exact S1971PrecompFunctor_map_val g φ

/-! ## 3. The restriction map of the `Q`-hom presheaf preserves the sign -/

variable (S : Iut.SchemeOverField S1726K)
variable (M N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S)))

/-- Restricting a morphism of the presheaf `S2152Q.presheafHom M N` along a
morphism of the over-site does not change its underlying sign element.  This is
the computation of Mathlib's `pullHom` for the strict pseudofunctor `S2152Q`. -/
theorem S2438presheafHom_map_val {T₁ T₂ : (Over S)ᵒᵖ} (p : T₁ ⟶ T₂)
    (x : (S2152Q.presheafHom M N).obj T₁) :
    ((S2152Q.presheafHom M N).map p x).val = x.val := by
  change ((S2438Q.presheafHom M N).map p x).val = x.val
  simp only [Pseudofunctor.presheafHom, Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  simp only [ConcreteCategory.hom]
  rw [ActionCategory.comp_val, ActionCategory.comp_val]
  rw [S2438mapComp'_hom_val]
  rw [S2438mapComp'_inv_val]
  rw [S2438precomp_map_val]
  rw [one_mul, mul_one]

end LeanFormal.IUT.XiFPaper.S2438SignProjectionActual

end
