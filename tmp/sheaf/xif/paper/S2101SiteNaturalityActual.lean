import tmp.sheaf.xif.paper.S2076IsoCommaTwoPullbackActual

/-!
# S2101: fibre-level lift iso and site-level naturality for the iso-comma

## What is proved here

For a cone `c : S2074GeneralCone f g`, a strong transformation
`h : StrongTrans c.W (sitePseudofunctor f g)`, and isomorphisms of the two
projections `eX : h ; toA ≅ c.toA`, `eY : h ; toB ≅ c.toB`:

1. `S2096FibreIsoOfConeIso`: an isomorphism of cones at each test object
   `U` produces, via S1893's `S1893LiftIsoOfConeIso`,
   `Iso (h.app U) (gLiftApp c U)` in the fibre at `U`.
2. `S2096ProjectionCompat`: the fibre-level compatibility (twist) equation
   saying that the two projection isomorphisms are a morphism of iso-comma
   objects from `h.app U` to the canonical lift object.
3. `S2096FibreIso`: the fibre-level iso, built from `eX`, `eY` and the
   compatibility equation, using S1893's `S1893LiftUniq`.
4. `S2096FibreIso_hom_fst` / `S2096FibreIso_hom_snd`: the fibre iso
   whiskered by the two iso-comma projections is exactly the given `eX`/`eY`.
5. `S2096SiteIso`: the site-level natural iso `h ≅ gLiftSite c`, built by
   `Pseudofunctor.StrongTrans.isoMk`.  Its modification naturality is checked
   after whiskering by `toA`/`toB`; both projections reduce to the
   modification naturality of `eX`/`eY`, and the two iso-comma projections
   are jointly faithful (`S1836IsoComma_hom_ext`).
6. `S2096LiftUniq_of_projectionCompat`: the direct consumer for the
   `S2076Witness` lift.

## Exact first missing / honest boundary

The projection isomorphisms alone are **not** sufficient: two functors into
the iso-comma with isomorphic projections can differ in their structure
2-cell.  S1893's header records this for the fibre universal property, and
S2099's `S2099TwistAt` records exactly the same obstruction.  The missing
datum is `S2096ProjectionCompatibility` (equivalently the twist at every
site object and every apex object).  This file takes that datum as an explicit
hypothesis; it is not assumed silently and it is not fabricated.

The site-level coherence fields of the resulting strong transformation are
proof-irrelevant and are supplied by `StrongTrans.isoMk`; the only content
is the modification naturality, which is proved here.  `gTwoCell_ext` is the
2-cell version of joint faithfulness and is not needed for this direction,
because `S1836IsoComma_hom_ext` already closes the componentwise comparison.

## Axioms

Only `propext`, `Classical.choice` and `Quot.sound` (see the audit at the
end).  No sorry, no new axiom, no fabricated 2-cell.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S2101SiteNaturalityActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1890IsoCommaPseudofunctorActual
open LeanFormal.IUT.XiFPaper.S1893PullbackUniversalActual
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S2074IsoCommaTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S2076IsoCommaTwoPullbackActual

universe u

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)

/-! ## 1. The comparison cone and the fibre iso from a cone iso -/

/-- The comparison cone at a test object attached to a strong transformation
`h` into the iso-comma site pseudofunctor. -/
noncomputable def S2096HConeAt (c : S2074GeneralCone f g)
    (h : Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g))
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    S1893Cone (f.map.app U).toFunctor (g.map.app U).toFunctor ↥(c.W.obj U) :=
  (S1893ComparisonFunctor (f.map.app U).toFunctor (g.map.app U).toFunctor
    ↥(c.W.obj U)).obj (h.app U).toFunctor

noncomputable def S2096FibreIsoOfConeIso (c : S2074GeneralCone f g)
    (h : Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g))
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    (e : Iso (S2096HConeAt (f := f) (g := g) c h U) (gConeAt (f := f) (g := g) c U)) :
    Iso (h.app U).toFunctor (gLiftApp (f := f) (g := g) c U) :=
  (S1893LiftIsoOfConeIso (f.map.app U).toFunctor (g.map.app U).toFunctor e).symm

variable (c : S2074GeneralCone f g)
  (h : Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g))
  (eX : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toA)
  (eY : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toB)
  (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)

theorem S2096EqToHom_self_eq_id {C : Type u} [Category C] {X : C} (h : X = X) :
    eqToHom h = 𝟙 X := by
  rw [Subsingleton.elim h rfl]
  simp

noncomputable def S2096StrongTransAppIso {W T : EtaleStackPseudofunctor S1726K}
    {F G : Pseudofunctor.StrongTrans W T}
    (e : Iso F G) (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    F.app U ≅ G.app U where
  hom := e.hom.as.app U
  inv := e.inv.as.app U
  hom_inv_id := by
    have h := congrArg (fun m => m.as.app U) e.hom_inv_id
    exact h
  inv_hom_id := by
    have h := congrArg (fun m => m.as.app U) e.inv_hom_id
    exact h

noncomputable def S2096HConeToA (c : S2074GeneralCone f g)
    (h : Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g))
    (eX : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toA)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    (S2096HConeAt (f := f) (g := g) c h U).toA ≅ (gConeAt (f := f) (g := g) c U).toA :=
  Cat.Hom.toNatIso (S2096StrongTransAppIso (W := c.W) (T := A.source.fiber)
    (F := Pseudofunctor.StrongTrans.vcomp h (toA f g)) (G := c.toA) eX U)

noncomputable def S2096HConeToB (c : S2074GeneralCone f g)
    (h : Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g))
    (eY : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toB)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    (S2096HConeAt (f := f) (g := g) c h U).toB ≅ (gConeAt (f := f) (g := g) c U).toB :=
  Cat.Hom.toNatIso (S2096StrongTransAppIso (W := c.W) (T := B.source.fiber)
    (F := Pseudofunctor.StrongTrans.vcomp h (toB f g)) (G := c.toB) eY U)

def S2096ProjectionCompat (c : S2074GeneralCone f g)
    (h : Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g))
    (eX : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toA)
    (eY : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toB)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) : Prop :=
  Functor.whiskerRight (S2096HConeToA (f := f) (g := g) c h eX U).hom
      (f.map.app U).toFunctor ≫ (gConeAt (f := f) (g := g) c U).commutes.hom =
    (S2096HConeAt (f := f) (g := g) c h U).commutes.hom ≫
      Functor.whiskerRight (S2096HConeToB (f := f) (g := g) c h eY U).hom
        (g.map.app U).toFunctor

/-- The exact missing compatibility datum: at every test object the two
projection isomorphisms are compatible with the structure 2-cell of the cone,
i.e. they form a morphism of the iso-comma from `h.app U` to the canonical
lift object.  Projection isomorphisms alone do not supply this (S1893's
header and S2099's twist record the obstruction). -/
def S2096ProjectionCompatibility (c : S2074GeneralCone f g)
    (h : Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g))
    (eX : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toA)
    (eY : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toB) : Prop :=
  ∀ U, S2096ProjectionCompat (f := f) (g := g) c h eX eY U

noncomputable def S2096ConeHomOfProjections (c : S2074GeneralCone f g)
    (h : Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g))
    (eX : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toA)
    (eY : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toB)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    (hcompat : S2096ProjectionCompat (f := f) (g := g) c h eX eY U) :
    S1893Cone.Hom (S2096HConeAt (f := f) (g := g) c h U) (gConeAt (f := f) (g := g) c U) :=
  ⟨((S2096HConeToA (f := f) (g := g) c h eX U).hom,
    (S2096HConeToB (f := f) (g := g) c h eY U).hom), hcompat⟩

noncomputable def S2096ConeIsoOfProjections (c : S2074GeneralCone f g)
    (h : Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g))
    (eX : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toA)
    (eY : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toB)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    (hcompat : S2096ProjectionCompat (f := f) (g := g) c h eX eY U) :
    Iso (S2096HConeAt (f := f) (g := g) c h U) (gConeAt (f := f) (g := g) c U) := by
  haveI hA : IsIso (S2096ConeHomOfProjections (f := f) (g := g) c h eX eY U hcompat).toA := by
    change IsIso (S2096HConeToA (f := f) (g := g) c h eX U).hom
    infer_instance
  haveI hB : IsIso (S2096ConeHomOfProjections (f := f) (g := g) c h eX eY U hcompat).toB := by
    change IsIso (S2096HConeToB (f := f) (g := g) c h eY U).hom
    infer_instance
  haveI hIso : IsIso (C := S1893Cone (f.map.app U).toFunctor (g.map.app U).toFunctor ↥(c.W.obj U)) (S2096ConeHomOfProjections (f := f) (g := g) c h eX eY U hcompat) := coneHom_isIso (m := S2096ConeHomOfProjections (f := f) (g := g) c h eX eY U hcompat)
  exact asIso (S2096ConeHomOfProjections (f := f) (g := g) c h eX eY U hcompat)

noncomputable def S2096FibreIso (c : S2074GeneralCone f g)
    (h : Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g))
    (eX : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toA)
    (eY : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toB)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    (hcompat : S2096ProjectionCompat (f := f) (g := g) c h eX eY U) :
    Iso (h.app U).toFunctor (gLiftApp (f := f) (g := g) c U) :=
  S1893LiftUniq (f.map.app U).toFunctor (g.map.app U).toFunctor
    (S2096ConeIsoOfProjections (f := f) (g := g) c h eX eY U hcompat)

theorem S1893ComparisonFunctor_obj_lift_iso_hom_toA (c : S1893Cone (f.map.app U).toFunctor (g.map.app U).toFunctor ↥(c.W.obj U)) :
    ((S1893ComparisonFunctor_obj_lift_iso (f.map.app U).toFunctor (g.map.app U).toFunctor c).hom).toA =
      𝟙 c.toA := rfl

theorem S1893ComparisonFunctor_obj_lift_iso_symm_hom_toA (c : S1893Cone (f.map.app U).toFunctor (g.map.app U).toFunctor ↥(c.W.obj U)) :
    ((S1893ComparisonFunctor_obj_lift_iso (f.map.app U).toFunctor (g.map.app U).toFunctor c).symm.hom).toA =
      𝟙 c.toA := rfl

theorem S2096VcompHToA_naturality_apply (c : S2074GeneralCone f g)
    (h : Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g))
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V)
    (x : ↑(c.W.obj U)) :
    ((Pseudofunctor.StrongTrans.vcomp h (toA f g)).naturality φ).hom.toNatTrans.app x =
      (S1836IsoCommaFst (f.map.app V).toFunctor (g.map.app V).toFunctor).map
        ((h.naturality φ).hom.toNatTrans.app x) := by
  simp only [Pseudofunctor.StrongTrans.vcomp, Pseudofunctor.StrongTrans.mkOfOplax,
    Oplax.StrongTrans.vcomp_naturality_hom, Pseudofunctor.StrongTrans.toOplax, toA,
    Cat.Hom.toNatIso, NatTrans.toCatHom₂_toNatTrans,
    CategoryTheory.Functor.toCatHom_toFunctor, Cat.Hom₂.comp_app]
  simp
  erw [Category.comp_id, Category.id_comp]
  rfl

theorem S2096VcompHToB_naturality_apply (c : S2074GeneralCone f g)
    (h : Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g))
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V)
    (x : ↑(c.W.obj U)) :
    ((Pseudofunctor.StrongTrans.vcomp h (toB f g)).naturality φ).hom.toNatTrans.app x =
      (S1836IsoCommaSnd (f.map.app V).toFunctor (g.map.app V).toFunctor).map
        ((h.naturality φ).hom.toNatTrans.app x) := by
  simp only [Pseudofunctor.StrongTrans.vcomp, Pseudofunctor.StrongTrans.mkOfOplax,
    Oplax.StrongTrans.vcomp_naturality_hom, Pseudofunctor.StrongTrans.toOplax, toB,
    Cat.Hom.toNatIso, NatTrans.toCatHom₂_toNatTrans,
    CategoryTheory.Functor.toCatHom_toFunctor, Cat.Hom₂.comp_app]
  simp
  erw [Category.comp_id, Category.id_comp]
  rfl

theorem S1893ComparisonFunctor_obj_lift_iso_symm_hom_toB (c : S1893Cone (f.map.app U).toFunctor (g.map.app U).toFunctor ↥(c.W.obj U)) :
    ((S1893ComparisonFunctor_obj_lift_iso (f.map.app U).toFunctor (g.map.app U).toFunctor c).symm.hom).toB =
      𝟙 c.toB := rfl

theorem S2096FibreIso_mapIso (c : S2074GeneralCone f g)
    (h : Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g))
    (eX : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toA)
    (eY : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toB)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    (hcompat : S2096ProjectionCompat (f := f) (g := g) c h eX eY U) :
    (S1893ComparisonFunctor (f.map.app U).toFunctor (g.map.app U).toFunctor
      ↥(c.W.obj U)).mapIso (S2096FibreIso (f := f) (g := g) c h eX eY U hcompat) =
      (S2096ConeIsoOfProjections (f := f) (g := g) c h eX eY U hcompat).trans
        (S1893ComparisonFunctor_obj_lift_iso (f.map.app U).toFunctor (g.map.app U).toFunctor
          (gConeAt (f := f) (g := g) c U)).symm := by
  dsimp [S2096FibreIso, S1893LiftUniq]
  exact (Functor.FullyFaithful.isoEquiv
    (Functor.FullyFaithful.ofFullyFaithful
      (S1893ComparisonFunctor (f.map.app U).toFunctor (g.map.app U).toFunctor
        ↥(c.W.obj U)))).apply_symm_apply _

theorem S2096FibreIso_hom_fst (c : S2074GeneralCone f g)
    (h : Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g))
    (eX : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toA)
    (eY : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toB)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    (hcompat : S2096ProjectionCompat (f := f) (g := g) c h eX eY U) :
    Functor.whiskerRight (S2096FibreIso (f := f) (g := g) c h eX eY U hcompat).hom
        (S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor) =
      (S2096HConeToA (f := f) (g := g) c h eX U).hom := by
  have hmap := S2096FibreIso_mapIso (f := f) (g := g) c h eX eY U hcompat
  have hproj := congrArg (fun m => m.hom.toA) hmap
  change ((S1893ComparisonFunctor (f.map.app U).toFunctor (g.map.app U).toFunctor
    ↥(c.W.obj U)).mapIso (S2096FibreIso (f := f) (g := g) c h eX eY U hcompat)).hom.toA =
      (S2096HConeToA (f := f) (g := g) c h eX U).hom
  rw [hproj]
  change (S2096HConeToA (f := f) (g := g) c h eX U).hom ≫
    ((S1893ComparisonFunctor_obj_lift_iso (f.map.app U).toFunctor (g.map.app U).toFunctor
      (gConeAt (f := f) (g := g) c U)).symm.hom).toA = _
  rw [S1893ComparisonFunctor_obj_lift_iso_symm_hom_toA]
  simp

theorem S2096FibreIso_hom_snd (c : S2074GeneralCone f g)
    (h : Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g))
    (eX : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toA)
    (eY : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toB)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    (hcompat : S2096ProjectionCompat (f := f) (g := g) c h eX eY U) :
    Functor.whiskerRight (S2096FibreIso (f := f) (g := g) c h eX eY U hcompat).hom
        (S1836IsoCommaSnd (f.map.app U).toFunctor (g.map.app U).toFunctor) =
      (S2096HConeToB (f := f) (g := g) c h eY U).hom := by
  have hmap := S2096FibreIso_mapIso (f := f) (g := g) c h eX eY U hcompat
  have hproj := congrArg (fun m => m.hom.toB) hmap
  change ((S1893ComparisonFunctor (f.map.app U).toFunctor (g.map.app U).toFunctor
    ↥(c.W.obj U)).mapIso (S2096FibreIso (f := f) (g := g) c h eX eY U hcompat)).hom.toB =
      (S2096HConeToB (f := f) (g := g) c h eY U).hom
  rw [hproj]
  change (S2096HConeToB (f := f) (g := g) c h eY U).hom ≫
    ((S1893ComparisonFunctor_obj_lift_iso (f.map.app U).toFunctor (g.map.app U).toFunctor
      (gConeAt (f := f) (g := g) c U)).symm.hom).toB = _
  rw [S1893ComparisonFunctor_obj_lift_iso_symm_hom_toB]
  simp

theorem S2096IsoCommaMap_fst_app {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ}
    (φ : U ⟶ V) {X Y : ↑(S1890IsoCommaObj f g U)} (y : X ⟶ Y) :
    (S1836IsoCommaFst (f.map.app V).toFunctor (g.map.app V).toFunctor).map
        ((S1890IsoCommaMap f g φ).toFunctor.map y) =
      (A.source.fiber.map φ).toFunctor.map
        ((S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor).map y) := by
  calc
    (S1836IsoCommaFst (f.map.app V).toFunctor (g.map.app V).toFunctor).map
        ((S1890IsoCommaMap f g φ).toFunctor.map y)
        = ((S1890IsoCommaMap f g φ).toFunctor ⋙
            S1836IsoCommaFst (f.map.app V).toFunctor (g.map.app V).toFunctor).map y := rfl
    _ = ((S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor) ⋙
          (A.source.fiber.map φ).toFunctor).map y := by
          erw [S1890IsoCommaMap_fst]
    _ = (A.source.fiber.map φ).toFunctor.map
          ((S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor).map y) := rfl

theorem S2096IsoCommaMap_snd_app {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ}
    (φ : U ⟶ V) {X Y : ↑(S1890IsoCommaObj f g U)} (y : X ⟶ Y) :
    (S1836IsoCommaSnd (f.map.app V).toFunctor (g.map.app V).toFunctor).map
        ((S1890IsoCommaMap f g φ).toFunctor.map y) =
      (B.source.fiber.map φ).toFunctor.map
        ((S1836IsoCommaSnd (f.map.app U).toFunctor (g.map.app U).toFunctor).map y) := by
  calc
    (S1836IsoCommaSnd (f.map.app V).toFunctor (g.map.app V).toFunctor).map
        ((S1890IsoCommaMap f g φ).toFunctor.map y)
        = ((S1890IsoCommaMap f g φ).toFunctor ⋙
            S1836IsoCommaSnd (f.map.app V).toFunctor (g.map.app V).toFunctor).map y := rfl
    _ = ((S1836IsoCommaSnd (f.map.app U).toFunctor (g.map.app U).toFunctor) ⋙
          (B.source.fiber.map φ).toFunctor).map y := by
          erw [S1890IsoCommaMap_snd]
    _ = (B.source.fiber.map φ).toFunctor.map
          ((S1836IsoCommaSnd (f.map.app U).toFunctor (g.map.app U).toFunctor).map y) := rfl

theorem S2096FibreIso_hom_fst_app (c : S2074GeneralCone f g)
    (h : Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g))
    (eX : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toA)
    (eY : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toB)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    (hcompat : S2096ProjectionCompat (f := f) (g := g) c h eX eY U)
    (y : ↑(c.W.obj U)) :
    (S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor).map
        ((S2096FibreIso (f := f) (g := g) c h eX eY U hcompat).hom.app y) =
      (S2096HConeToA (f := f) (g := g) c h eX U).hom.app y := by
  simpa only [Functor.whiskerRight_app] using
    congrArg (fun α => α.app y)
      (S2096FibreIso_hom_fst (f := f) (g := g) c h eX eY U hcompat)

theorem S2096FibreIso_hom_snd_app (c : S2074GeneralCone f g)
    (h : Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g))
    (eX : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toA)
    (eY : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toB)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    (hcompat : S2096ProjectionCompat (f := f) (g := g) c h eX eY U)
    (y : ↑(c.W.obj U)) :
    (S1836IsoCommaSnd (f.map.app U).toFunctor (g.map.app U).toFunctor).map
        ((S2096FibreIso (f := f) (g := g) c h eX eY U hcompat).hom.app y) =
      (S2096HConeToB (f := f) (g := g) c h eY U).hom.app y := by
  simpa only [Functor.whiskerRight_app] using
    congrArg (fun α => α.app y)
      (S2096FibreIso_hom_snd (f := f) (g := g) c h eX eY U hcompat)

theorem S2096GLiftNat_hom_fst_app (c : S2074GeneralCone f g)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V)
    (y : ↑(c.W.obj U)) :
    (S1836IsoCommaFst (f.map.app V).toFunctor (g.map.app V).toFunctor).map
        ((gLiftNat (f := f) (g := g) c φ).hom.app y) =
      (c.toA.naturality φ).hom.toNatTrans.app y := by
  simpa only [Functor.whiskerRight_app, gLiftNatConeA] using
    congrArg (fun α => α.app y) (gLiftNat_hom_fst (f := f) (g := g) c φ)

theorem S2096GLiftNat_hom_snd_app (c : S2074GeneralCone f g)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V)
    (y : ↑(c.W.obj U)) :
    (S1836IsoCommaSnd (f.map.app V).toFunctor (g.map.app V).toFunctor).map
        ((gLiftNat (f := f) (g := g) c φ).hom.app y) =
      (c.toB.naturality φ).hom.toNatTrans.app y := by
  simpa only [Functor.whiskerRight_app, gLiftNatConeB] using
    congrArg (fun α => α.app y) (gLiftNat_hom_snd (f := f) (g := g) c φ)


noncomputable def S2096SiteIso (c : S2074GeneralCone f g)
    (h : Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g))
    (eX : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toA)
    (eY : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toB)
    (hcompat : S2096ProjectionCompatibility (f := f) (g := g) c h eX eY) :
    Iso h (gLiftSite (f := f) (g := g) c) :=
  Pseudofunctor.StrongTrans.isoMk
    (fun U => Cat.Hom.isoMk (S2096FibreIso (f := f) (g := g) c h eX eY U (hcompat U)))
    (by
      intro U V φ
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext x
      apply S1836IsoComma_hom_ext (f.map.app V).toFunctor (g.map.app V).toFunctor
      · simp only [NatTrans.comp_app, Cat.Hom₂.comp_app, Cat.whiskerLeft_toNatTrans,
          Cat.whiskerRight_toNatTrans, Functor.whiskerLeft_app, Functor.whiskerRight_app,
          Cat.Hom.isoMk, Cat.Hom.toNatIso, NatTrans.toCatHom₂_toNatTrans,
          CategoryTheory.Functor.toCatHom_toFunctor, gLiftSite, sitePseudofunctor_map,
          S2096FibreIso_hom_fst_app, S2096GLiftNat_hom_fst_app,
          S2096IsoCommaMap_fst_app, Functor.map_comp]
        rw [← S2096VcompHToA_naturality_apply]
        have hX := congrArg (fun al => al.toNatTrans.app x) (eX.hom.as.naturality φ)
        simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_toNatTrans, Cat.whiskerRight_toNatTrans,
          Functor.whiskerLeft_app, Functor.whiskerRight_app] at hX
        simpa [S2096HConeToA, S2096StrongTransAppIso] using hX
      · simp only [NatTrans.comp_app, Cat.Hom₂.comp_app, Cat.whiskerLeft_toNatTrans,
          Cat.whiskerRight_toNatTrans, Functor.whiskerLeft_app, Functor.whiskerRight_app,
          Cat.Hom.isoMk, Cat.Hom.toNatIso, NatTrans.toCatHom₂_toNatTrans,
          CategoryTheory.Functor.toCatHom_toFunctor, gLiftSite, sitePseudofunctor_map,
          S2096FibreIso_hom_snd_app, S2096GLiftNat_hom_snd_app,
          S2096IsoCommaMap_snd_app, Functor.map_comp]
        rw [← S2096VcompHToB_naturality_apply]
        have hY := congrArg (fun al => al.toNatTrans.app x) (eY.hom.as.naturality φ)
        simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_toNatTrans, Cat.whiskerRight_toNatTrans,
          Functor.whiskerLeft_app, Functor.whiskerRight_app] at hY
        simpa [S2096HConeToB, S2096StrongTransAppIso] using hY)

noncomputable def S2096LiftUniq_of_projectionCompat
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2076Square (f := f) (g := g)).Cone W)
    (h : Pseudofunctor.StrongTrans W (sitePseudofunctor f g))
    (eX : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toX)
    (eY : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toY)
    (hcompat : S2096ProjectionCompatibility (f := f) (g := g)
      (S2076ConeToGeneral (f := f) (g := g) c) h eX eY) :
    Iso h ((S2076Witness (f := f) (g := g)).lift W c) :=
  S2096SiteIso (f := f) (g := g) (S2076ConeToGeneral (f := f) (g := g) c)
    h eX eY hcompat


/-! ## 8. Checks and axiom audit -/

#check S2096ProjectionCompat
#check S2096ProjectionCompatibility
#check S2096FibreIsoOfConeIso
#check S2096FibreIso
#check S2096FibreIso_hom_fst
#check S2096FibreIso_hom_snd
#check S2096SiteIso
#check S2096LiftUniq_of_projectionCompat

#print axioms S2096FibreIsoOfConeIso
#print axioms S2096FibreIso
#print axioms S2096FibreIso_hom_fst
#print axioms S2096FibreIso_hom_snd
#print axioms S2096SiteIso
#print axioms S2096LiftUniq_of_projectionCompat

end LeanFormal.IUT.XiFPaper.S2101SiteNaturalityActual

end
