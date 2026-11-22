/-
# S1935: Cat coherence components and the three site pasting identities

## Context

S1922 reduced the obstruction for S1864 (a) (the iso-comma site pseudofunctor) to the
three site-level pasting identities

  S1890SiteCompF (f-side composite pasting),
  S1890SiteCompG (g-side composite pasting, beta direction),
  S1890SiteIdG   (g-side identity pasting),

and diagnosed the remaining problem as a failure of definitional equality of the Cat
object identifications

  (F ≫ G).toFunctor.obj X = G.toFunctor.obj (F.toFunctor.obj X),
  (𝟙 X).toFunctor.obj Y = Y.

## What is established here

1.  Both object identifications above are in fact DEFINITIONAL (rfl) in this toolchain.
    They are restated as the normalisation lemmas catCompObj and catIdObj (general
    universe) and are usable as rw lemmas on the folded forms.  Thus the diagnosis of
    S1922 is not the actual obstruction.

2.  The actual obstruction is a UNIVERSE restriction in S1922's component lemmas.
    natCompHomApp was stated for {B : Type u} and F G : B ⥤ᵖ Cat.{u,u}, i.e. with the
    object universe of B tied to the Cat universe.  On the etale site, #check with
    pp.universes gives literally
      A.source.fiber : Pseudofunctor.{0,0,0,0,1,1}
        (LocallyDiscrete.{1} (Opposite.{2} (SchemeOverField.{0} S1726K))) Cat.{0,0}
    (S1726K : Type), so B lives in Type 1 while the stack pseudofunctors land in
    Cat.{0,0}.  For natCompHomApp with {B : Type u} this forces u = 1 and hence
    Cat.{1,1}, which does not match Cat.{0,0}; the rewrite failed precisely with
    "has type Cat but is expected to have type Bundled Category.{0,0}".  Here all
    component lemmas are restated with independent universes {B : Type u} and
    Cat.{v,v} and are then instantiated at (u,v) = (1,0).

3.  The three site pasting identities S1890SiteCompF, S1890SiteCompG, S1890SiteIdG are
    proved (siteCompF, siteCompG, siteIdG).  The proofs are done at the 2-cell level
    first (where the composites are syntactically well typed), the inverse comparison
    is cancelled there, and only then the component form is extracted; this avoids the
    instances-transparency mismatch of the folded object presentations.

4.  S1890PseudofunctorCoherence is stated for ARBITRARY comparison data mapComp/mapId,
    so it is not a derivable proposition as stated.  The exact remaining input for
    S1864 (a) is recorded as S1935RemainingSitePseudofunctor: comparison data
    (necessarily the ones built from S1890RestrictCompIso / S1890RestrictIdIso)
    together with the three coherence equations for that specific data.  The identity
    square S1890IdSquare is assembled from S1890SiteIdF (S1922), the C-side mapId
    naturality (S1890) and S1890SiteIdG (proved here).  For the composite square
    S1890CompSquare note the direction mismatch recorded in section 5: S1890CompSquare
    consumes the naturality comparisons beta.hom, whereas S1890SiteCompG is the
    beta.inverse direction, so the hom-direction g-side identity still has to be
    stated and proved before S1890CompSquare can be instantiated at the site.

No sorry, no axiom, no new assumption.
-/
import tmp.sheaf.xif.paper.S1922IsoCommaCoherenceActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S1935CatCoherenceActual

open CategoryTheory
open CategoryTheory.Bicategory
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1864GeneralPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1890IsoCommaPseudofunctorActual

universe u v

/-! ## 1. Normalisation lemmas for the folded Cat object forms -/

/-- Normalisation of the object of a composite 1-cell of Cat: the folded form
(F ≫ G).toFunctor.obj X rewrites to the unfolded form.  This is a restatement of
CategoryTheory.Cat.Hom.comp_obj, proved here by rfl; it is usable with rw on folded
presentations. -/
theorem catCompObj {B C D : Cat.{v, v}} (F : B ⟶ C) (G : C ⟶ D) (X : ↑B) :
    (F ≫ G).toFunctor.obj X = G.toFunctor.obj (F.toFunctor.obj X) :=
  CategoryTheory.Cat.Hom.comp_obj F G X

/-- Normalisation of the object of the identity 1-cell of Cat: the folded form
(𝟙 B).toFunctor.obj Y rewrites to Y.  This is a restatement of
CategoryTheory.Cat.Hom.id_obj; it is usable with rw on folded presentations. -/
theorem catIdObj {B : Cat.{v, v}} (Y : ↑B) :
    ((𝟙 B : B ⟶ B)).toFunctor.obj Y = Y :=
  CategoryTheory.Cat.Hom.id_obj Y

/-! The two normalisation lemmas are in fact definitional: -/

theorem catCompObj_rfl {B C D : Cat.{v, v}} (F : B ⟶ C) (G : C ⟶ D) (X : ↑B) :
    (F ≫ G).toFunctor.obj X = G.toFunctor.obj (F.toFunctor.obj X) := rfl

theorem catIdObj_rfl {B : Cat.{v, v}} (Y : ↑B) :
    ((𝟙 B : B ⟶ B)).toFunctor.obj Y = Y := rfl

/-! The two normalisation lemmas are usable with rw / conv on folded forms: -/

example {B C D : Cat.{v, v}} (F : B ⟶ C) (G : C ⟶ D) (X : ↑B) :
    (F ≫ G).toFunctor.obj X = G.toFunctor.obj (F.toFunctor.obj X) := by
  rw [catCompObj]

example {B : Cat.{v, v}} (Y : ↑B) :
    ((𝟙 B : B ⟶ B)).toFunctor.obj Y = Y := by
  rw [catIdObj]

example {B C D E : Cat.{v, v}} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E) (X : ↑B) :
    H.toFunctor.obj ((F ≫ G).toFunctor.obj X) =
      H.toFunctor.obj (G.toFunctor.obj (F.toFunctor.obj X)) := by
  conv_lhs => rw [catCompObj]

/-! ## 2. Component lemmas for unitors and associators at an independent universe -/

theorem catLeftUnitor_hom_app {B C : Cat.{v, v}} (F : B ⟶ C) (X : ↑B) :
    (λ_ F).hom.toNatTrans.app X = 𝟙 (F.toFunctor.obj X) := by simp

theorem catLeftUnitor_inv_app {B C : Cat.{v, v}} (F : B ⟶ C) (X : ↑B) :
    (λ_ F).inv.toNatTrans.app X = 𝟙 (F.toFunctor.obj X) := by simp

theorem catRightUnitor_hom_app {B C : Cat.{v, v}} (F : B ⟶ C) (X : ↑B) :
    (ρ_ F).hom.toNatTrans.app X = 𝟙 (F.toFunctor.obj X) := by simp

theorem catRightUnitor_inv_app {B C : Cat.{v, v}} (F : B ⟶ C) (X : ↑B) :
    (ρ_ F).inv.toNatTrans.app X = 𝟙 (F.toFunctor.obj X) := by simp

theorem catAssociator_hom_app {B C D E : Cat.{v, v}} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E)
    (X : ↑B) : (α_ F G H).hom.toNatTrans.app X = 𝟙 _ := by simp

theorem catAssociator_inv_app {B C D E : Cat.{v, v}} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E)
    (X : ↑B) : (α_ F G H).inv.toNatTrans.app X = 𝟙 _ := by simp

/-! ## 3. The component identities with the trailing inverse comparison cancelled

The statements below are exactly the site pasting identities in general form: the
right-hand side is the first three factors of the componentwise coherence lemma and
the left-hand side is the componentwise coherence lemma followed by the comparison
itself.  The proofs first form the 2-cell composites (well typed syntactically), cancel
the inverse comparison there, and only then take components. -/

/-- Componentwise natCompHomApp with the trailing inverse comparison cancelled against
the comparison itself (the f-side pasting identity in general form). -/
theorem natCompHomApp_comp {B : Type u} [Bicategory B] {F G : B ⥤ᵖ Cat.{v, v}}
    (α : Pseudofunctor.StrongTrans F G)
    {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (x : ↑(F.obj a)) :
    (α.naturality (f ≫ g)).hom.toNatTrans.app x ≫
        (G.mapComp f g).hom.toNatTrans.app ((α.app a).toFunctor.obj x) =
      (α.app c).toFunctor.map ((F.mapComp f g).hom.toNatTrans.app x) ≫
        (α.naturality g).hom.toNatTrans.app ((F.map f).toFunctor.obj x) ≫
          (G.map g).toFunctor.map ((α.naturality f).hom.toNatTrans.app x) := by
  rw [← CategoryTheory.Cat.whiskerLeft_app]
  rw [← CategoryTheory.Cat.Hom₂.comp_app]
  rw [Pseudofunctor.StrongTrans.naturality_comp_hom]
  simp only [Category.assoc]
  rw [← CategoryTheory.Bicategory.whiskerLeft_comp]
  rw [Iso.inv_hom_id]
  rw [CategoryTheory.Bicategory.whiskerLeft_id]
  rw [Category.comp_id]
  simp only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerRight_app,
    CategoryTheory.Cat.whiskerLeft_app, catAssociator_hom_app, catAssociator_inv_app,
    Category.id_comp, Category.comp_id]

/-- Componentwise natCompInvApp with the trailing inverse comparison cancelled against
the comparison itself (the g-side pasting identity, beta direction, in general form). -/
theorem natCompInvApp_comp {B : Type u} [Bicategory B] {F G : B ⥤ᵖ Cat.{v, v}}
    (α : Pseudofunctor.StrongTrans F G)
    {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (x : ↑(F.obj a)) :
    (G.mapComp f g).hom.toNatTrans.app ((α.app a).toFunctor.obj x) ≫
        (G.map g).toFunctor.map ((α.naturality f).inv.toNatTrans.app x) ≫
          (α.naturality g).inv.toNatTrans.app ((F.map f).toFunctor.obj x) =
      (α.naturality (f ≫ g)).inv.toNatTrans.app x ≫
        (α.app c).toFunctor.map ((F.mapComp f g).hom.toNatTrans.app x) := by
  have hhom : (α.naturality (f ≫ g)).inv.toNatTrans.app x ≫
        (α.app c).toFunctor.map ((F.mapComp f g).hom.toNatTrans.app x)
      = ((α.naturality (f ≫ g)).inv ≫ (F.mapComp f g).hom ▷ α.app c).toNatTrans.app x := by
    rw [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerRight_app]
  rw [hhom]
  rw [Pseudofunctor.StrongTrans.naturality_comp_inv]
  simp only [Category.assoc]
  rw [CategoryTheory.Bicategory.inv_hom_whiskerRight]
  rw [Category.comp_id]
  simp only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerRight_app,
    CategoryTheory.Cat.whiskerLeft_app, catAssociator_hom_app, catAssociator_inv_app,
    Category.id_comp, Category.comp_id]

/-- Componentwise natCompIdApp with the mapId inverse comparison cancelled against the
mapId comparison itself (the identity g-side pasting identity in general form). -/
theorem natCompIdApp_comp {B : Type u} [Bicategory B] {F G : B ⥤ᵖ Cat.{v, v}}
    (α : Pseudofunctor.StrongTrans F G)
    {a : B} (x : ↑(F.obj a)) :
    (α.naturality (𝟙 a)).inv.toNatTrans.app x ≫
        (α.app a).toFunctor.map ((F.mapId a).hom.toNatTrans.app x) =
      (G.mapId a).hom.toNatTrans.app ((α.app a).toFunctor.obj x) := by
  have hhom : (G.mapId a).hom.toNatTrans.app ((α.app a).toFunctor.obj x)
      = (α.app a ◁ (G.mapId a).hom).toNatTrans.app x := by
    rw [CategoryTheory.Cat.whiskerLeft_app]
  rw [hhom]
  have hcomp : (α.naturality (𝟙 a)).inv.toNatTrans.app x ≫
        (α.app a).toFunctor.map ((F.mapId a).hom.toNatTrans.app x)
      = ((α.naturality (𝟙 a)).inv ≫ (F.mapId a).hom ▷ α.app a).toNatTrans.app x := by
    rw [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerRight_app]
  rw [hcomp]
  rw [Pseudofunctor.StrongTrans.naturality_id_inv]
  simp only [Category.assoc]
  rw [CategoryTheory.Bicategory.inv_hom_whiskerRight]
  simp only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerRight_app,
    CategoryTheory.Cat.whiskerLeft_app, catLeftUnitor_inv_app, catRightUnitor_hom_app,
    Category.id_comp, Category.comp_id]
  exact Category.comp_id _

/-! ## 4. The three site pasting identities -/

section Site

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)

/-- The f-side composite pasting identity at the actual site: the comparison of the
composite A-map, the naturality of the first cover map and the comparison of the
C-map cancel.  This is S1890SiteCompF. -/
theorem siteCompF {U V W : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ}
    (φ : U ⟶ V) (ψ : V ⟶ W) (x : ↥(A.source.fiber.obj U)) :
    S1890SiteCompF f φ ψ x := by
  unfold S1890SiteCompF
  exact (natCompHomApp_comp (F := A.source.fiber) (G := C.source.fiber) f.map φ ψ x).symm

/-- The g-side composite pasting identity at the actual site, beta direction.
This is S1890SiteCompG. -/
theorem siteCompG {U V W : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ}
    (φ : U ⟶ V) (ψ : V ⟶ W) (y : ↥(B.source.fiber.obj U)) :
    S1890SiteCompG g φ ψ y := by
  unfold S1890SiteCompG
  exact natCompInvApp_comp (F := B.source.fiber) (G := C.source.fiber) g.map φ ψ y

/-- The g-side identity pasting identity at the actual site.  This is S1890SiteIdG. -/
theorem siteIdG (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    S1890SiteIdG f g U := by
  intro x y h
  exact natCompIdApp_comp (F := B.source.fiber) (G := C.source.fiber) g.map y

end Site

/-! ## 5. The exact first missing after this file

The remaining input for S1864 (a) is the site pseudofunctor itself, i.e. the choice of
the comparison data mapComp and mapId together with the three coherence equations.
Note that S1890PseudofunctorCoherence f g mapComp mapId quantifies over ARBITRARY
mapComp and mapId; it is therefore not a derivable proposition as stated.  What is
missing is precisely the existence of comparison data satisfying it (the only
geometrically meaningful candidate being the data induced by S1890RestrictCompIso and
S1890RestrictIdIso).

Two further concrete observations sharpen the boundary.

(a) The identity half: the f-side half of S1890IdSquare is S1890SiteIdF (proved in
    S1922), its C-side half is the naturality of the C mapId comparison (available from
    Mathlib and S1890), and its g-side half is S1890SiteIdG, proved in this file.  So
    the identity square input of S1890RestrictIdIso is now covered.

(b) The composite half: S1890CompSquare consumes beta_1.hom and beta_2.hom (the
    hom-direction naturality comparisons of g.map), while S1890SiteCompG is stated in
    the beta (inverse-naturality) direction.  Hence instantiating S1890CompSquare at the
    site additionally requires the hom-direction g-side pasting identity, which is not
    stated in S1890.  This is the precise next formal statement to add before
    S1890RestrictCompIso can be applied to the site comparison data. -/

/-- The exact remaining obligation for S1864 (a): existence of site comparison data
with the three pseudofunctor coherence equations. -/
def S1935RemainingSitePseudofunctor {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C) : Prop :=
  ∃ (mapComp : ∀ {U V W : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ}
      (φ : U ⟶ V) (ψ : V ⟶ W),
      S1890IsoCommaMap f g (φ ≫ ψ) ≅
        S1890IsoCommaMap f g φ ≫ S1890IsoCommaMap f g ψ)
    (mapId : ∀ (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ),
      S1890IsoCommaMap f g (𝟙 U) ≅ 𝟙 (S1890IsoCommaObj f g U)),
    S1890PseudofunctorCoherence f g mapComp mapId

/-! ## 6. Checks and axiom audit -/

#check catCompObj
#check catIdObj
#check catCompObj_rfl
#check catIdObj_rfl
#check catLeftUnitor_hom_app
#check catLeftUnitor_inv_app
#check catRightUnitor_hom_app
#check catRightUnitor_inv_app
#check catAssociator_hom_app
#check catAssociator_inv_app
#check natCompHomApp_comp
#check natCompInvApp_comp
#check natCompIdApp_comp
#check siteCompF
#check siteCompG
#check siteIdG
#check S1935RemainingSitePseudofunctor

#print axioms catCompObj
#print axioms catIdObj
#print axioms catCompObj_rfl
#print axioms catIdObj_rfl
#print axioms catLeftUnitor_hom_app
#print axioms catLeftUnitor_inv_app
#print axioms catRightUnitor_hom_app
#print axioms catRightUnitor_inv_app
#print axioms catAssociator_hom_app
#print axioms catAssociator_inv_app
#print axioms natCompHomApp_comp
#print axioms natCompInvApp_comp
#print axioms natCompIdApp_comp
#print axioms siteCompF
#print axioms siteCompG
#print axioms siteIdG

end LeanFormal.IUT.XiFPaper.S1935CatCoherenceActual
