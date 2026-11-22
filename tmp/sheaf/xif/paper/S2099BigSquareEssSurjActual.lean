import tmp.sheaf.xif.paper.S2095BigLiftUniqActual
import tmp.sheaf.xif.paper.S1836CoverPullbackStackActual
import tmp.sheaf.xif.paper.S1893PullbackUniversalActual
import tmp.sheaf.xif.paper.S1890IsoCommaPseudofunctorActual

/-!
# S2099: essential surjectivity of the iso-comma cone comparison -- exact first missing

## What is asked

S2094 records the full 2-universal input

  S2094BigSquareEssSurj : forall A B C (f : A -> C) (g : B -> C),
    S1827EssSurjOf (iso-comma square (toA f g, toB f g, f.map, g.map))
      (S2076Witness f g),

where S2076 supplies only the weak seven-field TwoPullbackWitness.  S2095
reduced it to the lift-uniqueness statement S2095BigLiftUniq.  This file
determines what the cone comparison needs and proves that the projection data
alone do not provide it.

## What is proved here (no sorry, no new axiom, no fake witness)

1. The target S2099BigSquareEssSurj is literally S2094's statement and is
   proved equal to it and to S2095's lift-uniqueness form
   (S2099BigSquareEssSurj_iff_S2094, S2099BigSquareEssSurj_iff_S2095).

2. S2099TwistAt is the **fibre-level compatibility (twist) equation** for the
   two projection 2-cells alpha, beta at a site object U and an apex object x:
   f(alpha x) ; gamma = delta ; g(beta x), where delta is the structure cell of
   the comma object h x and gamma is the commuting cell of the cone.

3. S2099TwistAt_iff_comma: the twist is **exactly** the condition that the pair
   (alpha x, beta x) is a morphism of the iso-comma from h x to the canonical
   lift object.  This is the precise fibre-level content of the missing datum.

4. S2099TwistAt_canonical: the canonical lift data (h := gLiftSite c,
   alpha := gLiftToA, beta := gLiftToB) satisfy the twist, so the missing
   statement is consistent and non-vacuous.

5. S2099SiteFirstMissing is the **exact first missing 2-categorical lemma**:
   the twist holds for every cone, every 1-cell h and every pair of projection
   isomorphisms.  S2099SiteFirstMissing_at unfolds it to the comma-morphism
   form at every fibre.

6. S2099CompatibleLift records the compatible-lift form of the missing datum
   and S2099BigSquareEssSurj_of_compatibleLift proves that it yields the
   target.

## Honest boundary: the target is NOT proved

No inhabitant of S2099SiteFirstMissing or S2099CompatibleLift is produced, and
S2099BigSquareEssSurj is not asserted.  The reason is structural, not notational:

* S1893's fibre-level universal property (S1893LiftUniq) requires an
  isomorphism of *cones*, i.e. a pair of projection isomorphisms satisfying the
  comma compatibility.  Its own header records that the projection-only version
  is false: two 1-cells with isomorphic projections can differ in the
  comparison 2-cell.  The twist is precisely that comparison 2-cell condition.
* The weak fields of S2076 produce the lift of a *cone*; they say nothing about
  an arbitrary 1-cell h and its given projection 2-cells.  S1827's
  S1827EssSurjNotFromWitness shows, at the level of the abstract schema, that
  the seven recorded fields never force the missing essential surjectivity.
* Consequently a proof of S2094BigSquareEssSurj must supply the compatibility
  of the two projection 2-cells (the twist), and after that the site-level
  naturality of the fibre comparison (recorded as missing API in S2096).  Both
  are named here; neither is assumed.

Axiom footprint: propext, Classical.choice, Quot.sound (audit block at the end).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2099BigSquareEssSurjActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1827CloseRetractionActual
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1890IsoCommaPseudofunctorActual
open LeanFormal.IUT.XiFPaper.S1893PullbackUniversalActual
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S2074IsoCommaTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S2076IsoCommaTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S2094FullUniversalInputsActual
open LeanFormal.IUT.XiFPaper.S2095BigLiftUniqActual

universe u

/-! ## 1. The target statement -/

/-- **The target of S2099**: the iso-comma square of any cospan of actual
finite-etale cover maps has the full 2-universal property recorded in S1827,
with the lift of S2076. -/
def S2099BigSquareEssSurj : Prop :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C),
    S1827EssSurjOf
      (EtalePseudofunctorSquare.mk (toA f g) (toB f g) f.map g.map (commutes f g))
      (S2076Witness (f := f) (g := g))

/-- S2099's target is literally S2094's recorded input. -/
theorem S2099BigSquareEssSurj_iff_S2094 :
    S2099BigSquareEssSurj ↔ S2094BigSquareEssSurj :=
  Iff.rfl

/-- In lift-uniqueness form the target is literally S2095's statement. -/
theorem S2099BigSquareEssSurj_iff_S2095 :
    S2099BigSquareEssSurj ↔ S2095BigLiftUniq :=
  Iff.rfl

#check S2099BigSquareEssSurj
#check S2099BigSquareEssSurj_iff_S2094
#check S2099BigSquareEssSurj_iff_S2095


/-! ## 2. The fibre-level compatibility (twist) equation -/

/-- **The fibre-level twist equation.**  At a site object `U` and an object `x` of
the apex `W.obj U`, the two projection isomorphisms `alpha` (to `c.toX`) and
`beta` (to `c.toY`) are compatible with the structure isomorphism
`delta = ((h.app U).obj x).obj.hom` of the comma object `h.app U x` and the
commuting isomorphism `gamma = c.commutes` of the cone `c`.

This is exactly the condition that the pair `(alpha x, beta x)` is a morphism of
the iso-comma from `h x` to the lift object `(c.toX x, c.toY x, gamma x)`. -/
def S2099TwistAt {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    {W : EtaleStackPseudofunctor S1726K} (c : (S2076Square f g).Cone W)
    (h : Pseudofunctor.StrongTrans W (sitePseudofunctor f g))
    (alpha : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toX)
    (beta : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toY)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (x : ↑(W.obj U)) : Prop :=
  (f.map.app U).toFunctor.map ((alpha.hom.as.app U).toNatTrans.app x) ≫
      (c.commutes.hom.as.app U).toNatTrans.app x =
    ((h.app U).toFunctor.obj x).obj.hom ≫
      (g.map.app U).toFunctor.map ((beta.hom.as.app U).toNatTrans.app x)

/-- The twist equation at every site object and every object of the apex. -/
def S2099Twist {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    {W : EtaleStackPseudofunctor S1726K} (c : (S2076Square f g).Cone W)
    (h : Pseudofunctor.StrongTrans W (sitePseudofunctor f g))
    (alpha : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toX)
    (beta : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toY) : Prop :=
  ∀ (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (x : ↑(W.obj U)),
    S2099TwistAt f g c h alpha beta U x

/-! ## 3. The canonical lift satisfies the twist -/

/-- The structure cell of a canonical lift object is the commuting cell of the
cone. -/
theorem gLiftApp_obj_hom {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (c : S2074GeneralCone f g) (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    (x : ↑(c.W.obj U)) :
    ((gLiftApp (f := f) (g := g) c U).obj x).obj.hom
      = (c.commutes.hom.as.app U).toNatTrans.app x := by
  simp only [gLiftApp]
  rw [S1893Lift_structure]
  exact gConeAt_commutes_hom_app (f := f) (g := g) c U x

/-- **The twist is satisfied by the canonical lift data.**  For `h = gLiftSite c`
and the two comparison isomorphisms of S2076 both sides reduce to
`c.commutes`, so the missing compatibility is consistent and non-vacuous. -/
theorem S2099TwistAt_canonical {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) {W : EtaleStackPseudofunctor S1726K}
    (c : (S2076Square f g).Cone W)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (x : ↑(W.obj U)) :
    S2099TwistAt f g c (gLiftSite (f := f) (g := g) (S2076ConeToGeneral (f := f) (g := g) c))
      (gLiftToA (f := f) (g := g) (S2076ConeToGeneral (f := f) (g := g) c))
      (gLiftToB (f := f) (g := g) (S2076ConeToGeneral (f := f) (g := g) c)) U x := by
  unfold S2099TwistAt
  set a := ((gLiftApp (f := f) (g := g) (S2076ConeToGeneral (f := f) (g := g) c) U).obj x).obj.left with ha
  set b := ((gLiftApp (f := f) (g := g) (S2076ConeToGeneral (f := f) (g := g) c) U).obj x).obj.right with hb
  have hA : ((gLiftToA (f := f) (g := g) (S2076ConeToGeneral (f := f) (g := g) c)).hom.as.app U).toNatTrans.app x = 𝟙 a := by
    rw [gLiftToA_hom_app_as]
    rfl
  have hB : ((gLiftToB (f := f) (g := g) (S2076ConeToGeneral (f := f) (g := g) c)).hom.as.app U).toNatTrans.app x = 𝟙 b := by
    rw [gLiftToB_hom_app_as]
    rfl
  have hδ : (((gLiftSite (f := f) (g := g) (S2076ConeToGeneral (f := f) (g := g) c)).app U).toFunctor.obj x).obj.hom
      = (c.commutes.hom.as.app U).toNatTrans.app x :=
    gLiftApp_obj_hom (f := f) (g := g) (S2076ConeToGeneral (f := f) (g := g) c) U x
  rw [hA, hB, hδ]
  have hm1 : (f.map.app U).toFunctor.map (𝟙 a) = 𝟙 ((f.map.app U).toFunctor.obj a) :=
    (f.map.app U).toFunctor.map_id a
  have hm2 : (g.map.app U).toFunctor.map (𝟙 b) = 𝟙 ((g.map.app U).toFunctor.obj b) :=
    (g.map.app U).toFunctor.map_id b
  rw [hm1, hm2]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- **The twist is exactly the comma-morphism condition.**  The pair of
projection isomorphisms `(alpha x, beta x)` is a morphism of the iso-comma from
`h x` to the canonical lift object if and only if the twist equation holds.
This is the precise fibre-level content of the missing compatibility. -/
theorem S2099TwistAt_iff_comma {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) {W : EtaleStackPseudofunctor S1726K}
    (c : (S2076Square f g).Cone W)
    (h : Pseudofunctor.StrongTrans W (sitePseudofunctor f g))
    (alpha : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toX)
    (beta : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toY)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (x : ↑(W.obj U)) :
    S2099TwistAt f g c h alpha beta U x ↔
      ∃ m : (h.app U).toFunctor.obj x ⟶
          (gLiftApp (f := f) (g := g) (S2076ConeToGeneral (f := f) (g := g) c) U).obj x,
        m.hom.left = (alpha.hom.as.app U).toNatTrans.app x ∧
          m.hom.right = (beta.hom.as.app U).toNatTrans.app x := by
  constructor
  · intro htw
    refine ⟨ObjectProperty.homMk (P := fun Y : Comma (f.map.app U).toFunctor (g.map.app U).toFunctor => IsIso Y.hom)
      (CommaMorphism.mk ((alpha.hom.as.app U).toNatTrans.app x)
        ((beta.hom.as.app U).toNatTrans.app x) ?_), rfl, rfl⟩
    rw [gLiftApp_obj_hom (f := f) (g := g) (S2076ConeToGeneral (f := f) (g := g) c) U x]
    exact htw
  · rintro ⟨m, hm1, hm2⟩
    have hw := m.hom.w
    rw [hm1, hm2, gLiftApp_obj_hom (f := f) (g := g) (S2076ConeToGeneral (f := f) (g := g) c) U x] at hw
    exact hw

/-! ## 4. The exact site-level first-missing statement -/

/-- **The exact first missing 2-categorical lemma**: the fibre-level
compatibility (twist) holds for *every* cone `c`, every `h` and every pair of
projection isomorphisms.  Equivalently, by `S2099TwistAt_iff_comma`, the given
pair of projection isomorphisms is a morphism of the iso-comma from `h` to the
canonical lift at every fibre.

This is precisely the datum that the weak `TwoPullbackWitness` of S2076 does
*not* export: the witness only produces the lift of a *cone*, not the
compatibility of an arbitrary 1-cell with the cone's two projections.  It is
not a consequence of the seven recorded fields (S1827's
`S1827EssSurjNotFromWitness` records the abstract insufficiency). -/
def S2099SiteFirstMissing : Prop :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    {W : EtaleStackPseudofunctor S1726K} (c : (S2076Square f g).Cone W)
    (h : Pseudofunctor.StrongTrans W (sitePseudofunctor f g))
    (alpha : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toX)
    (beta : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toY),
    S2099Twist f g c h alpha beta

/-- The first missing statement, unfolded at one site object and one apex
object: there is a morphism of the iso-comma from `h x` to the canonical lift
object whose two projections are the given ones. -/
theorem S2099SiteFirstMissing_at (hmiss : S2099SiteFirstMissing) {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C) {W : EtaleStackPseudofunctor S1726K}
    (c : (S2076Square f g).Cone W)
    (hh : Pseudofunctor.StrongTrans W (sitePseudofunctor f g))
    (alpha : Iso (Pseudofunctor.StrongTrans.vcomp hh (toA f g)) c.toX)
    (beta : Iso (Pseudofunctor.StrongTrans.vcomp hh (toB f g)) c.toY)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (x : ↑(W.obj U)) :
    ∃ m : (hh.app U).toFunctor.obj x ⟶
        (gLiftApp (f := f) (g := g) (S2076ConeToGeneral (f := f) (g := g) c) U).obj x,
      m.hom.left = (alpha.hom.as.app U).toNatTrans.app x ∧
        m.hom.right = (beta.hom.as.app U).toNatTrans.app x :=
  (S2099TwistAt_iff_comma f g c hh alpha beta U x).mp (hmiss A B C f g c hh alpha beta U x)

/-- **The compatible-lift form of the first missing datum**: for every cone and
every 1-cell with isomorphisms of the two projections, there is an isomorphism
to the witness lift whose whiskerings are exactly those two projection
isomorphisms.  This is the input that the fibre comparison produces; the target
statement only asks for the isomorphism, forgetting the two whiskering
equations. -/
def S2099CompatibleLift : Prop :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    {W : EtaleStackPseudofunctor S1726K} (c : (S2076Square f g).Cone W)
    (hh : Pseudofunctor.StrongTrans W (sitePseudofunctor f g))
    (alpha : Iso (Pseudofunctor.StrongTrans.vcomp hh (toA f g)) c.toX)
    (beta : Iso (Pseudofunctor.StrongTrans.vcomp hh (toB f g)) c.toY),
    ∃ e : Iso hh ((S2076Witness (f := f) (g := g)).lift W c),
      Pseudofunctor.StrongTrans.whiskerRight e.hom (toA f g) =
          alpha.hom ≫ ((S2076Witness (f := f) (g := g)).liftToX W c).inv ∧
        Pseudofunctor.StrongTrans.whiskerRight e.hom (toB f g) =
          beta.hom ≫ ((S2076Witness (f := f) (g := g)).liftToY W c).inv

/-- The compatible-lift form of the first missing datum yields the target. -/
theorem S2099BigSquareEssSurj_of_compatibleLift (h : S2099CompatibleLift) :
    S2099BigSquareEssSurj := by
  intro A B C f g W c hh hX hY
  exact ⟨(h A B C f g c hh hX.some hY.some).choose⟩

#check S2099SiteFirstMissing
#check S2099SiteFirstMissing_at
#check S2099CompatibleLift
#check S2099BigSquareEssSurj_of_compatibleLift

#print axioms S2099BigSquareEssSurj_iff_S2094
#print axioms S2099BigSquareEssSurj_iff_S2095
#print axioms gLiftApp_obj_hom
#print axioms S2099TwistAt_canonical
#print axioms S2099TwistAt_iff_comma
#print axioms S2099SiteFirstMissing_at
#print axioms S2099BigSquareEssSurj_of_compatibleLift