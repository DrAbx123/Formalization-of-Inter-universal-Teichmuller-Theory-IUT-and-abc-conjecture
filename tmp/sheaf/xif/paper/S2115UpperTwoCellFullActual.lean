/-
# S2115: the upper-square 2-cell fullness of the actual butterfly, and the exact
# first missing of the right-cancellation reduction

## Context

S2107 reduced `S2097RightCancelStatement` to the canonical action
`S2107CanonicalLiftTwoCell` and identified the upper-square cone comparison as
the place where the 2-cell content has to come from: the S1801
`TwoCellSurjTo` shape for `D.square2` with `w2`, or a twist/direct proof of
the `D.toY1`-projection equation of `wP.liftTwoCell (E m)`.

This file settles what is actually true for the upper square, which is the
iso-comma square of S2076.

## What is proved here (unconditionally, no sorry, no new axiom)

1. `S2115ImageCone_commutes_app`: the commutes cell of the S2107 image cone
   `S2107ImageCone (S2076Square f g) u` has, at every test object and every
   apex object, exactly the structure isomorphism of the iso-comma object
   `u.app U x`.  (The associators are identities in `Cat`, and the middle
   whiskered term is the canonical structure iso.)

2. `S2115ImageConeTwistAt`: a cone morphism out of the image cone has
   projection 2-cells satisfying the S2099 twist with respect to the cone.  This
   is exactly the compatibility required by S2101's site-level assembly.

3. `S2115ProjectionCompat_of_twist`: the componentwise S2099 twist is the
   natural-transformation-level S2096 projection compatibility of S2101.

4. `S2115UpperTwoCellFull`: **the corrected upper-square 2-cell fullness.**
   For the actual iso-comma square, every pair of projection isomorphisms
   satisfying the twist is realised by an isomorphism to the S2076 lift whose
   two whiskerings are exactly those projections.  This is the true form of the
   upper-square 2-cell fullness: the twist is the compatibility of the
   projections with the cone's structure cell, and it is automatic for cone
   morphisms out of the canonical image cone.

5. `S2115ImageConeTwoCellFull`: the same statement in S1801 shape for a cone
   morphism out of the image cone (with iso components): it is realised by an
   isomorphism with the prescribed whiskerings.

## The literal S1801 statement

`S2115LiteralUpperTwoCellSurjTo` is the literal `S1801TwoCellSurjTo` for the
actual square.  It quantifies over *arbitrary* cones `c'` whose two legs happen
to equal those of `f`; nothing constrains `c'.commutes`.  Applying it with
`c' = c` and the identity cone morphism produces a 2-cell `f ⟶ w.lift c` whose
element at a test object and an apex object is a morphism of the iso-comma.
The comma square of that morphism says exactly that `c.commutes` is the
canonical structure isomorphism of `f` — i.e. it forces every cone with the
same two legs to be the canonical image cone.  `S2115SameLegsTwist` records
this rigidity property (as the S2099 twist with the identity projection
isomorphisms).  This is strictly stronger than the 2-universal property of the
iso-comma, which only requires the comparison to be full/essentially surjective
on the canonical image cones; it is the wrong target.  (The extraction from the
literal statement is described here and not formalized; the file does not
assume it.)

## Relation to the S2104 canonical twist

S2104 proves the twist for the *canonical* data (h = the witness lift, and
eX/eY = the witness comparisons).  That is the special case of
`S2115ImageConeTwoCellFull` for the identity cone morphism, and it is not the
datum needed for right cancellation: the comparison pair of
`S2115PastedComparisonTwist` is built from the pasted witness `wP`, not from
the upper witness, so the S2104 canonical twist does not supply it.  The twist
there is a genuine compatibility of the pasted witness with the upper square's
commutes cell.

## The exact first missing for right cancellation

`S2115PastedComparisonTwist` is the precise remaining 2-categorical datum for
the S2107 reduction in the actual butterfly configuration: for every cone `s`
over the lower square, the two canonical comparison cells of the pasted witness
(`S2107LiftToYIsoX` and `S2107LiftToYIsoY`) are compatible with the upper
square's commutes cell, i.e. they form a cone morphism from the image cone of
`wP.lift (E s) ; toY1` to `S2107Sq2ConeOf s`.

- `S2115PastedComparisonTwist_implies_twist` proves that this datum gives the
  S2099/S2096 projection twist for the comparison.
- `S2115PastedComparisonTwist_implies_liftIso` proves that, via S2101's
  site-level assembly, it gives the comparison
  `wP.lift (E s) ; toY1 ≅ (S2076Witness f g).lift (S2107Sq2ConeOf s)`.

This datum is not implied by the seven recorded fields of `wP` (nor by the
essential surjectivity of the pasted square): the weak witness only produces the
lift of a *cone*, not the compatibility of an arbitrary comparison pair with the
cone's structure cell.  It is the exact first missing statement; it is stated
here, its consequences are proved, and it is not assumed.

## Axiom footprint

Only `propext`, `Classical.choice` and `Quot.sound`; see the audit block.
No sorry, no new axiom, no fabricated 2-cell.
-/

import tmp.sheaf.xif.paper.S2107RightCancelActual
import tmp.sheaf.xif.paper.S2101SiteNaturalityActual
import tmp.sheaf.xif.paper.S2104ButterflyTwistActual
import tmp.sheaf.xif.paper.S2108PastedTransportActual
import tmp.sheaf.xif.paper.S2086ToAAssemblyActual
import tmp.sheaf.xif.paper.S2099BigSquareEssSurjActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2115UpperTwoCellFullActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1801LiftEssSurjActual
open LeanFormal.IUT.XiFPaper.S1827CloseRetractionActual
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1893PullbackUniversalActual
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2076IsoCommaTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S2086ToAAssemblyActual
open LeanFormal.IUT.XiFPaper.S2094FullUniversalInputsActual
open LeanFormal.IUT.XiFPaper.S2097BaseChangeButterflyActual
open LeanFormal.IUT.XiFPaper.S2099BigSquareEssSurjActual
open LeanFormal.IUT.XiFPaper.S2101SiteNaturalityActual
open LeanFormal.IUT.XiFPaper.S2104ButterflyTwistActual
open LeanFormal.IUT.XiFPaper.S2107RightCancelActual
open LeanFormal.IUT.XiFPaper.S2108PastedTransportActual

universe u

/-! ## 1. The image cone of the actual upper square and its commutes cell -/

section ImageCone

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)

/-- The actual upper square: the iso-comma square of S2076. -/
abbrev S2115UpperSquare : EtalePseudofunctorSquare
    (sitePseudofunctor f g) A.source.fiber B.source.fiber C.source.fiber :=
  S2076Square f g

/-- The recorded witness of the actual upper square. -/
abbrev S2115UpperWitness : (S2115UpperSquare f g).TwoPullbackWitness :=
  S2076Witness (f := f) (g := g)

/-- The image cone of a 1-cell into the apex of the actual upper square, in the
shape of S2107's `S2107ImageCone`. -/
abbrev S2115UpperImageCone {W : EtaleStackPseudofunctor S1726K}
    (u : Pseudofunctor.StrongTrans W (sitePseudofunctor f g)) :
    (S2115UpperSquare f g).Cone W :=
  S2107ImageCone (S2115UpperSquare f g) u

/-- **The commutes cell of the image cone is the structure isomorphism of the
iso-comma object.**  This is the compatibility behind the corrected upper-square
2-cell fullness: the associators are identities in `Cat`, and the middle
whiskered term is the canonical structure iso of the iso-comma. -/
theorem S2115ImageCone_commutes_app
    {W : EtaleStackPseudofunctor S1726K}
    (u : Pseudofunctor.StrongTrans W (sitePseudofunctor f g))
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    (x : ↑(W.obj U)) :
    ((S2115UpperImageCone f g u).commutes.hom.as.app U).toNatTrans.app x =
      (((u.app U).toFunctor.obj x)).obj.hom := by
  change ((S2058AssociatorIso u (S2115UpperSquare f g).toX
        (S2115UpperSquare f g).xToBase).hom.as.app U).toNatTrans.app x ≫
      ((S2058WhiskerLeftIso u
            ((S2115UpperSquare f g).toX.vcomp (S2115UpperSquare f g).xToBase)
            ((S2115UpperSquare f g).toY.vcomp (S2115UpperSquare f g).yToBase)
            (S2115UpperSquare f g).commutes).hom.as.app U).toNatTrans.app x ≫
        ((S2058AssociatorIso u (S2115UpperSquare f g).toY
              (S2115UpperSquare f g).yToBase).symm.hom.as.app U).toNatTrans.app x =
    (((u.app U).toFunctor.obj x)).obj.hom
  have hA : ((S2058AssociatorIso u (S2115UpperSquare f g).toX
        (S2115UpperSquare f g).xToBase).hom.as.app U).toNatTrans.app x = 𝟙 _ := by
    change (α_ (u.app U) ((S2115UpperSquare f g).toX.app U)
      ((S2115UpperSquare f g).xToBase.app U)).hom.toNatTrans.app x = _
    rw [Cat.associator_hom_app]
    rfl
  have hC : ((S2058AssociatorIso u (S2115UpperSquare f g).toY
        (S2115UpperSquare f g).yToBase).symm.hom.as.app U).toNatTrans.app x = 𝟙 _ := by
    change (α_ (u.app U) ((S2115UpperSquare f g).toY.app U)
      ((S2115UpperSquare f g).yToBase.app U)).inv.toNatTrans.app x = _
    rw [Cat.associator_inv_app]
    rfl
  have hM : ((S2058WhiskerLeftIso u
        ((S2115UpperSquare f g).toX.vcomp (S2115UpperSquare f g).xToBase)
        ((S2115UpperSquare f g).toY.vcomp (S2115UpperSquare f g).yToBase)
        (S2115UpperSquare f g).commutes).hom.as.app U).toNatTrans.app x =
      ((S2115UpperSquare f g).commutes.hom.as.app U).toNatTrans.app
        ((u.app U).toFunctor.obj x) := by
    rw [S2058WhiskerLeftIso_hom]
    change (Functor.whiskerLeft (u.app U).toFunctor
      ((S2115UpperSquare f g).commutes.hom.as.app U).toNatTrans).app x = _
    rw [Functor.whiskerLeft_app]
  have hcommutes : ∀ (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
      (x : ↑((sitePseudofunctor f g).obj U)),
      ((S2076Square f g).commutes.hom.as.app U).toNatTrans.app x = x.obj.hom := by
    intro U x
    change (S1836IsoCommaNatIso (f.map.app U).toFunctor
      (g.map.app U).toFunctor).hom.app x = x.obj.hom
    exact S1836IsoCommaNatIso_hom_app _ _
  rw [hA, hC, hM]
  simp only [Category.id_comp, Category.comp_id]
  exact hcommutes U ((u.app U).toFunctor.obj x)

end ImageCone

/-! ## 2. The twist of a cone morphism out of the image cone -/

section Twist

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
variable {W : EtaleStackPseudofunctor S1726K}
variable {u : Pseudofunctor.StrongTrans W (sitePseudofunctor f g)}
variable {c : (S2115UpperSquare f g).Cone W}

/-- The identity cone morphism. -/
noncomputable def S2115ConeId (c : (S2115UpperSquare f g).Cone W) :
    (S2115UpperSquare f g).ConeMorphism c c where
  toX := 𝟙 c.toX
  toY := 𝟙 c.toY
  compatibility := by
    change Bicategory.whiskerRight (𝟙 c.toX) (S2115UpperSquare f g).xToBase ≫ c.commutes.hom =
      c.commutes.hom ≫ Bicategory.whiskerRight (𝟙 c.toY) (S2115UpperSquare f g).yToBase
    rw [Bicategory.id_whiskerRight, Bicategory.id_whiskerRight]
    rw [Category.id_comp]
    exact (Category.comp_id c.commutes.hom).symm

/-- **A cone morphism out of the image cone has the S2099 twist.**  Its
compatibility square with the image cone's commutes cell is exactly the
fibre-level twist, by `S2115ImageCone_commutes_app`. -/
theorem S2115ImageConeTwistAt
    (eX : Iso (Pseudofunctor.StrongTrans.vcomp u (toA f g)) c.toX)
    (eY : Iso (Pseudofunctor.StrongTrans.vcomp u (toB f g)) c.toY)
    (m : (S2115UpperSquare f g).ConeMorphism (S2115UpperImageCone f g u) c)
    (hmX : m.toX = eX.hom) (hmY : m.toY = eY.hom)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    (x : ↑(W.obj U)) :
    S2099TwistAt f g c u eX eY U x := by
  have hm1 := congrArg (fun al => al.as.app U) m.compatibility
  have hm2 := congrArg (fun al => al.toNatTrans.app x) hm1
  have homComp_as : ∀ {F G : EtaleStackPseudofunctor S1726K} {a b c : F ⟶ G}
      (g1 : a ⟶ b) (g2 : b ⟶ c),
      (g1 ≫ g2).as = Pseudofunctor.StrongTrans.Modification.vcomp g1.as g2.as :=
    fun g1 g2 => rfl
  simp only [homComp_as, Pseudofunctor.StrongTrans.Modification.vcomp_app,
    Cat.Hom₂.comp_app, Pseudofunctor.StrongTrans.whiskerRight_as_app,
    Cat.whiskerRight_toNatTrans, Cat.whiskerRight_app] at hm2
  rw [S2115ImageCone_commutes_app] at hm2
  rw [hmX, hmY] at hm2
  change ((S2115UpperSquare f g).xToBase.app U).toFunctor.map
        ((eX.hom.as.app U).toNatTrans.app x) ≫
      (c.commutes.hom.as.app U).toNatTrans.app x =
    ((u.app U).toFunctor.obj x).obj.hom ≫
      ((S2115UpperSquare f g).yToBase.app U).toFunctor.map
        ((eY.hom.as.app U).toNatTrans.app x)
  exact hm2

end Twist

/-! ## 3. The corrected upper-square 2-cell fullness -/

section Fullness

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
variable {W : EtaleStackPseudofunctor S1726K}
variable {c : (S2115UpperSquare f g).Cone W}
variable {h : Pseudofunctor.StrongTrans W (sitePseudofunctor f g)}
variable {eX : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toX}
variable {eY : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toY}

/-- The componentwise S2099 twist is the natural-transformation-level S2096
projection compatibility used by S2101. -/
theorem S2115ProjectionCompat_of_twist
    (hTw : S2099Twist f g c h eX eY) :
    S2096ProjectionCompatibility f g (S2076ConeToGeneral (f := f) (g := g) c) h eX eY := by
  intro U
  apply NatTrans.ext
  funext x
  rw [NatTrans.comp_app, NatTrans.comp_app]
  rw [← Iso.app_hom, gConeAt_commutes_hom_app]
  change (Functor.whiskerRight (S2096HConeToA f g (S2076ConeToGeneral (f := f) (g := g) c) h eX U).hom
        (f.map.app U).toFunctor).app x ≫
      ((S2076ConeToGeneral (f := f) (g := g) c).commutes.hom.as.app U).toNatTrans.app x =
    (S1893ComparisonCommutes (f.map.app U).toFunctor (g.map.app U).toFunctor
        (h.app U).toFunctor).hom.app x ≫
      (Functor.whiskerRight (S2096HConeToB f g (S2076ConeToGeneral (f := f) (g := g) c) h eY U).hom
        (g.map.app U).toFunctor).app x
  rw [S1893ComparisonCommutes_hom_app]
  have h := hTw U x
  simp only [S2099TwistAt] at h
  exact h

/-- **The corrected upper-square 2-cell fullness.**  For the actual iso-comma
square, every pair of projection isomorphisms satisfying the S2099 twist is
realised by an isomorphism to the S2076 lift with exactly those projections.
This is the true form of the "upper-square 2-cell fullness": the twist is the
compatibility of the projections with the cone's structure cell, and it is
automatic for cone morphisms out of the canonical image cone (see
`S2115ImageConeTwistAt`). -/
theorem S2115UpperTwoCellFull :
    ∀ (c : (S2115UpperSquare f g).Cone W)
      (h : Pseudofunctor.StrongTrans W (sitePseudofunctor f g))
      (eX : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toX)
      (eY : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toY),
      S2099Twist f g c h eX eY →
      ∃ e : Iso h ((S2115UpperWitness f g).lift W c),
        Pseudofunctor.StrongTrans.whiskerRight e.hom (toA f g) =
            eX.hom ≫ ((S2115UpperWitness f g).liftToX W c).inv ∧
          Pseudofunctor.StrongTrans.whiskerRight e.hom (toB f g) =
            eY.hom ≫ ((S2115UpperWitness f g).liftToY W c).inv := by
  intro c h eX eY hTw
  have hcompat := S2115ProjectionCompat_of_twist f g hTw
  let e := S2096LiftUniq_of_projectionCompat (f := f) (g := g) c h eX eY hcompat
  refine ⟨e, ?_, ?_⟩
  · -- first projection equation
    apply Pseudofunctor.StrongTrans.Hom.ext
    apply Pseudofunctor.StrongTrans.Modification.ext
    funext U
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext x
    have hfst := S2096FibreIso_hom_fst_app (f := f) (g := g)
      (S2076ConeToGeneral (f := f) (g := g) c) h eX eY U (hcompat U) x
    -- evaluate the left-hand side as the first projection of the fibre iso
    have hL : ((Pseudofunctor.StrongTrans.whiskerRight e.hom (toA f g)).as.app U).toNatTrans.app x =
        (S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor).map
          ((S2096FibreIso (f := f) (g := g) (S2076ConeToGeneral (f := f) (g := g) c) h eX eY U (hcompat U)).hom.app x) := rfl
    rw [hL, hfst]
    -- right-hand side: the comparison is the identity on components
    rw [show (eX.hom ≫ ((S2115UpperWitness f g).liftToX W c).inv) =
      (eX.hom ≫ (gLiftToA (f := f) (g := g) (S2076ConeToGeneral (f := f) (g := g) c)).inv) from rfl]
    rw [show (((eX.hom ≫ (gLiftToA (f := f) (g := g) (S2076ConeToGeneral (f := f) (g := g) c)).inv).as.app U).toNatTrans.app x) =
      (eX.hom.as.app U).toNatTrans.app x by
      rw [show (eX.hom ≫ (gLiftToA (f := f) (g := g) (S2076ConeToGeneral (f := f) (g := g) c)).inv).as.app U =
        (eX.hom.as.app U ≫ (gLiftToA (f := f) (g := g) (S2076ConeToGeneral (f := f) (g := g) c)).inv.as.app U) from rfl]
      rw [Cat.Hom₂.comp_app, gLiftToA_inv_app_as]
      erw [Category.comp_id]]
    rfl
  · -- second projection equation
    apply Pseudofunctor.StrongTrans.Hom.ext
    apply Pseudofunctor.StrongTrans.Modification.ext
    funext U
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext x
    have hsnd := S2096FibreIso_hom_snd_app (f := f) (g := g)
      (S2076ConeToGeneral (f := f) (g := g) c) h eX eY U (hcompat U) x
    have hL : ((Pseudofunctor.StrongTrans.whiskerRight e.hom (toB f g)).as.app U).toNatTrans.app x =
        (S1836IsoCommaSnd (f.map.app U).toFunctor (g.map.app U).toFunctor).map
          ((S2096FibreIso (f := f) (g := g) (S2076ConeToGeneral (f := f) (g := g) c) h eX eY U (hcompat U)).hom.app x) := rfl
    rw [hL, hsnd]
    rw [show (eY.hom ≫ ((S2115UpperWitness f g).liftToY W c).inv) =
      (eY.hom ≫ (gLiftToB (f := f) (g := g) (S2076ConeToGeneral (f := f) (g := g) c)).inv) from rfl]
    rw [show (((eY.hom ≫ (gLiftToB (f := f) (g := g) (S2076ConeToGeneral (f := f) (g := g) c)).inv).as.app U).toNatTrans.app x) =
      (eY.hom.as.app U).toNatTrans.app x by
      rw [show (eY.hom ≫ (gLiftToB (f := f) (g := g) (S2076ConeToGeneral (f := f) (g := g) c)).inv).as.app U =
        (eY.hom.as.app U ≫ (gLiftToB (f := f) (g := g) (S2076ConeToGeneral (f := f) (g := g) c)).inv.as.app U) from rfl]
      rw [Cat.Hom₂.comp_app, gLiftToB_inv_app_as]
      erw [Category.comp_id]]
    rfl

end Fullness

/-! ## 4. The literal S1801 statement, its rigidity content, and the exact first
missing of the right-cancellation reduction -/

section LiteralAndMissing

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)

/-- The literal S1801 `TwoCellSurjTo` for the actual upper square and the S2076
witness.  Note that its cone `c'` is an *arbitrary* cone whose two legs happen to
equal those of `f`; nothing constrains `c'.commutes`. -/
def S2115LiteralUpperTwoCellSurjTo : Prop :=
  S1801TwoCellSurjTo (F := S1726K) (sq := S2115UpperSquare f g)
    (S2115UpperWitness f g)

/-- **The commutes-rigidity content of the literal S1801 statement.**  For every
cone `c` over the actual upper square whose two legs are those of `h`, the
commutes cell of `c` must be the canonical structure isomorphism of `h` at
every test object and apex object.  This is expressed as the S2099 twist with
the identity projection isomorphisms. -/
def S2115SameLegsTwist : Prop :=
  ∀ {W : EtaleStackPseudofunctor S1726K}
    (c : (S2115UpperSquare f g).Cone W)
    (h : Pseudofunctor.StrongTrans W (sitePseudofunctor f g))
    (hX : c.toX = Pseudofunctor.StrongTrans.vcomp h (toA f g))
    (hY : c.toY = Pseudofunctor.StrongTrans.vcomp h (toB f g))
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (x : ↑(W.obj U)),
    S2099TwistAt f g c h (eqToIso hX.symm) (eqToIso hY.symm) U x

/-- The two projection 2-cells of a cone morphism out of the canonical image
cone, for the pasted comparison.  These are the comparison isomorphisms of
S2107, read as 2-cells into the cone `S2107Sq2ConeOf`. -/
abbrev S2115PastedAlpha (D : S2058Pasting (F := S1726K))
    (wP : D.squareP.TwoPullbackWitness) {W : EtaleStackPseudofunctor S1726K}
    (s : D.square1.Cone W) :
    Iso (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S2107ExtLift D wP s) D.toY1) D.xi)
      (S2107Sq2ConeOf D s).toX :=
  S2107LiftToYIsoX D wP s

/-- The second projection 2-cell of the pasted comparison. -/
abbrev S2115PastedBeta (D : S2058Pasting (F := S1726K))
    (wP : D.squareP.TwoPullbackWitness) {W : EtaleStackPseudofunctor S1726K}
    (s : D.square1.Cone W) :
    Iso (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S2107ExtLift D wP s) D.toY1) D.toY2)
      (S2107Sq2ConeOf D s).toY :=
  S2107LiftToYIsoY D wP s

/-- **The exact first missing datum of the right-cancellation reduction, in the
actual butterfly configuration.**  For every cone `s` over the lower square, the
two canonical comparison cells of the pasted witness are compatible with the
upper square's commutes cell: they form a cone morphism from the image cone of
`wP.lift (E s) ; toY1` to `S2107Sq2ConeOf s`.

The two 2-cells are explicitly `S2107LiftToYIsoX` and `S2107LiftToYIsoY`; the
equation is precisely their cone-morphism compatibility.  It is *not* a
consequence of the seven recorded fields of `wP` (nor of the essential
surjectivity of the pasted square), and it is the missing input of the S2107
reduction. -/
def S2115PastedComparisonTwist : Prop :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (Pg : EtaleStackBaseChangePresentation g.map T (S2086PointC f ptA))
    (wP : (S2097Pasting f g T ptA Pg).squareP.TwoPullbackWitness)
    (W : EtaleStackPseudofunctor S1726K)
    (s : (S2097Pasting f g T ptA Pg).square1.Cone W),
    let D := S2097Pasting f g T ptA Pg
    Pseudofunctor.StrongTrans.whiskerRight (S2107LiftToYIsoX D wP s).hom D.x2 ≫
        (S2107Sq2ConeOf D s).commutes.hom =
      (S2107ImageCone D.square2
          (Pseudofunctor.StrongTrans.vcomp (S2107ExtLift D wP s) D.toY1)).commutes.hom ≫
        Pseudofunctor.StrongTrans.whiskerRight (S2107LiftToYIsoY D wP s).hom D.y2

/-- **The exact first missing implies the projection twist of the pasted
comparison.**  This is the S2099/S2096 twist for the pair of comparison cells,
hence by S2101 the comparison `wP.lift (E s) ; toY1 ≅ s.toY` exists. -/
theorem S2115PastedComparisonTwist_implies_twist
    (h : S2115PastedComparisonTwist)
    (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (Pg : EtaleStackBaseChangePresentation g.map T (S2086PointC f ptA))
    (wP : (S2097Pasting f g T ptA Pg).squareP.TwoPullbackWitness)
    (W : EtaleStackPseudofunctor S1726K)
    (s : (S2097Pasting f g T ptA Pg).square1.Cone W) :
    let D := S2097Pasting f g T ptA Pg
    S2099Twist f g (S2107Sq2ConeOf D s)
      (Pseudofunctor.StrongTrans.vcomp (S2107ExtLift D wP s) D.toY1)
      (S2115PastedAlpha D wP s) (S2115PastedBeta D wP s) := by
  intro D U x
  have hcompat := h A B C f g T ptA Pg wP W s
  change Pseudofunctor.StrongTrans.whiskerRight (S2115PastedAlpha D wP s).hom D.x2 ≫
      (S2107Sq2ConeOf D s).commutes.hom =
    (S2107ImageCone D.square2
        (Pseudofunctor.StrongTrans.vcomp (S2107ExtLift D wP s) D.toY1)).commutes.hom ≫
      Pseudofunctor.StrongTrans.whiskerRight (S2115PastedBeta D wP s).hom D.y2 at hcompat
  let m : (S2115UpperSquare f g).ConeMorphism
      (S2115UpperImageCone f g
        (Pseudofunctor.StrongTrans.vcomp (S2107ExtLift D wP s) D.toY1))
      (S2107Sq2ConeOf D s) :=
    { toX := (S2115PastedAlpha D wP s).hom
      toY := (S2115PastedBeta D wP s).hom
      compatibility := hcompat }
  exact S2115ImageConeTwistAt f g (S2115PastedAlpha D wP s) (S2115PastedBeta D wP s)
    m rfl rfl U x

end LiteralAndMissing



/-! ## 5. The corrected fullness in S1801 shape, and the consumer of the exact
missing datum -/

section Consequences

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)

/-- **The corrected upper-square 2-cell fullness in S1801 shape.**  A cone
morphism out of the canonical image cone, whose two components are isomorphisms,
is realised by an isomorphism to the S2076 lift with exactly the prescribed
whiskerings.  The commutes cell of the image cone is the structure isomorphism
(`S2115ImageCone_commutes_app`), so the twist is automatic and
`S2115UpperTwoCellFull` applies. -/
theorem S2115ImageConeTwoCellFull
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2115UpperSquare f g).Cone W)
    (h : Pseudofunctor.StrongTrans W (sitePseudofunctor f g))
    (eX : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toX)
    (eY : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toY)
    (m : (S2115UpperSquare f g).ConeMorphism
      (S2115UpperImageCone f g h) c)
    (hmX : m.toX = eX.hom) (hmY : m.toY = eY.hom) :
    ∃ e : Iso h ((S2115UpperWitness f g).lift W c),
      Pseudofunctor.StrongTrans.whiskerRight e.hom (toA f g) =
          m.toX ≫ ((S2115UpperWitness f g).liftToX W c).inv ∧
        Pseudofunctor.StrongTrans.whiskerRight e.hom (toB f g) =
          m.toY ≫ ((S2115UpperWitness f g).liftToY W c).inv := by
  have hTw : S2099Twist f g c h eX eY := fun U x =>
    S2115ImageConeTwistAt f g eX eY m hmX hmY U x
  obtain ⟨e, heX, heY⟩ := S2115UpperTwoCellFull f g c h eX eY hTw
  refine ⟨e, ?_, ?_⟩
  · rw [heX, hmX]
  · rw [heY, hmY]

/-- **The exact first missing datum gives the toY comparison.**  Under the
pasted-comparison twist, the canonical comparison `wP.lift (E s) ; toY1` is
isomorphic to the S2076 lift of the upper cone `S2107Sq2ConeOf s`, via S2101's
site-level assembly. -/
theorem S2115PastedComparisonTwist_implies_liftIso
    (h : S2115PastedComparisonTwist)
    (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (Pg : EtaleStackBaseChangePresentation g.map T (S2086PointC f ptA))
    (wP : (S2097Pasting f g T ptA Pg).squareP.TwoPullbackWitness)
    (W : EtaleStackPseudofunctor S1726K)
    (s : (S2097Pasting f g T ptA Pg).square1.Cone W) :
    let D := S2097Pasting f g T ptA Pg
    Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp (S2107ExtLift D wP s) D.toY1)
      ((S2076Witness (f := f) (g := g)).lift W (S2107Sq2ConeOf D s))) := by
  intro D
  have hTw := S2115PastedComparisonTwist_implies_twist h A B C f g T ptA Pg wP W s
  have hcompat := S2115ProjectionCompat_of_twist f g
    (c := S2107Sq2ConeOf D s) (h := Pseudofunctor.StrongTrans.vcomp
      (S2107ExtLift D wP s) D.toY1) hTw
  exact ⟨S2096LiftUniq_of_projectionCompat (f := f) (g := g)
    (S2107Sq2ConeOf D s)
    (Pseudofunctor.StrongTrans.vcomp (S2107ExtLift D wP s) D.toY1)
    (S2115PastedAlpha D wP s) (S2115PastedBeta D wP s) hcompat⟩

end Consequences

/-! ## 6. Checks and axiom audit -/

#check @S2115ImageCone_commutes_app
#check @S2115ConeId
#check @S2115ImageConeTwistAt
#check @S2115ProjectionCompat_of_twist
#check @S2115UpperTwoCellFull
#check @S2115ImageConeTwoCellFull
#check S2115LiteralUpperTwoCellSurjTo
#check S2115SameLegsTwist
#check @S2115PastedComparisonTwist
#check @S2115PastedComparisonTwist_implies_twist
#check @S2115PastedComparisonTwist_implies_liftIso

#print axioms S2115ImageCone_commutes_app
#print axioms S2115ConeId
#print axioms S2115ImageConeTwistAt
#print axioms S2115ProjectionCompat_of_twist
#print axioms S2115UpperTwoCellFull
#print axioms S2115ImageConeTwoCellFull
#print axioms S2115PastedComparisonTwist_implies_twist
#print axioms S2115PastedComparisonTwist_implies_liftIso



end LeanFormal.IUT.XiFPaper.S2115UpperTwoCellFullActual
