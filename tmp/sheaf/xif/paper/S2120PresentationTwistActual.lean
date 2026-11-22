/-
# S2120: cone-category essential surjectivity, 2-cell fullness, and the
# strong-presentation twist

## Context

S2118 reduced the right-cancellation target of the butterfly reduction to the
presentation twist `S2118PresentationTwist`: for the actual presentation
`Pg : EtaleStackBaseChangePresentation g.map T (S2086PointC f ptA)`, the two
recorded comparison 2-cells of `Pg.isPullback` must form a cone morphism from
the image cone of the presentation lift to the transported cone
`S2118Conv`.  S2118 proved that the S2108 transport is definitionally
transparent and recorded that the twist is not derivable from the seven fields
of `TwoPullbackWitness`.  The remaining question addressed here is whether the
*strong* presentation of S1852, i.e. the weak presentation together with the
full cone essential surjectivity `S1852ConeEssSurj`, supplies the twist.

## The result: conditionally proved, with the exact missing API

This file formalizes the implication

  cone-category essential surjectivity + cone-category 2-cell fullness
    + representability of the presentation apex
      ==> the strong-presentation twist.

Concretely:

1. `S2120StrongPresentationTwist` is the strong-presentation version of
   `S2118PresentationTwist`: the S2118 twist at `Pg.toWeak` for
   `Pg : StrongEtaleStackBaseChangePresentation`.  It is proved to follow from
   the unrestricted `S2118PresentationTwist` (`S2120StrongPresentationTwist_of_S2118`).

2. `S2120LiftConeMor sq w` is the **cone-category essential-surjectivity half
   at the recorded lift**: for every cone `c` there is a cone morphism from
   the image cone of `w.lift W c` to `c`.  This is the counit of the cone
   comparison, i.e. the part of "the cone comparison is essentially surjective"
   that produces a cone *morphism* (not just an isomorphism of the two legs).

3. `S2120TwistAt_of_coneMor_and_twoCellFull` / 
   `S2120Twist_of_liftConeMor_and_twoCellFull`: given such a cone morphism and
   the **cone-category 2-cell fullness** `S1801TwoCellSurjTo` (every cone
   morphism from an image cone is realised by a 2-cell with the prescribed
   projections), the recorded comparisons are forced to be the components of
   the cone morphism, and the twist follows.  The proof uses that the apex
   `Y(Pg.pullbackScheme)` is representable, hence modifications into it are
   subsingleton (`S1827SubsingletonModRep`), so the 2-cell produced by
   fullness is the identity.

4. `S2120PresentationLiftConeMor` and `S2120PresentationTwoCellFull` are the
   two statements instantiated at the presentation squares of strong
   presentations; together they are the precise first missing
   (`S2120FirstMissing`).  `S2120StrongPresentationTwist_of_firstMissing`
   proves the strong twist from them.

5. `S2120PresentationLiftConeMor_of_strongTwist` proves the converse direction
   for the first component: the strong twist gives the cone morphism.  Hence,
   modulo the 2-cell fullness, the strong twist is *equivalent* to the
   existence of the cone morphism at the transported cones.

6. `S2120StrongPresentationTwist_for_strongTwoFullData` instantiates the result
   at the `strongPresentation` field of S2110's `S2110StrongTwoFullData`,
   which is the actual consumer interface.

## Why `S1852ConeEssSurj` alone is not enough

`S1852ConeEssSurj` is 1-cell essential surjectivity: for a cone `c` and a
1-cell `f` with *given* projection isomorphisms it produces an isomorphism
`f ≅ w.lift c`.  At the twist data (`f := w.lift W c`, projections
`w.liftToX` and `w.liftToY`) its conclusion is an endomorphism isomorphism of
`w.lift W c`; `S2120ConeEssSurj_twistData_trivial` shows this type is
inhabited with no hypothesis at all, while
`S2120ConeEssSurj_twistData_instance` shows it is exactly what the strong field
returns.  So the strong field carries no information about the *compatibility*
of the recorded comparison 2-cells with the structure cell: the twist is a
2-cell-level coherence, not the existence of an isomorphism.  The same boundary
is recorded by S2099/S2104/S2115 at the iso-comma square and by S2118 at the
presentation square.  The precise missing data are therefore:

* `S2120PresentationLiftConeMor`: the counit half of the cone-category
  essential surjectivity (a cone morphism from the image cone of the lift);
* `S2120PresentationTwoCellFull`: the cone-category 2-cell fullness
  `S1801TwoCellSurjTo` of the presentation witness.

Neither is among the recorded fields: S1801 records that the weak fields do not
export the 2-cell surjectivity, and S2118 records that the recorded fields contain
no equation relating `liftToX` and `liftToY` (hence no cone morphism with the
recorded comparisons).  Neither is among the fields of
`StrongEtaleStackBaseChangePresentation` (which records only
`S1852ConeEssSurj` on top of the weak witness).  This file
does not construct a countermodel inside the cover situation, and it does not
assume either statement as an axiom: they are named hypotheses, and their exact
consequences are proved.

## Honest boundary

No `sorry`, no new axiom, no fabricated witness, no change to
`EtaleStackBaseChangePresentation` or to any other recorded definition.
`S2120StrongPresentationTwist` is **not** proved unconditionally.  The file
proves it from the two named missing APIs and proves that the first of them is
necessary.  Axiom footprint: `propext`, `Classical.choice`, `Quot.sound`.
-/

import tmp.sheaf.xif.paper.S2118PastedComparisonTwistActual
import tmp.sheaf.xif.paper.S1852CoherentCoverActual
import tmp.sheaf.xif.paper.S1801LiftEssSurjActual
import tmp.sheaf.xif.paper.S1827CloseRetractionActual
import tmp.sheaf.xif.paper.S2110StrongTwoFullInputsActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2120PresentationTwistActual

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
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S2076IsoCommaTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S2086ToAAssemblyActual
open LeanFormal.IUT.XiFPaper.S2097BaseChangeButterflyActual
open LeanFormal.IUT.XiFPaper.S2107RightCancelActual
open LeanFormal.IUT.XiFPaper.S2110StrongTwoFullInputsActual
open LeanFormal.IUT.XiFPaper.S2115UpperTwoCellFullActual
open LeanFormal.IUT.XiFPaper.S2118PastedComparisonTwistActual

universe u

/-! ## 1. The strong-presentation version of the S2118 twist -/

/-- **The strong-presentation twist.**  The S2118 presentation twist at
`Pg.toWeak`, for a strong presentation `Pg` (the weak presentation together
with `S1852ConeEssSurj`).  This is the "strong presentation version" of
`S2118PresentationTwist`; the recorded definition
`EtaleStackBaseChangePresentation` is not changed. -/
def S2120StrongPresentationTwist : Prop :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (Pg : StrongEtaleStackBaseChangePresentation g.map T (S2086PointC f ptA))
    (W : EtaleStackPseudofunctor S1726K)
    (s : (S2097Pasting f g T ptA Pg.toWeak).square1.Cone W),
    let c0 := S2118Conv f g T ptA Pg.toWeak s
    Pseudofunctor.StrongTrans.whiskerRight (Pg.toWeak.isPullback.liftToX W c0).hom g.map ≫
        c0.commutes.hom =
      (S2107ImageCone (S2118PresentationSquare f g T ptA Pg.toWeak)
          (Pg.toWeak.isPullback.lift W c0)).commutes.hom ≫
        Pseudofunctor.StrongTrans.whiskerRight (Pg.toWeak.isPullback.liftToY W c0).hom
          (Pseudofunctor.StrongTrans.vcomp ptA f.map)

/-- The unrestricted S2118 presentation twist implies the strong-presentation
twist: instantiate it at the weak image of the strong presentation. -/
theorem S2120StrongPresentationTwist_of_S2118 (h : S2118PresentationTwist) :
    S2120StrongPresentationTwist := by
  intro A B C f g T ptA Pg W s
  exact h A B C f g T ptA Pg.toWeak W s

/-! ## 2. The generic cone-comparison criterion

The twist at a cone `c` is the compatibility equation of the recorded
comparisons.  It is exactly the compatibility field of a cone morphism whose
components are the recorded comparisons.  The following definitions isolate the
two inputs needed to *produce* such a cone morphism from the universal property.
-/

/-- **The cone-category essential-surjectivity half at the recorded lift.**  For
every cone `c` there is a cone morphism from the image cone of the recorded
lift `w.lift W c` to `c`.  This is the counit of the cone comparison: the
object-level part of essential surjectivity that produces a cone morphism (not
merely an isomorphism of the two legs). -/
def S2120LiftConeMor {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness) : Prop :=
  ∀ (W : EtaleStackPseudofunctor S1726K) (c : sq.Cone W),
    Nonempty (sq.ConeMorphism (S2107ImageCone sq (w.lift W c)) c)

/-- The conjunction of the two cone-category inputs: the lift cone morphism and
the 2-cell fullness `S1801TwoCellSurjTo`. -/
def S2120ConeComparisonCoherent {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness) : Prop :=
  S2120LiftConeMor sq w ∧ S1801TwoCellSurjTo (F := S1726K) w

/-- In a category, an arrow whose composite with the inverse of an isomorphism
is an identity is the isomorphism itself.  (Bookkeeping used to compare the
components of the cone morphism with the recorded comparisons.) -/
theorem S2120_eq_hom_of_comp_inv_eq_id {C : Type*} [Category C] {A B : C}
    (a : A ⟶ B) (e : A ≅ B) (h : a ≫ e.inv = 𝟙 A) : a = e.hom := by
  calc a = a ≫ 𝟙 B := (Category.comp_id a).symm
    _ = a ≫ (e.inv ≫ e.hom) := by rw [Iso.inv_hom_id]
    _ = (a ≫ e.inv) ≫ e.hom := by rw [Category.assoc]
    _ = 𝟙 A ≫ e.hom := by rw [h]
    _ = e.hom := Category.id_comp e.hom

/-- The component of the identity modification whiskered on the right is the
identity. -/
theorem S2120_whiskerRight_ident_aux {P X : EtaleStackPseudofunctor S1726K}
    {W : EtaleStackPseudofunctor S1726K}
    (l : Pseudofunctor.StrongTrans W P)
    (F : Pseudofunctor.StrongTrans P X)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    (Pseudofunctor.StrongTrans.whiskerRight (𝟙 l) F).as.app U
      = 𝟙 (l.app U ≫ F.app U) := by
  have hid : (𝟙 l : Pseudofunctor.StrongTrans.Hom l l)
      = ⟨Pseudofunctor.StrongTrans.Modification.id l⟩ := rfl
  rw [hid]
  change (((⟨Pseudofunctor.StrongTrans.Modification.id l⟩ :
    Pseudofunctor.StrongTrans.Hom l l).as.app U) ▷ (F.app U))
      = 𝟙 (l.app U ≫ F.app U)
  rw [show ((⟨Pseudofunctor.StrongTrans.Modification.id l⟩ :
    Pseudofunctor.StrongTrans.Hom l l).as.app U) = 𝟙 (l.app U) from rfl]
  rw [id_whiskerRight]

/-- Right whiskering of the identity modification by a strong transformation is
the identity modification. -/
theorem S2120_whiskerRight_ident {P X : EtaleStackPseudofunctor S1726K}
    {W : EtaleStackPseudofunctor S1726K}
    (l : Pseudofunctor.StrongTrans W P)
    (F : Pseudofunctor.StrongTrans P X) :
    Pseudofunctor.StrongTrans.whiskerRight (𝟙 l) F =
      𝟙 (Pseudofunctor.StrongTrans.vcomp l F) := by
  apply Pseudofunctor.StrongTrans.Hom.ext
  apply Pseudofunctor.StrongTrans.Modification.ext
  funext U
  rw [show (Pseudofunctor.StrongTrans.whiskerRight (𝟙 l) F).as.app U
      = 𝟙 (l.app U ≫ F.app U) from S2120_whiskerRight_ident_aux l F U]
  conv_rhs =>
    rw [show (𝟙 (Pseudofunctor.StrongTrans.vcomp l F))
      = (⟨Pseudofunctor.StrongTrans.Modification.id
          (Pseudofunctor.StrongTrans.vcomp l F)⟩ :
          Pseudofunctor.StrongTrans.Hom (Pseudofunctor.StrongTrans.vcomp l F)
            (Pseudofunctor.StrongTrans.vcomp l F)) from rfl]
  rfl

/-- **The twist gives the cone-category essential-surjectivity half.**  The
recorded comparisons form a cone morphism exactly when the twist holds. -/
theorem S2120LiftConeMor_of_twist {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness)
    (htw : ∀ (W : EtaleStackPseudofunctor S1726K) (c : sq.Cone W),
      Pseudofunctor.StrongTrans.whiskerRight (w.liftToX W c).hom sq.xToBase ≫ c.commutes.hom =
        (S2107ImageCone sq (w.lift W c)).commutes.hom ≫
          Pseudofunctor.StrongTrans.whiskerRight (w.liftToY W c).hom sq.yToBase) :
    S2120LiftConeMor sq w := by
  intro W c
  exact ⟨{ toX := (w.liftToX W c).hom
           toY := (w.liftToY W c).hom
           compatibility := htw W c }⟩

/-- **The core theorem: cone-category essential surjectivity and 2-cell fullness
give the twist.**  For a cone `c`, a cone morphism `m` from the image cone of
the recorded lift, and the 2-cell fullness `S1801TwoCellSurjTo`, the recorded
comparison 2-cells of the witness are exactly the components of `m`; hence
`m`'s compatibility equation *is* the twist.

The representability hypothesis `hsub` ("all parallel 2-cells into the apex
`P` are equal") is automatic for the presentation square, whose apex is the
representable stack `Y(Pg.pullbackScheme)` (`S1827SubsingletonModRep`). -/
theorem S2120TwistAt_of_coneMor_and_twoCellFull
    {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z)
    (w : sq.TwoPullbackWitness)
    (hsub : ∀ {W : EtaleStackPseudofunctor S1726K}
      (a b : Pseudofunctor.StrongTrans W P), Subsingleton (a ⟶ b))
    {W : EtaleStackPseudofunctor S1726K} (c : sq.Cone W)
    (hMor : Nonempty (sq.ConeMorphism (S2107ImageCone sq (w.lift W c)) c))
    (hFull : S1801TwoCellSurjTo (F := S1726K) w) :
    Pseudofunctor.StrongTrans.whiskerRight (w.liftToX W c).hom sq.xToBase ≫ c.commutes.hom =
      (S2107ImageCone sq (w.lift W c)).commutes.hom ≫
        Pseudofunctor.StrongTrans.whiskerRight (w.liftToY W c).hom sq.yToBase := by
  obtain ⟨m⟩ := hMor
  obtain ⟨u, huX, huY⟩ := hFull W c (S2107ImageCone sq (w.lift W c)) (w.lift W c) m rfl rfl
  have hu : u = 𝟙 (w.lift W c) :=
    @Subsingleton.elim _ (hsub (w.lift W c) (w.lift W c)) _ _
  have hXeq : m.toX = (w.liftToX W c).hom := by
    have h := huX
    rw [hu] at h
    rw [S2120_whiskerRight_ident] at h
    simp only [eqToHom_refl, Category.id_comp] at h
    exact S2120_eq_hom_of_comp_inv_eq_id m.toX (w.liftToX W c) (h.symm)
  have hYeq : m.toY = (w.liftToY W c).hom := by
    have h := huY
    rw [hu] at h
    rw [S2120_whiskerRight_ident] at h
    simp only [eqToHom_refl, Category.id_comp] at h
    exact S2120_eq_hom_of_comp_inv_eq_id m.toY (w.liftToY W c) (h.symm)
  rw [← hXeq, ← hYeq]
  exact m.compatibility

/-- The all-cones form of `S2120TwistAt_of_coneMor_and_twoCellFull`. -/
theorem S2120Twist_of_liftConeMor_and_twoCellFull
    {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z)
    (w : sq.TwoPullbackWitness)
    (hsub : ∀ {W : EtaleStackPseudofunctor S1726K}
      (a b : Pseudofunctor.StrongTrans W P), Subsingleton (a ⟶ b))
    (hMor : S2120LiftConeMor sq w)
    (hFull : S1801TwoCellSurjTo (F := S1726K) w) :
    ∀ (W : EtaleStackPseudofunctor S1726K) (c : sq.Cone W),
      Pseudofunctor.StrongTrans.whiskerRight (w.liftToX W c).hom sq.xToBase ≫ c.commutes.hom =
        (S2107ImageCone sq (w.lift W c)).commutes.hom ≫
          Pseudofunctor.StrongTrans.whiskerRight (w.liftToY W c).hom sq.yToBase :=
  fun W c => S2120TwistAt_of_coneMor_and_twoCellFull sq w hsub c (hMor W c) hFull

/-! ## 3. The two missing APIs at the presentation squares -/

/-- **First missing API (cone-category essential surjectivity at the recorded
lift).**  For every strong presentation and every transported cone `c0`, there
is a cone morphism from the image cone of the presentation lift to `c0`.

This is *not* among the recorded fields of `TwoPullbackWitness` (which contain
no equation between `liftToX` and `liftToY`) and it is *not* the content of
`S1852ConeEssSurj` (which produces an isomorphism of the lift, not a cone
morphism).  It is the counit half of the cone-comparison equivalence. -/
def S2120PresentationLiftConeMor : Prop :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (Pg : StrongEtaleStackBaseChangePresentation g.map T (S2086PointC f ptA))
    (W : EtaleStackPseudofunctor S1726K)
    (s : (S2097Pasting f g T ptA Pg.toWeak).square1.Cone W),
    Nonempty ((S2118PresentationSquare f g T ptA Pg.toWeak).ConeMorphism
      (S2107ImageCone (S2118PresentationSquare f g T ptA Pg.toWeak)
        (Pg.toWeak.isPullback.lift W (S2118Conv f g T ptA Pg.toWeak s)))
      (S2118Conv f g T ptA Pg.toWeak s))

/-- **Second missing API (cone-category 2-cell fullness).**  The S1801
`TwoCellSurjTo` fullness for the recorded witness of every strong presentation.
This is exactly the API that pins the components of any cone morphism out of an
image cone to the recorded comparisons. -/
def S2120PresentationTwoCellFull : Prop :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (Pg : StrongEtaleStackBaseChangePresentation g.map T (S2086PointC f ptA)),
    S1801TwoCellSurjTo (F := S1726K) Pg.toWeak.isPullback

/-- **The precise first missing datum**: the conjunction of the cone-category
essential-surjectivity half at the lift and the 2-cell fullness, for all strong
presentations.  Both components are strictly stronger than the recorded
`S1852ConeEssSurj`; neither is assumed as an axiom. -/
def S2120FirstMissing : Prop :=
  S2120PresentationLiftConeMor ∧ S2120PresentationTwoCellFull

/-- **The strong-presentation twist from the two missing cone-category APIs.**
The representability of the apex `Y(Pg.pullbackScheme)` supplies the
subsingleton-2-cell hypothesis of the core theorem. -/
theorem S2120StrongPresentationTwist_of_firstMissing (h : S2120FirstMissing) :
    S2120StrongPresentationTwist := by
  intro A B C f g T ptA Pg W s
  exact S2120TwistAt_of_coneMor_and_twoCellFull
    (S2118PresentationSquare f g T ptA Pg.toWeak) Pg.toWeak.isPullback
    (fun a b => S1827SubsingletonModRep a b)
    (S2118Conv f g T ptA Pg.toWeak s)
    (h.1 A B C f g T ptA Pg W s) (h.2 A B C f g T ptA Pg)

/-- **Necessity of the first missing component.**  The strong twist produces the
cone morphism from the image cone of the lift to the transported cone.  Hence,
modulo the 2-cell fullness, the strong twist is equivalent to the existence of
that cone morphism. -/
theorem S2120PresentationLiftConeMor_of_strongTwist
    (h : S2120StrongPresentationTwist) : S2120PresentationLiftConeMor := by
  intro A B C f g T ptA Pg W s
  exact ⟨{ toX := (Pg.toWeak.isPullback.liftToX W
              (S2118Conv f g T ptA Pg.toWeak s)).hom
           toY := (Pg.toWeak.isPullback.liftToY W
              (S2118Conv f g T ptA Pg.toWeak s)).hom
           compatibility := h A B C f g T ptA Pg W s }⟩

/-- **Consumer form at S2110's strong input.**  The strong presentation selected
by the `strongPresentation` field of `S2110StrongTwoFullData` satisfies the
twist, given the two missing cone-category APIs.  This is the interface used by
the S2110 strong butterfly reduction. -/
theorem S2120StrongPresentationTwist_for_strongTwoFullData
    (h : S2120FirstMissing) (D : S2110StrongTwoFullData)
    (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (W : EtaleStackPseudofunctor S1726K)
    (s : (S2097Pasting f g T ptA
      (D.strongPresentation A B C f g T ptA).toWeak).square1.Cone W) :
    let c0 := S2118Conv f g T ptA (D.strongPresentation A B C f g T ptA).toWeak s
    Pseudofunctor.StrongTrans.whiskerRight
        ((D.strongPresentation A B C f g T ptA).toWeak.isPullback.liftToX W c0).hom g.map ≫
        c0.commutes.hom =
      (S2107ImageCone (S2118PresentationSquare f g T ptA
          (D.strongPresentation A B C f g T ptA).toWeak)
          ((D.strongPresentation A B C f g T ptA).toWeak.isPullback.lift W c0)).commutes.hom ≫
        Pseudofunctor.StrongTrans.whiskerRight
          ((D.strongPresentation A B C f g T ptA).toWeak.isPullback.liftToY W c0).hom
          (Pseudofunctor.StrongTrans.vcomp ptA f.map) :=
  S2120StrongPresentationTwist_of_firstMissing h
    A B C f g T ptA (D.strongPresentation A B C f g T ptA) W s

/-! ## 4. Why `S1852ConeEssSurj` alone carries no comparison coherence -/

/-- The conclusion of cone essential surjectivity at the twist data: at the cone
`c` and the 1-cell `w.lift W c` with the recorded projections, it is an
endomorphism isomorphism of the lift.  This type is inhabited with **no
hypothesis at all**. -/
theorem S2120ConeEssSurj_twistData_trivial
    {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness)
    (W : EtaleStackPseudofunctor S1726K) (c : sq.Cone W) :
    Nonempty (Iso (w.lift W c) (w.lift W c)) :=
  ⟨Iso.refl _⟩

/-- The strong field `S1827EssSurjOf` (`S1852ConeEssSurj` in square form),
instantiated at exactly the twist data, returns precisely the trivially
inhabited conclusion of `S2120ConeEssSurj_twistData_trivial`.  In particular the
strong field carries no information about the compatibility of
`w.liftToX`/`w.liftToY` with the cone's structure cell. -/
theorem S2120ConeEssSurj_twistData_instance
    {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness)
    (h : S1827EssSurjOf sq w)
    (W : EtaleStackPseudofunctor S1726K) (c : sq.Cone W) :
    Nonempty (Iso (w.lift W c) (w.lift W c)) :=
  h W c (w.lift W c) ⟨w.liftToX W c⟩ ⟨w.liftToY W c⟩

/-! ## 5. Checks and axiom audit -/

#check @S2120StrongPresentationTwist
#check S2120StrongPresentationTwist_of_S2118
#check @S2120LiftConeMor
#check @S2120ConeComparisonCoherent
#check @S2120LiftConeMor_of_twist
#check @S2120TwistAt_of_coneMor_and_twoCellFull
#check @S2120Twist_of_liftConeMor_and_twoCellFull
#check S2120PresentationLiftConeMor
#check S2120PresentationTwoCellFull
#check S2120FirstMissing
#check S2120StrongPresentationTwist_of_firstMissing
#check S2120PresentationLiftConeMor_of_strongTwist
#check S2120StrongPresentationTwist_for_strongTwoFullData
#check @S2120ConeEssSurj_twistData_trivial
#check @S2120ConeEssSurj_twistData_instance

#print axioms S2120StrongPresentationTwist_of_S2118
#print axioms S2120LiftConeMor_of_twist
#print axioms S2120TwistAt_of_coneMor_and_twoCellFull
#print axioms S2120Twist_of_liftConeMor_and_twoCellFull
#print axioms S2120StrongPresentationTwist_of_firstMissing
#print axioms S2120PresentationLiftConeMor_of_strongTwist
#print axioms S2120StrongPresentationTwist_for_strongTwoFullData
#print axioms S2120ConeEssSurj_twistData_trivial
#print axioms S2120ConeEssSurj_twistData_instance

end LeanFormal.IUT.XiFPaper.S2120PresentationTwistActual
