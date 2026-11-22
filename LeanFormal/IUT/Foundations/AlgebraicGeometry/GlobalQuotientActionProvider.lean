import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionEquivariance
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientGluingColimitConsumer
import LeanFormal.IUT.Foundations.GlobalQuotientProvider
import Mathlib.Tactic

/-!
# Global quotient provider from a finite group action

This file assembles the global quotient provider for a finite group action on a
finite etale cover: the actual gluing quotient cover, the invariant projection,
the gluing desc/fac/uniq, and the action cocone.  The action cocone colimit is
isolated as an explicit residual; no provider inhabitant is fabricated when
that colimit is not supplied.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option maxRecDepth 10000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionProvider

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartPresentation
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartPresentationToGluedProof
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientGluingDiagram
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientGluingColimitConsumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionData
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionEquivariance
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientProvider
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalFiniteEtaleQuotient
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G]
variable {X : FiniteEtaleCover (Spec (CommRingCat.of R))}

/-- The actual global quotient provider assembled from an action-data package. -/
structure GlobalQuotientActionProvider (A : GlobalQuotientActionData (R := R) X (G := G))
    where
  cover : FiniteEtaleCover (Spec (CommRingCat.of R))
  projection : X ⟶ cover
  projection_invariant : ∀ g : G, (A.coverAction g).hom ≫ projection = projection
  gluingCocone : Cocone (gluingDiagram A.presentation)
  gluingIsColimit : IsColimit gluingCocone
  desc : ∀ c : Cocone (gluingDiagram A.presentation),
    (quotientCover A.presentation).carrier ⟶ c.pt
  desc_fac : ∀ (c : Cocone (gluingDiagram A.presentation)) (Y : GluingObject A.presentation),
    (quotientCocone A.presentation).ι.app Y ≫ desc c = c.ι.app Y
  desc_uniq : ∀ (c : Cocone (gluingDiagram A.presentation))
    (u : (quotientCocone A.presentation).pt ⟶ c.pt),
    (∀ Y : GluingObject A.presentation,
      (quotientCocone A.presentation).ι.app Y ≫ u = c.ι.app Y) → u = desc c
  actionCocone : Cocone A.actionFunctor
  actionCoconeResidual : Prop

/-- The actual provider data, with the action cocone colimit left as the
explicit residual. -/
noncomputable def globalQuotientActionProvider
    (A : GlobalQuotientActionData (R := R) X (G := G)) :
    GlobalQuotientActionProvider A where
  cover := quotientCover A.presentation
  projection := invariantQuotientProjection A
  projection_invariant := invariantQuotientProjection_invariant A
  gluingCocone := quotientCocone A.presentation
  gluingIsColimit := actionGluingIsColimit A
  desc := fun c => desc A.presentation c
  desc_fac := fun c Y => desc_fac A.presentation c Y
  desc_uniq := fun c u hu => desc_uniq A.presentation c u hu
  actionCocone := A.cocone
  actionCoconeResidual := Nonempty (IsColimit A.cocone)

namespace GlobalQuotientActionProvider

variable {A : GlobalQuotientActionData (R := R) X (G := G)}
  (P : GlobalQuotientActionProvider A)

/-- The provider cover is the gluing quotient cover. -/
theorem cover_eq : P.cover = quotientCover A.presentation := rfl

/-- The provider projection is the invariant projection. -/
theorem projection_eq : P.projection = invariantQuotientProjection A := rfl

/-- The provider projection is invariant under the actual cover action. -/
theorem projection_invariant_apply (g : G) :
    (A.coverAction g).hom ≫ P.projection = P.projection :=
  P.projection_invariant g

/-- The provider cover is finite etale over the affine base. -/
theorem cover_finiteEtale :
    Etale (FiniteEtaleCover.structureMap P.cover) ∧
      IsFinite (FiniteEtaleCover.structureMap P.cover) :=
  quotientCover_finiteEtale A.presentation

/-- The provider gluing cocone is the actual quotient cocone. -/
theorem gluingCocone_eq : P.gluingCocone = quotientCocone A.presentation := rfl

/-- The provider gluing IsColimit is the actual gluing colimit. -/
theorem gluingIsColimit_eq : P.gluingIsColimit = actionGluingIsColimit A := rfl

/-- The provider desc is the gluing desc. -/
theorem desc_eq (c : Cocone (gluingDiagram A.presentation)) :
    P.desc c = desc A.presentation c := rfl

/-- The provider desc fac equation. -/
theorem desc_fac_apply (c : Cocone (gluingDiagram A.presentation))
    (Y : GluingObject A.presentation) :
    (quotientCocone A.presentation).ι.app Y ≫ P.desc c = c.ι.app Y :=
  P.desc_fac c Y

/-- The provider desc uniqueness. -/
theorem desc_uniq_apply (c : Cocone (gluingDiagram A.presentation))
    (u : (quotientCocone A.presentation).pt ⟶ c.pt)
    (hu : ∀ Y : GluingObject A.presentation,
      (quotientCocone A.presentation).ι.app Y ≫ u = c.ι.app Y) :
    u = P.desc c :=
  P.desc_uniq c u hu

/-- The provider action cocone is the actual action cocone. -/
theorem actionCocone_eq : P.actionCocone = A.cocone := rfl

/-- The exact action-cocone residual: an actual IsColimit for the action
cocone.  It is not asserted by the provider construction. -/
def ActionCoconeColimitResidual : Prop :=
  Nonempty (IsColimit P.actionCocone)

/-- The residual is equivalent to the existence of an action-cocone
IsColimit. -/
theorem actionCoconeColimitResidual_iff :
    P.ActionCoconeColimitResidual ↔ Nonempty (IsColimit P.actionCocone) :=
  Iff.rfl

/-- A provider with action-cocone colimit, conditional on the actual colimit
witness. -/
structure GlobalQuotientActionProviderWithColimit
    extends GlobalQuotientActionProvider A where
  actionIsColimit : IsColimit actionCocone

/-- Conditional provider upgrade from an actual action-cocone IsColimit. -/
noncomputable def globalQuotientActionProviderWithColimit
    (A : GlobalQuotientActionData (R := R) X (G := G))
    (h : IsColimit A.cocone) :
    GlobalQuotientActionProviderWithColimit A where
  __ := globalQuotientActionProvider A
  actionIsColimit := h

/-- The provider projection is compatible with the action-data projection. -/
theorem projection_eq_action_data :
    P.projection = A.projection := rfl

/-- The invariant quotient projection gives the provider projection. -/
theorem projection_invariant_eq :
    P.projection = invariantQuotientProjection A := rfl

end GlobalQuotientActionProvider

/-- The action-cocone residual is exactly the uncovered action quotient
universal property; no provider inhabitant is asserted beyond this. -/
theorem globalQuotientActionProvider_residual
    (A : GlobalQuotientActionData (R := R) X (G := G)) :
    (globalQuotientActionProvider A).actionCoconeResidual =
      Nonempty (IsColimit A.cocone) := rfl


namespace GlobalQuotientActionProvider

variable {A : GlobalQuotientActionData (R := R) X (G := G)}
  (P : GlobalQuotientActionProvider A)

/-- The provider cover has the invariant projection as its canonical map. -/
theorem cover_projection_fac :
    P.projection = invariantQuotientProjection A := rfl

/-- The provider cover structure map is the glued map. -/
theorem cover_structureMap :
    FiniteEtaleCover.structureMap P.cover = A.presentation.gluedMap :=
  quotientCover_structureMap A.presentation

/-- The provider cover carrier is the presentation glued scheme. -/
theorem cover_carrier : P.cover.carrier = A.presentation.glued := rfl

/-- The provider gluing cocone has the actual quotient point. -/
theorem gluingCocone_pt :
    P.gluingCocone.pt = (quotientCocone A.presentation).pt := rfl

/-- The provider gluing cocone components are the quotient cocone components. -/
theorem gluingCocone_ι (Y : GluingObject A.presentation) :
    P.gluingCocone.ι.app Y = (quotientCocone A.presentation).ι.app Y := rfl

/-- The provider action cocone is the action cocone of the action-data package. -/
theorem actionCocone_pt : P.actionCocone.pt = A.cocone.pt := rfl

/-- The provider action cocone components are the action-data components. -/
theorem actionCocone_ι (j : SingleObj G) :
    P.actionCocone.ι.app j = A.cocone.ι.app j := rfl

/-- The action-cocone residual gives a colimit witness when it holds. -/
theorem actionIsColimit_of_residual
    (h : P.ActionCoconeColimitResidual) : Nonempty (IsColimit P.actionCocone) :=
  h

/-- The action cocone residual is monotone under an actual colimit. -/
theorem actionCoconeColimitResidual_of_isColimit
    (h : IsColimit P.actionCocone) : P.ActionCoconeColimitResidual :=
  ⟨h⟩

/-- The provider with action colimit has the expected cover. -/
theorem withColimit_cover (Q : GlobalQuotientActionProviderWithColimit A) :
    Q.cover = quotientCover A.presentation := rfl

/-- The provider with action colimit has the expected projection. -/
theorem withColimit_projection (Q : GlobalQuotientActionProviderWithColimit A) :
    Q.projection = invariantQuotientProjection A := rfl

/-- The provider with action colimit has the expected action IsColimit. -/
theorem withColimit_actionIsColimit
    (Q : GlobalQuotientActionProviderWithColimit A) :
    Q.actionIsColimit = Q.actionIsColimit := rfl

end GlobalQuotientActionProvider


namespace GlobalQuotientActionProvider

variable {A : GlobalQuotientActionData (R := R) X (G := G)}

/-- The actual action provider cover is the gluing quotient cover. -/
theorem globalQuotientActionProvider_cover :
    (globalQuotientActionProvider A).cover = quotientCover A.presentation := rfl

/-- The actual action provider projection is the invariant projection. -/
theorem globalQuotientActionProvider_projection :
    (globalQuotientActionProvider A).projection = invariantQuotientProjection A := rfl

/-- The actual action provider has the gluing IsColimit. -/
theorem globalQuotientActionProvider_gluingIsColimit :
    (globalQuotientActionProvider A).gluingIsColimit = actionGluingIsColimit A := rfl

/-- The actual action provider action cocone is the action cocone. -/
theorem globalQuotientActionProvider_actionCocone :
    (globalQuotientActionProvider A).actionCocone = A.cocone := rfl

end GlobalQuotientActionProvider


namespace GlobalQuotientActionProvider

variable {A : GlobalQuotientActionData (R := R) X (G := G)}

/-- The action provider has the actual invariant projection. -/
theorem globalQuotientActionProvider_invariant (g : G) :
    (A.coverAction g).hom ≫ (globalQuotientActionProvider A).projection =
      (globalQuotientActionProvider A).projection :=
  invariantQuotientProjection_invariant A g

end GlobalQuotientActionProvider

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionProvider
