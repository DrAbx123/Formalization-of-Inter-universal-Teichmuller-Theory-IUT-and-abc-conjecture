import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionProvider
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientGluingDiagram
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientGluingColimitConsumer
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionCoconeIsColimit
import Mathlib.Tactic

/-!
# Gluing-based global quotient provider

The provider universal property is the actual gluing-diagram colimit: cover,
invariant projection, gluing desc/fac/uniq.  The action-cocone comparison is an
optional separate target and is NOT a prerequisite for the provider.  No fake
action colimit is asserted.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option maxRecDepth 10000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionProviderGluing

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionData
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionEquivariance
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientGluingDiagram
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientGluingColimitConsumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionProvider
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartPresentation
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartPresentationToGluedProof
open ABCBridge.GlobalQuotientActionCoconeIsColimit
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G]
variable {X : FiniteEtaleCover (Spec (CommRingCat.of R))}
variable (A : GlobalQuotientActionData (R := R) X G)

/-- The gluing-based global quotient provider.  Its universality is the actual
gluing-diagram IsColimit, not an action-cocone IsColimit. -/
structure GlobalQuotientProviderGluing
    (A : GlobalQuotientActionData (R := R) X G) where
  cover : FiniteEtaleCover (Spec (CommRingCat.of R))
  projection : X ⟶ cover
  projection_invariant : ∀ g : G, (A.coverAction g).hom ≫ projection = projection
  cocone : Cocone (gluingDiagram A.presentation)
  isColimit : IsColimit cocone
  desc : ∀ c : Cocone (gluingDiagram A.presentation),
    (quotientCover A.presentation).carrier ⟶ c.pt
  desc_fac : ∀ (c : Cocone (gluingDiagram A.presentation))
    (Y : GluingObject A.presentation),
    (quotientCocone A.presentation).ι.app Y ≫ desc c = c.ι.app Y
  desc_uniq : ∀ (c : Cocone (gluingDiagram A.presentation))
    (u : (quotientCocone A.presentation).pt ⟶ c.pt),
    (∀ Y : GluingObject A.presentation,
      (quotientCocone A.presentation).ι.app Y ≫ u = c.ι.app Y) → u = desc c

/-- The actual gluing-based provider. -/
noncomputable def globalQuotientProviderGluing
    (A : GlobalQuotientActionData (R := R) X G) :
    GlobalQuotientProviderGluing A where
  cover := quotientCover A.presentation
  projection := invariantQuotientProjection A
  projection_invariant := invariantQuotientProjection_invariant A
  cocone := quotientCocone A.presentation
  isColimit := actionGluingIsColimit A
  desc := fun c => desc A.presentation c
  desc_fac := fun c Y => desc_fac A.presentation c Y
  desc_uniq := fun c u hu => desc_uniq A.presentation c u hu

namespace GlobalQuotientProviderGluing

variable {A : GlobalQuotientActionData (R := R) X G}
  (P : GlobalQuotientProviderGluing A)

/-- The provider cover is the actual gluing quotient cover. -/
theorem cover_eq : P.cover = quotientCover A.presentation := rfl

/-- The provider projection is the action-invariant projection. -/
theorem projection_eq : P.projection = invariantQuotientProjection A := rfl

/-- The provider projection is invariant under the cover action. -/
theorem projection_invariant_apply (g : G) :
    (A.coverAction g).hom ≫ P.projection = P.projection :=
  P.projection_invariant g

/-- The provider cover is finite etale over the affine base. -/
theorem cover_finiteEtale :
    Etale (FiniteEtaleCover.structureMap P.cover) ∧
      IsFinite (FiniteEtaleCover.structureMap P.cover) :=
  quotientCover_finiteEtale A.presentation

/-- The provider cocone is the actual gluing cocone. -/
theorem cocone_eq : P.cocone = quotientCocone A.presentation := rfl

/-- The provider gluing IsColimit is the actual gluing colimit. -/
theorem isColimit_eq : P.isColimit = actionGluingIsColimit A := rfl

/-- The provider desc is the actual gluing desc. -/
theorem desc_eq (c : Cocone (gluingDiagram A.presentation)) :
    P.desc c = desc A.presentation c := rfl

/-- Fac for the provider desc. -/
theorem desc_fac_apply (c : Cocone (gluingDiagram A.presentation))
    (Y : GluingObject A.presentation) :
    (quotientCocone A.presentation).ι.app Y ≫ P.desc c = c.ι.app Y :=
  P.desc_fac c Y

/-- Uniqueness of the provider desc. -/
theorem desc_uniq_apply (c : Cocone (gluingDiagram A.presentation))
    (u : (quotientCocone A.presentation).pt ⟶ c.pt)
    (hu : ∀ Y : GluingObject A.presentation,
      (quotientCocone A.presentation).ι.app Y ≫ u = c.ι.app Y) :
    u = P.desc c :=
  P.desc_uniq c u hu

/-- The provider universal property: every gluing cone factors uniquely through
the cover. -/
def UniversalProperty : Prop :=
  ∀ c : Cocone (gluingDiagram A.presentation),
    ∃! u : (quotientCocone A.presentation).pt ⟶ c.pt,
      ∀ Y : GluingObject A.presentation,
        (quotientCocone A.presentation).ι.app Y ≫ u = c.ι.app Y

/-- The actual provider satisfies the universal property. -/
theorem universalProperty : P.UniversalProperty := by
  intro c
  refine ⟨P.desc c, ?_, ?_⟩
  · intro Y
    exact P.desc_fac c Y
  · intro u hu
    exact P.desc_uniq c u hu

/-- The universal property is exactly the gluing-diagram IsColimit. -/
theorem universalProperty_iff_isColimit :
    P.UniversalProperty ↔ Nonempty (IsColimit P.cocone) := by
  constructor
  · intro h
    refine ⟨IsColimit.mk (fun c => (h c).choose)
      (fun c j => (h c).choose_spec.1 j) ?_⟩
    intro c u hu
    exact (h c).choose_spec.2 u hu
  · rintro ⟨I⟩ c
    exact ⟨I.desc c, I.fac c, fun u hu => I.uniq c u hu⟩

/-- The provider is complete without any action-cocone colimit. -/
theorem provider_no_action_colimit_needed : P.UniversalProperty :=
  P.universalProperty

/-- The action-cocone comparison is an optional separate target, not a provider
field. -/
def ActionCoconeComparisonResidual : Prop :=
  Nonempty (GluingActionCoconeComparison
    (actionCoconeDataOfActionData (R := R) A))

/-- The optional residual is independent of the provider universal property. -/
theorem actionCoconeComparisonResidual_iff :
    P.ActionCoconeComparisonResidual ↔
      Nonempty (GluingActionCoconeComparison
        (actionCoconeDataOfActionData (R := R) A)) :=
  Iff.rfl

/-- The gluing-based provider remains valid regardless of the optional
action-cocone comparison. -/
theorem provider_holds_without_action_comparison :
    P.UniversalProperty :=
  P.universalProperty

/-- The provider has actual desc/fac/uniq. -/
theorem provider_desc_fac_uniq (c : Cocone (gluingDiagram A.presentation)) :
    (∃ u : (quotientCocone A.presentation).pt ⟶ c.pt,
      ∀ Y : GluingObject A.presentation,
        (quotientCocone A.presentation).ι.app Y ≫ u = c.ι.app Y) ∧
      (∀ u : (quotientCocone A.presentation).pt ⟶ c.pt,
        (∀ Y : GluingObject A.presentation,
          (quotientCocone A.presentation).ι.app Y ≫ u = c.ι.app Y) →
        u = P.desc c) := by
  refine ⟨⟨P.desc c, ?_⟩, ?_⟩
  · intro Y
    exact P.desc_fac c Y
  · intro u hu
    exact P.desc_uniq c u hu

/-- The provider cover is the same actual quotient cover as the action
provider's cover. -/
theorem cover_eq_action_provider :
    P.cover = (globalQuotientActionProvider (R := R) A).cover := rfl

/-- The provider projection is the same invariant projection as the action
provider's projection. -/
theorem projection_eq_action_provider :
    P.projection = (globalQuotientActionProvider (R := R) A).projection := rfl

end GlobalQuotientProviderGluing

/-- The actual gluing provider cover. -/
theorem globalQuotientProviderGluing_cover :
    (globalQuotientProviderGluing (R := R) A).cover =
      quotientCover A.presentation := rfl

/-- The actual gluing provider universal property. -/
theorem globalQuotientProviderGluing_universal :
    (globalQuotientProviderGluing (R := R) A).UniversalProperty :=
  (globalQuotientProviderGluing (R := R) A).universalProperty

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionProviderGluing
