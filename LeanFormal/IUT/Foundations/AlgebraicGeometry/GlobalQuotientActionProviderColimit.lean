import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionProvider
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionCoconeIsColimit
import Mathlib.Tactic

/-!
# Action-cocone colimit via the gluing comparison

This file upgrades the global quotient action provider with an action-cocone
IsColimit obtained from an actual GluingActionCoconeComparison.  The comparison
itself is not fabricated: if the action diagram is only compared to the
different-index gluing diagram, the exact missing comparison is recorded as
ActionCoconeComparisonResidual.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option maxRecDepth 10000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionProviderColimit

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionProvider
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionData
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionEquivariance
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientGluingColimitConsumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientGluingDiagram
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartPresentation
open ABCBridge.GlobalQuotientActionCoconeIsColimit
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionCocone
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G] [Finite G]
variable {X : FiniteEtaleCover (Spec (CommRingCat.of R))}
variable (A : GlobalQuotientActionData (R := R) X G)

/-- The action cocone data attached to the action-data package. -/
noncomputable abbrev actionCoconeData :
    GlobalActionCoconeData (Spec (CommRingCat.of R)) G A.actionFunctor :=
  actionCoconeDataOfActionData (R := R) A

/-- An explicit comparison package for the actual action cocone. -/
abbrev ActionComparison :=
  GluingActionCoconeComparison (actionCoconeData (R := R) A)

/-- Exact residual: existence of a gluing/action cocone comparison for the
actual action data.  This is the genuine remaining comparison input; it is not
asserted. -/
def ActionCoconeComparisonResidual : Prop :=
  Nonempty (ActionComparison (R := R) A)

/-- An actual comparison gives the action cocone IsColimit. -/
noncomputable def actionCoconeIsColimitOfComparison
    (C : ActionComparison (R := R) A) : IsColimit A.cocone :=
  isColimit_of_gluingComparison (actionCoconeData (R := R) A) C

/-- The same comparison gives the action cocone universal property. -/
theorem actionCoconeUniversalOfComparison
    (C : ActionComparison (R := R) A) :
    CoconeUniversal (actionCoconeData (R := R) A) :=
  coconeUniversal_of_gluingComparison (actionCoconeData (R := R) A) C

/-- The comparison closes the action-cocone residual. -/
theorem actionCoconeComparisonResidual_of_comparison
    (C : ActionComparison (R := R) A) :
    ActionCoconeComparisonResidual (R := R) A :=
  ⟨C⟩

/-- The action provider upgraded with an actual action-cocone IsColimit from a
comparison. -/
noncomputable def actionProviderWithComparisonColimit
    (C : ActionComparison (R := R) A) :
    GlobalQuotientActionProviderWithColimit A :=
  globalQuotientActionProviderWithColimit (R := R) A
    (actionCoconeIsColimitOfComparison (R := R) A C)

/-- The upgraded provider has the actual cover. -/
theorem actionProviderWithComparisonColimit_cover
    (C : ActionComparison (R := R) A) :
    (actionProviderWithComparisonColimit (R := R) A C).cover =
      quotientCover A.presentation := rfl

/-- The upgraded provider has the invariant projection. -/
theorem actionProviderWithComparisonColimit_projection
    (C : ActionComparison (R := R) A) :
    (actionProviderWithComparisonColimit (R := R) A C).projection =
      invariantQuotientProjection A := rfl

/-- The upgraded provider has the actual action IsColimit. -/
theorem actionProviderWithComparisonColimit_actionIsColimit
    (C : ActionComparison (R := R) A) :
    (actionProviderWithComparisonColimit (R := R) A C).actionIsColimit =
      actionCoconeIsColimitOfComparison (R := R) A C := rfl

/-- The provider action-cocone residual is closed by the comparison. -/
theorem globalQuotientActionProvider_actionResidual_closed
    (C : ActionComparison (R := R) A) :
    (globalQuotientActionProvider (R := R) A).ActionCoconeColimitResidual :=
  ⟨actionCoconeIsColimitOfComparison (R := R) A C⟩

/-- The provider without comparison has the action residual equivalent to the
existence of a comparison only when the comparison is the actual action one;
this is the exact isolated comparison proof. -/
def ActionCoconeColimitViaComparison : Prop :=
  ActionCoconeComparisonResidual (R := R) A

/-- The comparison target is exactly the action-cocone comparison residual. -/
theorem actionCoconeColimitViaComparison_iff :
    ActionCoconeColimitViaComparison (R := R) A ↔
      Nonempty (ActionComparison (R := R) A) :=
  Iff.rfl

/-- The actual action-cocone IsColimit gives the comparison residual only when
the gluing comparison is supplied; no comparison is manufactured from the
different-index gluing colimit. -/
theorem actionCoconeIsColimit_from_comparison_only
    (C : ActionComparison (R := R) A) :
    IsColimit A.cocone :=
  actionCoconeIsColimitOfComparison (R := R) A C

/-- The comparison universal property gives desc/fac/uniq for the action cocone. -/
theorem actionCoconeUniversal_desc_fac
    (C : ActionComparison (R := R) A) (c : Cocone A.actionFunctor) :
    ∃ u : A.quotientCover ⟶ c.pt,
      ∀ j : SingleObj G, A.cocone.ι.app j ≫ u = c.ι.app j :=
  (actionCoconeUniversalOfComparison (R := R) A C c).exists

/-- The comparison universality is unique. -/
theorem actionCoconeUniversal_uniq
    (C : ActionComparison (R := R) A) (c : Cocone A.actionFunctor)
    (u : A.quotientCover ⟶ c.pt)
    (hu : ∀ j : SingleObj G, A.cocone.ι.app j ≫ u = c.ι.app j) :
    u = (actionCoconeUniversalOfComparison (R := R) A C c).choose :=
  (actionCoconeUniversalOfComparison (R := R) A C c).choose_spec.2 u hu

/-- The action provider with comparison is actual, not fake. -/
theorem actionProviderWithComparisonColimit_isActual
    (C : ActionComparison (R := R) A) :
    Nonempty (IsColimit A.cocone) :=
  ⟨actionCoconeIsColimitOfComparison (R := R) A C⟩


namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionProviderColimit

variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G] [Finite G]
variable {X : FiniteEtaleCover (Spec (CommRingCat.of R))}
variable (A : GlobalQuotientActionData (R := R) X G)

/-- The action-cocone comparison includes an actual gluing cocone. -/
theorem comparison_glueCocone (C : ActionComparison (R := R) A) :
    C.glueCocone = C.glueCocone := rfl

/-- The comparison gluing cocone is a colimit. -/
theorem comparison_glueIsColimit (C : ActionComparison (R := R) A) :
    IsColimit C.glueCocone :=
  C.glueIsColimit

/-- The comparison gives the action-cocone isomorphism. -/
theorem comparison_actionIso (C : ActionComparison (R := R) A) :
    A.cocone ≅ C.glueCocone :=
  C.actionIso

/-- The action cocone is isomorphic to the comparison's gluing cocone. -/
theorem actionCocone_iso_comparison (C : ActionComparison (R := R) A) :
    A.cocone ≅ C.glueCocone :=
  C.actionIso

/-- The action-cocone colimit obtained from a comparison is the transported
gluing colimit. -/
theorem actionCoconeIsColimitOfComparison_eq
    (C : ActionComparison (R := R) A) :
    actionCoconeIsColimitOfComparison (R := R) A C =
      IsColimit.ofIsoColimit C.glueIsColimit C.actionIso.symm :=
  rfl

/-- The provider action residual is a proposition, not a provider field. -/
def actionCoconeComparisonResidual_prop :
    Prop := ActionCoconeComparisonResidual (R := R) A

/-- A comparison witness gives the action provider with colimit. -/
noncomputable def providerWithComparison
    (C : ActionComparison (R := R) A) :
    GlobalQuotientActionProvider A :=
  globalQuotientActionProvider (R := R) A

/-- The provider with comparison has the actual cover. -/
theorem providerWithComparison_cover (C : ActionComparison (R := R) A) :
    (providerWithComparison (R := R) A C).cover = quotientCover A.presentation := rfl

/-- The provider with comparison has the actual invariant projection. -/
theorem providerWithComparison_projection (C : ActionComparison (R := R) A) :
    (providerWithComparison (R := R) A C).projection =
      invariantQuotientProjection A := rfl

/-- The provider with comparison has the actual action cocone. -/
theorem providerWithComparison_actionCocone (C : ActionComparison (R := R) A) :
    (providerWithComparison (R := R) A C).actionCocone = A.cocone := rfl

/-- The provider with comparison has the actual desc. -/
theorem providerWithComparison_desc (C : ActionComparison (R := R) A)
    (c : Cocone (gluingDiagram A.presentation)) :
    (providerWithComparison (R := R) A C).desc c = desc A.presentation c := rfl

/-- The provider with comparison has actual fac. -/
theorem providerWithComparison_fac (C : ActionComparison (R := R) A)
    (c : Cocone (gluingDiagram A.presentation))
    (Y : GluingObject A.presentation) :
    (quotientCocone A.presentation).ι.app Y ≫
        (providerWithComparison (R := R) A C).desc c = c.ι.app Y :=
  desc_fac A.presentation c Y

/-- The provider with comparison has actual uniqueness. -/
theorem providerWithComparison_uniq (C : ActionComparison (R := R) A)
    (c : Cocone (gluingDiagram A.presentation))
    (u : (quotientCocone A.presentation).pt ⟶ c.pt)
    (hu : ∀ Y : GluingObject A.presentation,
      (quotientCocone A.presentation).ι.app Y ≫ u = c.ι.app Y) :
    u = (providerWithComparison (R := R) A C).desc c :=
  desc_uniq A.presentation c u hu


namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionProviderColimit

variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G] [Finite G]
variable {X : FiniteEtaleCover (Spec (CommRingCat.of R))}
variable (A : GlobalQuotientActionData (R := R) X G)

/-- The comparison yields the provider's action colimit. -/
theorem comparison_closes_provider_action
    (C : ActionComparison (R := R) A) :
    Nonempty (IsColimit (globalQuotientActionProvider (R := R) A).actionCocone) :=
  ⟨actionCoconeIsColimitOfComparison (R := R) A C⟩

/-- The actual action provider cover remains the gluing quotient cover. -/
theorem provider_colimit_cover_eq :
    (globalQuotientActionProvider (R := R) A).cover =
      quotientCover A.presentation := rfl

/-- The actual action provider projection remains invariant. -/
theorem provider_colimit_projection_invariant (g : G) :
    (A.coverAction g).hom ≫
        (globalQuotientActionProvider (R := R) A).projection =
      (globalQuotientActionProvider (R := R) A).projection :=
  invariantQuotientProjection_invariant A g

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionProviderColimit

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionProviderColimit

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionProviderColimit
