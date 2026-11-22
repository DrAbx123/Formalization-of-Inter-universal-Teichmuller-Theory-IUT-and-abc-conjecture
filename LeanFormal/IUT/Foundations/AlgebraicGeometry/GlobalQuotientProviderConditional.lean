import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientCoconeNaturality
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-!
# Global quotient: conditional provider

This file packages a provider only as an explicit conditional input: a choice
of action cocone data together with an `IsColimit` proof for every diagram.
Nothing inhabits the provider; the implications below are actual but conditional.
-/

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientProviderConditional

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionCocone
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientCoconeNaturality
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {S : Scheme.{u}}

/-- Conditional global provider: for every finite-group action diagram, actual
cocone data plus an explicit `IsColimit` proof. This is an input structure; no
inhabitant is constructed or claimed. -/
structure GlobalQuotientProvider (S : Scheme.{u}) where
  /-- Cocone data for every finite-group action diagram. -/
  coconeData : ∀ (G : Type u) [Group G] [Finite G]
    (F : SingleObj G ⥤ FiniteEtaleCover S), GlobalActionCoconeData S G F
  /-- Explicit colimit proof for every such cocone. -/
  isColimit : ∀ (G : Type u) [Group G] [Finite G]
    (F : SingleObj G ⥤ FiniteEtaleCover S)
    (D : GlobalActionCoconeData S G F), IsColimit D.cocone

/-- The provider gives the cocone for each action diagram. -/
noncomputable def GlobalQuotientProvider.cocone (P : GlobalQuotientProvider S)
    (G : Type u) [Group G] [Finite G]
    (F : SingleObj G ⥤ FiniteEtaleCover S) : Cocone F :=
  (P.coconeData G F).cocone

/-- The provider gives the explicit IsColimit proof for its cocone. -/
theorem GlobalQuotientProvider.isColimit_cocone (P : GlobalQuotientProvider S)
    (G : Type u) [Group G] [Finite G]
    (F : SingleObj G ⥤ FiniteEtaleCover S) :
    IsColimit (P.cocone G F) :=
  P.isColimit G F (P.coconeData G F)

/-- Conditional residual: the provider implies the exact cocone/IsColimit
statement for all finite-group action diagrams. -/
theorem globalActionCoconeResidual_of_provider (P : GlobalQuotientProvider S) :
    GlobalActionCoconeResidual S := by
  intro G _ _ F
  refine ⟨P.coconeData G F, ?_⟩
  exact ⟨P.isColimit G F (P.coconeData G F)⟩

/-- The provider implies the global HasColimits residual. -/
theorem globalQuotientCoconeResidual_of_provider (P : GlobalQuotientProvider S) :
    GlobalQuotientCoconeResidual S := by
  intro G _ _
  refine ⟨fun F => ?_⟩
  exact HasColimit.mk (P.cocone G F) (P.isColimit G F (P.coconeData G F))

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientProviderConditional
end