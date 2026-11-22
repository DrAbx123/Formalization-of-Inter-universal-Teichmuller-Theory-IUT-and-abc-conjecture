import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientProviderConditional
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-!
# Global quotient: provider residual

This file states the exact residual corresponding to a conditional provider:
for every finite-group action diagram, actual cocone data with an explicit
`IsColimit` proof.  It is only a Prop; no provider inhabitant is constructed.
-/

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientProviderResidual

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionCocone
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientProviderConditional
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {S : Scheme.{u}}

/-- Exact provider residual: every finite-group action diagram has actual cocone
data and an explicit `IsColimit` proof.  This is a Prop with no inhabitant. -/
def GlobalQuotientProviderResidual (S : Scheme.{u}) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G]
    (F : SingleObj G ⥤ FiniteEtaleCover S),
    ∃ D : GlobalActionCoconeData S G F, Nonempty (IsColimit D.cocone)

/-- A conditional provider implies the residual. -/
theorem providerResidual_of_provider (P : GlobalQuotientProvider S) :
    GlobalQuotientProviderResidual S := by
  intro G _ _ F
  exact ⟨P.coconeData G F, ⟨P.isColimit G F (P.coconeData G F)⟩⟩

/-- The provider residual is the per-diagram colimit form of the action-cocone
residual. -/
theorem globalActionCoconeResidual_iff_providerResidual (S : Scheme.{u}) :
    GlobalActionCoconeResidual S ↔ GlobalQuotientProviderResidual S := by
  constructor
  · intro h G _ _ F
    rcases h G F with ⟨D, ⟨d⟩⟩
    exact ⟨D, ⟨d.isColimit⟩⟩
  · intro h G _ _ F
    rcases h G F with ⟨D, ⟨hc⟩⟩
    exact ⟨D, ⟨{ isColimit := hc }⟩⟩

/-- The provider residual implies the exact global `HasColimitsOfShape`
residual.  This is a conditional implication, not an inhabited provider. -/
theorem globalQuotientCoconeResidual_of_providerResidual
    (h : GlobalQuotientProviderResidual S) :
    GlobalQuotientCoconeResidual S := by
  classical
  intro G _ _
  refine ⟨fun F => ?_⟩
  rcases h G F with ⟨D, ⟨hc⟩⟩
  exact HasColimit.mk D.cocone hc

/-- The exact residual is equivalent to the existence of a provider only in the
conditional direction; no provider inhabitant is asserted. -/
theorem providerResidual_of_nonempty_provider
    (h : Nonempty (GlobalQuotientProvider S)) :
    GlobalQuotientProviderResidual S :=
  h.elim providerResidual_of_provider

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientProviderResidual
end