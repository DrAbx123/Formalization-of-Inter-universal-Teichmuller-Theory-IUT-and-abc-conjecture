import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientProviderAssembly
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientCoconeCompat
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-!
# Global quotient: provider descent

Conditional descent of chart providers to provider assembly along quotient
isomorphisms.  This is a post-compile-delta draft, held for the next batch.
-/

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientProviderDescent

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDesc
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionCocone
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientCoconeCompat
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientProviderAssembly
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientProviderResidual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {S : Scheme.{u}}

/-- A chart provider equipped with a quotient isomorphism to another cover. -/
structure GlobalQuotientChartProviderIso {G : Type u} [Group G] [Finite G]
    {F : SingleObj G ⥤ FiniteEtaleCover S}
    (P : GlobalQuotientActionChartProvider S G F)
    (Q' : FiniteEtaleCover S) where
  /-- The quotient isomorphism. -/
  iso : P.actionData.quotient ≅ Q'

namespace GlobalQuotientChartProviderIso

variable {G : Type u} [Group G] [Finite G]
variable {F : SingleObj G ⥤ FiniteEtaleCover S}
variable {P : GlobalQuotientActionChartProvider S G F}
variable {Q' : FiniteEtaleCover S}

variable (I : GlobalQuotientChartProviderIso P Q')

/-- The reindexed action data. -/
noncomputable def reindexedData : GlobalActionCoconeData S G F :=
  P.actionData.reindex Q' I.iso

theorem reindexedData_proj :
    I.reindexedData.proj = P.actionData.proj ≫ I.iso.hom :=
  rfl

end GlobalQuotientChartProviderIso

/-- A chart provider with a chosen quotient isomorphism remains a chart
provider for the reindexed quotient; the colimit proof is transported only
conditionally, with an explicit input. -/
noncomputable def GlobalQuotientChartProviderIso.toChartProvider
    {G : Type u} [Group G] [Finite G]
    {F : SingleObj G ⥤ FiniteEtaleCover S}
    {P : GlobalQuotientActionChartProvider S G F}
    {Q' : FiniteEtaleCover S}
    (I : GlobalQuotientChartProviderIso P Q')
    (hcolim : IsColimit I.reindexedData.cocone) :
    GlobalQuotientActionChartProvider S G F where
  D := P.D
  actionData := I.reindexedData
  quotient_eq := by
    rw [I.reindexedData_proj]
    exact P.quotient_eq
  isColimit := hcolim

/-- Conditional assembly theorem: chart providers with explicit colimit
transport give a provider assembly.  No inhabitant is produced. -/
theorem providerAssembly_of_chartProviders
    (P : ∀ (G : Type u) [Group G] [Finite G]
      (F : SingleObj G ⥤ FiniteEtaleCover S), GlobalQuotientActionChartProvider S G F) :
    GlobalQuotientProviderResidual S := by
  intro G _ _ F
  exact ⟨(P G F).actionData, ⟨(P G F).isColimit⟩⟩

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientProviderDescent
end