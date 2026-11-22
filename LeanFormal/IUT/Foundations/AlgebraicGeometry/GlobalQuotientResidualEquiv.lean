import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientProviderResidual
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientProviderAssembly
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-!
# Global quotient: residual equivalences

Equivalent conditional forms of the global quotient residual.  These are
post-compile-delta drafts, held for the next batch; none is an inhabitation
claim.
-/

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientResidualEquiv

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionCocone
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientProviderAssembly
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientProviderResidual
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientUniq
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {S : Scheme.{u}}

/-- The chart-provider assembly residual is equivalent to the provider residual:
an assembly supplies the chosen cocone data, and a provider supplies its chart
data per diagram. -/
theorem providerResidual_iff_assemblyResidual
    (S : Scheme.{u}) :
    GlobalQuotientProviderResidual S ↔
      Nonempty (GlobalQuotientProviderAssembly S) :=
  by
    constructor
    · intro h
      classical
      exact ⟨{ chartProvider := fun G _ _ F => by
        rcases h G F with ⟨D, ⟨hc⟩⟩
        exact { D := D, actionData := D, quotient_eq := rfl, isColimit := hc } }⟩
    · rintro ⟨A⟩
      exact A.providerResidual

/-- The exact HasColimits residual implies the per-diagram provider residual
only conditionally, via choice of the action cocone data.  This direction is
not a provider construction. -/
theorem providerResidual_of_globalResidual
    (h : GlobalQuotientCoconeResidual S) :
    GlobalQuotientProviderResidual S :=
  by
    classical
    intro G _ _ F
    exact ⟨{ quotient := (h G).has_colimit F |>.cocone.pt
      proj := (h G).has_colimit F |>.cocone.ι.app (SingleObj.star G)
      proj_invariant := fun g => (h G).has_colimit F |>.cocone.ι.naturality g },
      ⟨(h G).has_colimit F |>.isColimit⟩⟩

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientResidualEquiv
end