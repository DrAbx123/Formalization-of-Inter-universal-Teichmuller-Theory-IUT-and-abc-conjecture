import LeanFormal.IUT.Foundations.AlgebraicGeometry.LogUnscaledImageConsumer
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmFunctoriality
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion

/-! Source consumer for the unscaled log naturality square and image formula. -/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LeanFormal.N8.LogUnscaledSourceConsumer

open LeanFormal.N8.LogUnscaledImageConsumer
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits

variable {F : Type*} [Field F] [NumberField F] {p : Nat} [Fact p.Prime]

local instance normalizedCompletionNormedAlgebraAtPrime
    (place : FinitePlaceAtPrime F p) :
    NormedAlgebra ℚ_[p] (NormalizedCompletion place.val) := by
  rcases place with ⟨v, hv⟩
  cases hv
  exact normalizedCompletionNormedAlgebra v

variable (place : FinitePlaceAtPrime F p)

/-- Exposed underlying formula of the actual unscaled log image equivalence:
`val(e_L x) = e(val x)`. -/
theorem actualUnscaledLogImageEquiv_formula :
    ∀ x : unscaledLogImage (p := p) (K := SourceCompletion place),
      (actualUnscaledLogImageEquiv place x : TargetCompletion place) =
        completionIsometryEquiv place (x : SourceCompletion place) :=
  fun x => actualUnscaledLogImageEquiv_val place x

/-- Forall-unit unscaled log naturality square at an arbitrary finite-place
actual completion: the image equivalence sends the log of a unit to the log of
the corresponding integral unit. -/
theorem actual_unscaled_log_naturality_forall :
    ∀ u : (Integers (SourceCompletion place))ˣ,
      (actualUnscaledLogImageEquiv place
        ⟨unitLog (K := SourceCompletion place) u,
          unitLog_mem_unscaledLogImage (p := p) u⟩ : TargetCompletion place) =
        unitLog (K := TargetCompletion place)
          (integralUnitMap (completionIsometryEquiv place).toRingHom
            (completionIsometryEquiv_isometry place) u) := by
  intro u
  exact congrArg Subtype.val (actualUnscaledLogImageEquiv_unitLog place u)

/-- Multiplicative form of the same square. -/
theorem actual_unscaled_log_naturality_mul_forall :
    ∀ u v : (Integers (SourceCompletion place))ˣ,
      (actualUnscaledLogImageEquiv place
        ⟨unitLog (K := SourceCompletion place) (u * v),
          unitLog_mem_unscaledLogImage (p := p) (u * v)⟩ : TargetCompletion place) =
        unitLog (K := TargetCompletion place)
          (integralUnitMap (completionIsometryEquiv place).toRingHom
            (completionIsometryEquiv_isometry place) (u * v)) := by
  intro u v
  exact actual_unscaled_log_naturality_forall place (u * v)

end LeanFormal.N8.LogUnscaledSourceConsumer
