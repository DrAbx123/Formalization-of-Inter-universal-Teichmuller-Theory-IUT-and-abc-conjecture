import LeanFormal.IUT.Foundations.AlgebraicGeometry.LogKummerK1K2Consumer
import LeanFormal.IUT.Foundations.AlgebraicGeometry.LogUnscaledK1K2Consumer

/-! One actual-source consumer square: K1/K2 and log-Kummer for all principal units. -/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LeanFormal.N8.LogSourceK1K2Consumer

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.N8.LogCarrierK1K2
open ABCBridge.LogKummerK1K2
open ABCBridge.LogKummerK1K2Consumer
open LeanFormal.N8.LogUnscaledK1K2Consumer
open scoped Pointwise

variable {F : Type*} [Field F] [NumberField F] {p : Nat} [Fact p.Prime]

local instance normalizedCompletionNormedAlgebraAtPrime
    (place : FinitePlaceAtPrime F p) :
    NormedAlgebra ℚ_[p] (NormalizedCompletion place.val) := by
  rcases place with ⟨v, hv⟩
  cases hv
  exact normalizedCompletionNormedAlgebra v

variable (place : FinitePlaceAtPrime F p)

/-- For all principal units: the actual log-Kummer square. -/
theorem source_logKummer_square_all :
    ∀ u : principalUnits (K := SourceCompletion place),
      completionIsometryEquiv place
          (principalUnitLog (K := SourceCompletion place) u) =
        principalUnitLog (K := TargetCompletion place) (principalUnitMap place u) :=
  logKummerK1K2_square_all place

/-- For all integral units: the unscaled K1/K2 square. -/
theorem source_K2Map_unitLog_all :
    ∀ u : (Integers (SourceCompletion place))ˣ,
      (K2Map place (unitLogToLattice (K := SourceCompletion place) (p := p) u) :
          TargetCompletion place) =
        unitLog (K := TargetCompletion place)
          (integralUnitMap (completionIsometryEquiv place).toRingHom
            (completionIsometryEquiv_isometry place) u) :=
  actual_K2Map_unitLog_forall (p := p) place

theorem source_p_scaling_all :
    ∀ u : principalUnits (K := SourceCompletion place),
      completionIsometryEquiv place
          (principalUnitLog (K := SourceCompletion place) (u ^ p)) =
        (p : TargetCompletion place) *
          completionIsometryEquiv place
            (principalUnitLog (K := SourceCompletion place) u) :=
  fun u => logKummerK1K2_p_scaling place u

theorem source_logShellScale_scaling_all :
    ∀ u : principalUnits (K := SourceCompletion place),
      completionIsometryEquiv place
          ((logShellScale p : SourceCompletion place)⁻¹ *
            principalUnitLog (K := SourceCompletion place) u) =
        (logShellScale p : TargetCompletion place)⁻¹ *
          principalUnitLog (K := TargetCompletion place) (principalUnitMap place u) :=
  fun u => logKummerK1K2_logShellScale_scaling place u

theorem source_logShellScale_eq :
    logShellScale p = if p = 2 then p ^ 2 else p := rfl

/-- The combined actual-source consumer square: forall principal units (K1/K2
and log-Kummer), with exact p and logShellScale scaling. -/
theorem sourceK1K2_logKummer_consumer_square :
    (∀ u : principalUnits (K := SourceCompletion place),
      completionIsometryEquiv place
          (principalUnitLog (K := SourceCompletion place) u) =
        principalUnitLog (K := TargetCompletion place) (principalUnitMap place u)) ∧
    (∀ u : (Integers (SourceCompletion place))ˣ,
      (K2Map place (unitLogToLattice (K := SourceCompletion place) (p := p) u) :
          TargetCompletion place) =
        unitLog (K := TargetCompletion place)
          (integralUnitMap (completionIsometryEquiv place).toRingHom
            (completionIsometryEquiv_isometry place) u)) ∧
    (logShellScale p = if p = 2 then p ^ 2 else p) ∧
    (∀ u : principalUnits (K := SourceCompletion place),
      completionIsometryEquiv place
          (principalUnitLog (K := SourceCompletion place) (u ^ p)) =
        (p : TargetCompletion place) *
          completionIsometryEquiv place
            (principalUnitLog (K := SourceCompletion place) u)) ∧
    (∀ u : principalUnits (K := SourceCompletion place),
      completionIsometryEquiv place
          ((logShellScale p : SourceCompletion place)⁻¹ *
            principalUnitLog (K := SourceCompletion place) u) =
        (logShellScale p : TargetCompletion place)⁻¹ *
          principalUnitLog (K := TargetCompletion place)
            (principalUnitMap place u)) :=
  ⟨source_logKummer_square_all place,
    source_K2Map_unitLog_all (p := p) place,
    source_logShellScale_eq (p := p),
    source_p_scaling_all place,
    source_logShellScale_scaling_all place⟩

end LeanFormal.N8.LogSourceK1K2Consumer
