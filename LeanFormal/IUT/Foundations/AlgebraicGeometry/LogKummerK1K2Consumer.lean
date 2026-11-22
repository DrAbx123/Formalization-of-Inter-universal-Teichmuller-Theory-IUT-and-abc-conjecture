import LeanFormal.IUT.Foundations.AlgebraicGeometry.LogKummerK1K2
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithm
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceLogShell
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

/-!
# Consumer package for the actual K1/K2 log-Kummer square

Unconditional generic packaging at `place : FinitePlaceAtPrime F p` with the
actual source/target completions and the actual completion isometry.  It states
the square for all principal units, the exact p-power scaling, and the exact
`logShellScale p` scaling.  No Q5 alias and no source card.
-/
namespace ABCBridge.LogKummerK1K2Consumer

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.N8.LogCarrierK1K2
open ABCBridge.LogKummerK1K2

universe u

variable {F : Type u} [Field F] [NumberField F] {p : ℕ} [Fact p.Prime]
  (place : FinitePlaceAtPrime F p)

local instance normalizedCompletionNormedAlgebraAtPrime :
    NormedAlgebra ℚ_[p] (NormalizedCompletion place.val) := by
  rcases place with ⟨v, hv⟩
  cases hv
  exact normalizedCompletionNormedAlgebra v

/-- **The exact generic K1/K2 log-Kummer square, for all principal units**, plus
the exact p-power and `logShellScale p` scalings. -/
theorem logKummerK1K2_consumer
    (u : principalUnits (K := SourceCompletion place)) :
    completionIsometryEquiv place
        (LeanFormal.IUT.IUTII.Frobenioid.Example36.principalUnitLog
          (K := SourceCompletion place) u) =
      LeanFormal.IUT.IUTII.Frobenioid.Example36.principalUnitLog
        (K := TargetCompletion place) (principalUnitMap place u) :=
  principalUnitLog_naturality place u

/-- The square is also available in `∀ u` form for a source consumer. -/
theorem logKummerK1K2_square_all :
    ∀ u : principalUnits (K := SourceCompletion place),
      completionIsometryEquiv place
          (LeanFormal.IUT.IUTII.Frobenioid.Example36.principalUnitLog
            (K := SourceCompletion place) u) =
        LeanFormal.IUT.IUTII.Frobenioid.Example36.principalUnitLog
          (K := TargetCompletion place) (principalUnitMap place u) :=
  fun u => logKummerK1K2_consumer place u

/-- Exact p-power scaling of the source log-Kummer square. -/
theorem logKummerK1K2_p_scaling
    (u : principalUnits (K := SourceCompletion place)) :
    completionIsometryEquiv place
        (LeanFormal.IUT.IUTII.Frobenioid.Example36.principalUnitLog
          (K := SourceCompletion place) (u ^ p)) =
      (p : TargetCompletion place) *
        completionIsometryEquiv place
          (LeanFormal.IUT.IUTII.Frobenioid.Example36.principalUnitLog
            (K := SourceCompletion place) u) := by
  have hpow : LeanFormal.IUT.IUTII.Frobenioid.Example36.principalUnitLog
        (K := SourceCompletion place) (u ^ p) =
      (p : SourceCompletion place) *
        LeanFormal.IUT.IUTII.Frobenioid.Example36.principalUnitLog
          (K := SourceCompletion place) u := by
    simpa [LeanFormal.IUT.IUTII.Frobenioid.Example36.principalUnitLog] using
      principalUnitLog_pow (K := SourceCompletion place) (p := p)
        (u : (Integers (SourceCompletion place))ˣ) u.property p
  rw [hpow, map_mul, map_natCast, logKummerK1K2_consumer place u]

/-- Exact `logShellScale p` scaling of the transported principal-unit log-Kummer
image. -/
theorem logKummerK1K2_logShellScale_scaling
    (u : principalUnits (K := SourceCompletion place)) :
    completionIsometryEquiv place
        ((logShellScale p : SourceCompletion place)⁻¹ *
          LeanFormal.IUT.IUTII.Frobenioid.Example36.principalUnitLog
            (K := SourceCompletion place) u) =
      (logShellScale p : TargetCompletion place)⁻¹ *
        LeanFormal.IUT.IUTII.Frobenioid.Example36.principalUnitLog
          (K := TargetCompletion place) (principalUnitMap place u) := by
  rw [map_mul, map_inv₀, map_natCast, logKummerK1K2_consumer place u]

end ABCBridge.LogKummerK1K2Consumer
