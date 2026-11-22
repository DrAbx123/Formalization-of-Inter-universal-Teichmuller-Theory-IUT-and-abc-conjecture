import LeanFormal.IUT.Foundations.AlgebraicGeometry.LogKummerK1K2Consumer
import LeanFormal.IUT.Foundations.LocalFields.LogShellSaturation
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceLogShell
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.N8.LogCarrierK1K2
open ABCBridge.LogKummerK1K2
open ABCBridge.LogKummerK1K2Consumer

variable {F : Type} [Field F] [NumberField F] {p : ℕ} [Fact p.Prime]
  (place : FinitePlaceAtPrime F p)

local instance normalizedCompletionNormedAlgebraAtPrime :
    NormedAlgebra ℚ_[p] (NormalizedCompletion place.val) := by
  rcases place with ⟨v, hv⟩
  cases hv
  exact normalizedCompletionNormedAlgebra v

local instance normalizedCompletionFiniteAtPrime :
    FiniteDimensional ℚ_[p] (NormalizedCompletion place.val) := by
  rcases place with ⟨v, hv⟩
  cases hv
  exact normalizedCompletionFinite v

theorem logShellScale_exact :
    logShellScale p = if p = 2 then p ^ 2 else p := rfl

/-- For every integral unit, the actual source scaled unit logarithm lies in
the actual source log-shell. -/
theorem forallUnit_sourceShell_compat
    (u : (Integers (SourceCompletion place))ˣ) :
    (logShellScale p : SourceCompletion place)⁻¹ *
        unitLog (K := SourceCompletion place) u ∈
      integralLogShell (K := SourceCompletion place) (p := p) := by
  change (logShellScale p : SourceCompletion place)⁻¹ *
      unitLog (K := SourceCompletion place) u ∈
    (integralLogShell (K := SourceCompletion place) (p := p) :
      Set (SourceCompletion place))
  rw [coe_integralLogShell_eq_range (K := SourceCompletion place) (p := p)]
  exact ⟨u, rfl⟩

/-- **Exact residual for the source uniformizer/normalization comparison.**
After the K1/K2 completion isometry, the source scaled unit-log image lies in
the actual completion log-shell.  This is stated as a Prop and is not
inhabited here; no source card is introduced. -/
def sourceUniformizerNormalizationResidual : Prop :=
  ∀ u : (Integers (SourceCompletion place))ˣ,
    completionIsometryEquiv place
      ((logShellScale p : SourceCompletion place)⁻¹ *
        unitLog (K := SourceCompletion place) u) ∈
      completionLogShell place.val

/-- Conditional completion-log-shell compatibility for all units, from the
exact residual. -/
theorem forallUnit_completionLogShell_compat
    (h : sourceUniformizerNormalizationResidual (p := p) place)
    (u : (Integers (SourceCompletion place))ˣ) :
    completionIsometryEquiv place
      ((logShellScale p : SourceCompletion place)⁻¹ *
        unitLog (K := SourceCompletion place) u) ∈
      completionLogShell place.val :=
  h u

end