import LeanFormal.IUT.Foundations.AlgebraicGeometry.LogSourceK1K2Consumer
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceLogShell

/-! Link the combined source K1/K2 square to the actual completionLogShell. -/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LeanFormal.N8.LogSourceShellConsumer

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.N8.LogCarrierK1K2
open LeanFormal.N8.LogSourceK1K2Consumer
open ABCBridge.LogKummerK1K2

variable {F : Type*} [Field F] [NumberField F] {p : Nat} [Fact p.Prime]

local instance normalizedCompletionNormedAlgebraAtPrime
    (place : FinitePlaceAtPrime F p) :
    NormedAlgebra ℚ_[p] (NormalizedCompletion place.val) := by
  rcases place with ⟨v, hv⟩
  cases hv
  exact normalizedCompletionNormedAlgebra v

variable (place : FinitePlaceAtPrime F p)

theorem principalUnitLog_eq_unitLog
    (u : principalUnits (K := SourceCompletion place)) :
    principalUnitLog (K := SourceCompletion place) u =
      unitLog (K := SourceCompletion place) (u : (Integers (SourceCompletion place))ˣ) :=
  (unitLog_eq_log1p (K := SourceCompletion place) (p := p)
    (u : (Integers (SourceCompletion place))ˣ) u.property).symm

theorem target_principalUnitLog_eq_unitLog
    (u : principalUnits (K := TargetCompletion place)) :
    principalUnitLog (K := TargetCompletion place) u =
      unitLog (K := TargetCompletion place) (u : (Integers (TargetCompletion place))ˣ) :=
  (unitLog_eq_log1p (K := TargetCompletion place) (p := p)
    (u : (Integers (TargetCompletion place))ˣ) u.property).symm

abbrev sourceScaledLog (u : principalUnits (K := SourceCompletion place)) :
    SourceCompletion place :=
  (logShellScale p : SourceCompletion place)⁻¹ *
    principalUnitLog (K := SourceCompletion place) u

abbrev targetScaledLog (u : principalUnits (K := SourceCompletion place)) :
    TargetCompletion place :=
  (logShellScale p : TargetCompletion place)⁻¹ *
    principalUnitLog (K := TargetCompletion place) (principalUnitMap place u)

/-- The source scaled log lies in the actual normalized source log-shell; the
production completionLogShell is its image under the normalized completion
isomorphism. -/
theorem sourceScaledLog_mem_integralLogShell
    (u : principalUnits (K := SourceCompletion place)) :
    sourceScaledLog place u ∈ integralLogShell (K := SourceCompletion place) (p := p) := by
  refine ⟨(u : (Integers (SourceCompletion place))ˣ), ?_⟩
  dsimp only [sourceScaledLog]
  rw [principalUnitLog_eq_unitLog]

theorem targetScaledLog_mem_integralLogShell
    (u : principalUnits (K := SourceCompletion place)) :
    targetScaledLog place u ∈ integralLogShell (K := TargetCompletion place) (p := p) := by
  refine ⟨((principalUnitMap place u : principalUnits (K := TargetCompletion place)) :
      (Integers (TargetCompletion place))ˣ), ?_⟩
  dsimp only [targetScaledLog]
  rw [target_principalUnitLog_eq_unitLog]

/-- Forall principal units: the transported scaled log-square plus membership of
both sides in the actual normalized log-shells. -/
theorem source_shell_consumer_all :
    ∀ u : principalUnits (K := SourceCompletion place),
      completionIsometryEquiv place (sourceScaledLog place u) = targetScaledLog place u ∧
      sourceScaledLog place u ∈ integralLogShell (K := SourceCompletion place) (p := p) ∧
      targetScaledLog place u ∈ integralLogShell (K := TargetCompletion place) (p := p) := by
  intro u
  exact ⟨source_logShellScale_scaling_all place u,
    sourceScaledLog_mem_integralLogShell place u,
    targetScaledLog_mem_integralLogShell place u⟩

theorem source_shell_logShellScale_eq :
    logShellScale p = if p = 2 then p ^ 2 else p := rfl

/-- The actual completionLogShell is exactly the normalized-isomorphism image of
the normalized integral log-shell; this is the shell consumer link. -/
theorem source_shell_completionLogShell_image :
    (completionLogShell (place : NumberField.FinitePlace F) :
        Set (Completion (place : NumberField.FinitePlace F))) =
      normalizedCompletionRingEquiv (place : NumberField.FinitePlace F) ''
        (integralLogShell (K := NormalizedCompletion (place : NumberField.FinitePlace F))
          (p := (completionRationalPrime (place : NumberField.FinitePlace F)).val) :
            Set (NormalizedCompletion (place : NumberField.FinitePlace F))) := rfl

end LeanFormal.N8.LogSourceShellConsumer
