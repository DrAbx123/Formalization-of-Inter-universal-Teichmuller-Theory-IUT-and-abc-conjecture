import LeanFormal.IUT.Foundations.AlgebraicGeometry.LogCarrierK1K2
import LeanFormal.IUT.IUTII.Frobenioid.Example36LogDomainActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceLogShell
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

/-!
# Log-Kummer compatibility over the actual K1/K2 completion isometry

At a finite place `place` of a number field `F` at a prime `p`, the production
K1/K2 carrier has source `CommonPrimeCompletion place` and target
`NormalizedCompletion place.val`, with the actual completion ring isometry.
This file proves the principal-unit log-Kummer compatibility square and the
image compatibility of the actual source log-shell.  It uses no concrete Q5
source card and no `SourceLogKummerIdentificationCard`.
-/
namespace ABCBridge.LogKummerK1K2

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.N8.LogCarrierK1K2

universe u

variable {F : Type u} [Field F] [NumberField F] {p : ℕ} [Fact p.Prime]
  (place : FinitePlaceAtPrime F p)

local instance normalizedCompletionNormedAlgebraAtPrime :
    NormedAlgebra ℚ_[p] (NormalizedCompletion place.val) := by
  rcases place with ⟨v, hv⟩
  cases hv
  exact normalizedCompletionNormedAlgebra v

/-- The principal units at the source completion, mapped to the target
completion by the actual K1/K2 completion isometry. -/
noncomputable def principalUnitMap
    (u : principalUnits (K := SourceCompletion place)) :
    principalUnits (K := TargetCompletion place) :=
  ⟨integralUnitMap (completionIsometryEquiv place).toRingHom
      (completionIsometryEquiv_isometry place) u,
    integralUnitMap_mem_principalUnits
      (completionIsometryEquiv place).toRingHom
      (completionIsometryEquiv_isometry place) u u.property⟩

/-- **Principal-unit log-Kummer compatibility square** over the actual
completion isometry. -/
theorem principalUnitLog_naturality
    (u : principalUnits (K := SourceCompletion place)) :
    completionIsometryEquiv place
        (LeanFormal.IUT.IUTII.Frobenioid.Example36.principalUnitLog
          (K := SourceCompletion place) u) =
      LeanFormal.IUT.IUTII.Frobenioid.Example36.principalUnitLog
        (K := TargetCompletion place) (principalUnitMap place u) := by
  rw [show LeanFormal.IUT.IUTII.Frobenioid.Example36.principalUnitLog
        (K := SourceCompletion place) u =
      unitLog (K := SourceCompletion place)
        (u : (Integers (SourceCompletion place))ˣ) from
    (unitLog_eq_log1p (K := SourceCompletion place) (p := p)
      (u : (Integers (SourceCompletion place))ˣ) u.property).symm,
    show LeanFormal.IUT.IUTII.Frobenioid.Example36.principalUnitLog
        (K := TargetCompletion place) (principalUnitMap place u) =
      unitLog (K := TargetCompletion place)
        (principalUnitMap place u :
          (Integers (TargetCompletion place))ˣ) from
    (unitLog_eq_log1p (K := TargetCompletion place) (p := p)
      (principalUnitMap place u :
        (Integers (TargetCompletion place))ˣ)
      (principalUnitMap place u).property).symm]
  exact unitLog_map (p := p) (completionIsometryEquiv place).toRingHom
    (completionIsometryEquiv_isometry place) u

/-- Every actual transported source principal-unit log-Kummer value lies in
the target principal-unit log-Kummer image. -/
theorem principalUnitLog_image_compat
    (u : principalUnits (K := SourceCompletion place)) :
    completionIsometryEquiv place
        (LeanFormal.IUT.IUTII.Frobenioid.Example36.principalUnitLog
          (K := SourceCompletion place) u) ∈
      Set.range (fun v : principalUnits (K := TargetCompletion place) =>
        LeanFormal.IUT.IUTII.Frobenioid.Example36.principalUnitLog
          (K := TargetCompletion place) v) :=
  ⟨principalUnitMap place u, (principalUnitLog_naturality place u).symm⟩


/-- The actual source log-shell at the target completion is exactly the scaled
actual unit-logarithmic image. -/
theorem completionLogShell_image_compat :
    (completionLogShell place.val : Set (Completion place.val)) =
      Set.range (fun u : (CompletionIntegers place.val)ˣ =>
        (logShellScale (completionRationalPrime place.val).val :
            Completion place.val)⁻¹ * completionUnitLog place.val u) :=
  completionLogShell_eq_unitLog_range place.val

end ABCBridge.LogKummerK1K2
