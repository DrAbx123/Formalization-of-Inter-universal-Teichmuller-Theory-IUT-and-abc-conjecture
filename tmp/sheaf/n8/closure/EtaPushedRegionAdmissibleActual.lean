import tmp.sheaf.n8.closure.EtaGlobalRegionIntoF

/-!
# Pushed region admissibility actual attempt

Target: PushedOpenRegionAdmissible for the one-way pushed base open ball.

Actual facts:
- pushedOpenRegion is nonempty (0 is in the base ball and baseToF 0 = 0).

Exact remaining gaps:
- measurability of the image baseToF '' baseOpenBall;
- positive finite F-Haar mass of that image.

Production supplies continuity and injectivity of completionMap /
relativeNormalizedCompletionRingHom, but no measurable-embedding theorem for
the relative normalized completion map and no measure-pushing/scaling theorem.
No fabricated measure equality is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaPushedRegionAdmissibleActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaGlobalRegionIntoF

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [MeasurableSpace (BaseCompletion X)]

/-- Actual nonemptiness: the pushed image contains 0. -/
theorem zero_mem_pushedOpenRegion : (0 : QCompletion X) ∈ pushedOpenRegion X := by
  refine ⟨0, ?_, ?_⟩
  · simp [baseOpenBall]
  · exact map_zero (baseToF X)

/-- The missing production theorem: a measure-pushing/scaling formula for the
relative normalized completion map (or an equivalent measurable-embedding plus
mass-scaling theorem).  Recorded as a Prop, not assumed. -/
def PushedRegionMeasureScalingMissing
    (μBase : Measure (BaseCompletion X))
    [Measure.IsAddHaarMeasure μBase]
    (μF : Measure (QCompletion X))
    [Measure.IsAddHaarMeasure μF] : Prop :=
  ∃ (c : ENNReal), c ≠ 0 ∧ c ≠ ⊤ ∧
    μF (pushedOpenRegion X) = c * μBase (baseOpenBall X)

end LeanFormal.IUT.N8Closure.EtaPushedRegionAdmissibleActual
