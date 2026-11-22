import tmp.sheaf.n8.closure.EtaGlobalRegionIntoF
import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# Pushed region measurability actual (normalized F-completion)

The one-way map baseToF lands in the normalized F-completion
CommonPrimeCompletion (nativeFPlaceAtPrime X).  The base open unit ball is
compact there (nonarch balls are clopen, contained in the compact closed ball),
and baseToF is continuous, so the pushed image is compact, hence measurable.

This proves measurability in the actual normalized F-completion without any
measure-scaling theorem.  Transporting the same set to the raw QCompletion is a
separate normalization/homeomorphism obligation, not a definitional cast.
-/

set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaPushedRegionMeasurableActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaGlobalRegionIntoF
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [MeasurableSpace (BaseCompletion X)]
variable [MeasurableSpace (CommonPrimeCompletion (nativeFPlaceAtPrime X))]
variable [BorelSpace (CommonPrimeCompletion (nativeFPlaceAtPrime X))]

/-- Actual pushed region in the normalized F-completion. -/
def pushedOpenRegionActual :
    Set (CommonPrimeCompletion (nativeFPlaceAtPrime X)) :=
  baseToF X '' baseOpenBall X

/-- The actual base open unit ball is compact. -/
theorem isCompact_baseOpenBall : IsCompact (baseOpenBall X) := by
  have hclosed : IsClosed (baseOpenBall X) :=
    IsUltrametricDist.isClosed_ball (0 : BaseCompletion X) (1 : ℝ)
  exact (isCompact_closedBall (0 : BaseCompletion X) (1 : ℝ)).of_isClosed_subset
    hclosed Metric.ball_subset_closedBall

/-- Actual pushed region is compact: continuous image of a compact set. -/
theorem isCompact_pushedOpenRegionActual :
    IsCompact (pushedOpenRegionActual X) :=
  (isCompact_baseOpenBall X).image
    (continuous_relativeNormalizedCompletionRingHom (k := X.S.arithmetic.Fmod)
      (place := nativeFPlaceAtPrime X))

/-- Actual measurability of the pushed normalized F-region. -/
theorem pushedOpenRegionActual_measurable :
    MeasurableSet (pushedOpenRegionActual X) :=
  (isCompact_pushedOpenRegionActual X).measurableSet

/-- Actual admissibility target: measurability is proved; positive finite mass is
the remaining measure-scaling gap. -/
def PushedOpenRegionActualAdmissible
    (μF : Measure (CommonPrimeCompletion (nativeFPlaceAtPrime X)))
    [Measure.IsAddHaarMeasure μF] : Prop :=
  MeasurableSet (pushedOpenRegionActual X) ∧
    0 < μF (pushedOpenRegionActual X) ∧ μF (pushedOpenRegionActual X) < ⊤

end LeanFormal.IUT.N8Closure.EtaPushedRegionMeasurableActual
