import tmp.sheaf.n8.closure.P6ReadoutNonarchSphereAttempt
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.WeightedNormalization
import Mathlib

/-!
# P6 procession weight/dimension donor: actual attempt

`ProcessionWeightDimensionDonor` needs a support, a Real weight and a nonzero
Real dimension on `NativePlaces`.  Production has actual weight/dimension data
only on different index types:

- `WeightedDeterminantPacket` (WeightedNormalization.lean) has actual
  `hullLogDegree`, denominator weights and normalized/weighted log-volume on a
  finite `label` type;
- `FinitePlaceSelectedPrimeWeightedVolume` has actual selected-prime tuple
  weights and `fullPrimeArithmeticTensorDimension`, indexed by tuple places;
- `ArithmeticQPilotLogVolume.selectedLogMagnitude` has only conditional
  selected-place weights.

There is no production bridge from those indices to `NativePlaces`, and no
actual native-place support/weight/dimension source.  This file therefore
registers the exact target with a theorem-level named sorry; no all-1 or
arbitrary weights are introduced.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.P6ReadoutNonarchSphereAttempt

namespace LeanFormal.IUT.N8Closure.P6ProcessionWeightDonorActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Exact target: an actual native-place support/weight/dimension donor. -/
def ProcessionWeightDimensionDonorActualTarget : Prop :=
  Nonempty (ProcessionWeightDimensionDonor (X := X))

/- Exact production weight packet shape, for the record: label-indexed, not
NativePlaces-indexed. -/
#check WeightedDeterminantPacket
#check WeightedDeterminantPacket.normalizedLogVolume
#check WeightedDeterminantPacket.weightedLogVolume

/-! ## Exact no-go for the direct construction

Production weight/dimension donors are label- or tuple-indexed.  The only
bridge would be a native-place-to-label/tuple index with exact weight and
dimension compatibility; no such production declaration exists.  Hence the
direct actual construction is no-go at the present interfaces. -/

end LeanFormal.IUT.N8Closure.P6ProcessionWeightDonorActual
