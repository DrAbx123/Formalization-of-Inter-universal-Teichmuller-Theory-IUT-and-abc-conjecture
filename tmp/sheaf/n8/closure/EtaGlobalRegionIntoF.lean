import tmp.sheaf.n8.closure.EtaQRegionRepresentation
import tmp.sheaf.n8.closure.C3TensorTargetCorrection
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceRelativeNormalizedCompletion

/-!
# Eta global base region into F (one-way)

Production has only the one-way completion map from the base Fmod completion to
the native F-completion:

  relativeNormalizedCompletionRingHom : CommonPrimeCompletion base -> CommonPrimeCompletion F.

This file defines that actual one-way map and pushes an actual base unit-ball
region to the F-completion.  It does NOT introduce a reverse F -> Fmod map.

Pushing measure/admissibility to the F side is the exact remaining gap:
production has no measure-scaling theorem for relativeNormalizedCompletionRingHom.
The qO comparison on the F-side Rss is therefore also an exact gap.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaGlobalRegionIntoF

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The base Fmod place under the native F-place. -/
noncomputable abbrev baseRelativePlace : FinitePlaceAtPrime X.S.arithmetic.Fmod (nativePrime X) :=
  relativeCommonPrimePlace (k := X.S.arithmetic.Fmod) (nativeFPlaceAtPrime X)

/-- Base Fmod completion. -/
abbrev BaseCompletion : Type _ := CommonPrimeCompletion (baseRelativePlace X)

/-- Actual one-way ring map base Fmod completion -> q/F completion. -/
noncomputable def baseToF : BaseCompletion X →+*
    CommonPrimeCompletion (nativeFPlaceAtPrime X) :=
  relativeNormalizedCompletionRingHom (k := X.S.arithmetic.Fmod)
    (place := nativeFPlaceAtPrime X)

/-- Actual base open unit ball. -/
def baseOpenBall : Set (BaseCompletion X) :=
  Metric.ball (0 : BaseCompletion X) (1 : ℝ)

/-- Actual pushed F-side region. -/
def pushedOpenRegion : Set (QCompletion X) :=
  baseToF X '' baseOpenBall X

/-- Exact admissibility target for the pushed region: measurable + positive
finite F-Haar mass. -/
def PushedOpenRegionAdmissible
    (μF : Measure (QCompletion X)) [Measure.IsAddHaarMeasure μF] : Prop :=
  MeasurableSet (pushedOpenRegion X) ∧
    0 < μF (pushedOpenRegion X) ∧ μF (pushedOpenRegion X) < ⊤

/-- Exact F-side qO comparison target: the pushed region and the actual qO region
have the same F-Haar mass (or the two values are recorded separately). -/
def PushedClassQOComparison
    (μF : Measure (QCompletion X)) [Measure.IsAddHaarMeasure μF] : Prop :=
  μF (pushedOpenRegion X) = μF (qORegion X)

end LeanFormal.IUT.N8Closure.EtaGlobalRegionIntoF
