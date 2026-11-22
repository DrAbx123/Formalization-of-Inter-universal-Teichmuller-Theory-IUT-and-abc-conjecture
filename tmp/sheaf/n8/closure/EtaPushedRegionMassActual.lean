import tmp.sheaf.n8.closure.EtaPushedRegionMeasurableActual

/-!
# Eta pushed region mass actual

The pushed region is compact in the actual normalized F-completion.  Therefore
its F-Haar mass is finite whenever the Haar measure is finite on compact sets.
That part is actual.

Positive mass is NOT proved: compactness alone does not imply positive Haar
mass, and the image of the lower completion under the relative completion map
can be a lower-dimensional closed subfield (measure-zero possibility when the
extension is nontrivial).  Production supplies no measure-pushing/scaling theorem
for relativeNormalizedCompletionRingHom, so positivity remains the exact gap.
No fabricated measure equality is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaPushedRegionMassActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaGlobalRegionIntoF
open LeanFormal.IUT.N8Closure.EtaPushedRegionMeasurableActual
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [MeasurableSpace (BaseCompletion X)]
variable [MeasurableSpace (CommonPrimeCompletion (nativeFPlaceAtPrime X))]
variable [BorelSpace (CommonPrimeCompletion (nativeFPlaceAtPrime X))]

/-- Actual finite mass of the pushed compact region. -/
theorem pushedRegion_mass_lt_top
    (μF : Measure (CommonPrimeCompletion (nativeFPlaceAtPrime X)))
    [Measure.IsAddHaarMeasure μF] :
    μF (pushedOpenRegionActual X) < ⊤ :=
  (isCompact_pushedOpenRegionActual X).measure_lt_top

/-- Exact positive-mass target. -/
def PushedRegionPositiveMass
    (μF : Measure (CommonPrimeCompletion (nativeFPlaceAtPrime X)))
    [Measure.IsAddHaarMeasure μF] : Prop :=
  0 < μF (pushedOpenRegionActual X)

/-- Exact admissibility: finite mass actual, positivity named. -/
def PushedRegionPositiveFiniteMass
    (μF : Measure (CommonPrimeCompletion (nativeFPlaceAtPrime X)))
    [Measure.IsAddHaarMeasure μF] : Prop :=
  0 < μF (pushedOpenRegionActual X) ∧
    μF (pushedOpenRegionActual X) < ⊤

end LeanFormal.IUT.N8Closure.EtaPushedRegionMassActual
