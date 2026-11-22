import tmp.sheaf.n8.closure.EtaAnabToVaryingRss
import tmp.sheaf.n8.closure.EtaSourceActionConcrete
import Mathlib

/-!
# ETA source-region extraction: exact bridge gap

The source evaluation lands in a function-valued commutative value monoid, not
in a measurable subset of a local field K.  Extracting

  Rval -> PositiveFiniteRegion K

therefore requires an explicit value-monoid -> K bridge plus a nonconstant
actual region family.  This file records that bridge and constructs the
varying-Rss candidate conditionally; no arbitrary region is chosen.
-/

noncomputable section

namespace ABCBridge.N8.EtaSourceRegionExtraction

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open ABCBridge.N8.EtaSourceActionConcrete
open ABCBridge.N8.EtaAnabToVaryingRss
open LeanFormal.IUT.N8Closure.EtaRssNontrivialActual
open LeanFormal.IUT.N8Closure.EtaValueGroupLineActual
open ABCBridge.N8.C4Actual

universe ua uv upi umon ui uL uK uM

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {Label : Type uL} [Group Label]
variable {C4 : SourceWitnessedOutputData (l := l) (V := V) I Label}
variable {X : N8NativeInput l}
variable {n : ThetaPilotCarrier l}
variable {x : I.ThetaPilotPoint C4.place.v}

/-- The source theta-pilot carrier is function-valued. -/
theorem sourceThetaPilotPoint_is_function_valued :
    I.ThetaPilotPoint C4.place.v =
      (ThetaPilotCarrier l × SignedLabel l.value →
        I.ValueMonoidAt 0 0 C4.place.v) :=
  rfl

/-- Exact missing bridge: a value-monoid -> K map plus an actual nonconstant
region family on Rval.  This is a donor/structure, not an arbitrary map. -/
structure SourceValueToKRegionBridge (M : Type uM)
    (K : Type uK) [NormedField K] [MeasurableSpace K] [BorelSpace K]
    [IsUltrametricDist K] [ProperSpace K]
    (mu : Measure K) [Measure.IsAddHaarMeasure mu] where
  toK : M → K
  regionOf : Rval → PositiveFiniteRegion K mu
  nonconstant : ∃ a b : Rval,
    regionClass (K := K) (mu := mu) (regionOf a) ≠
      regionClass (K := K) (mu := mu) (regionOf b)

/-- Conditional extraction: from the bridge, get the varying-Rss candidate. -/
noncomputable def etaSourceRegionExtractionCandidate
    {M : Type uM}
    {K : Type uK} [NormedField K] [MeasurableSpace K] [BorelSpace K]
    [IsUltrametricDist K] [ProperSpace K]
    {mu : Measure K} [Measure.IsAddHaarMeasure mu]
    (A : EtaSourceActionConcrete C4 X n x)
    (B : SourceValueToKRegionBridge M K mu) :
    EtaAnabToVaryingRssCandidate (K := K) (mu := mu) :=
  etaAnabToVaryingRssCandidateOf (K := K) (mu := mu) B.regionOf B.nonconstant

/-- Conditional nonconstancy of the extracted candidate. -/
theorem etaSourceRegionExtractionCandidate_nonconstant
    {M : Type uM}
    {K : Type uK} [NormedField K] [MeasurableSpace K] [BorelSpace K]
    [IsUltrametricDist K] [ProperSpace K]
    {mu : Measure K} [Measure.IsAddHaarMeasure mu]
    (A : EtaSourceActionConcrete C4 X n x)
    (B : SourceValueToKRegionBridge M K mu) :
    ∃ a b : Rval,
      (etaSourceRegionExtractionCandidate (X := X) (M := M) A B).classOf a ≠
        (etaSourceRegionExtractionCandidate (X := X) (M := M) A B).classOf b :=
  (etaSourceRegionExtractionCandidate (X := X) (M := M) A B).nonconstant

/-- Exact gap: the value-monoid -> K bridge has no production inhabitant.
The source value monoid is not a field/normed/measurable space; the missing
bridge is precisely toK together with a nonconstant actual region family. -/
def SourceValueToKRegionBridgeGap (M : Type uM)
    (K : Type uK) [NormedField K] [MeasurableSpace K] [BorelSpace K]
    [IsUltrametricDist K] [ProperSpace K]
    (mu : Measure K) [Measure.IsAddHaarMeasure mu] : Prop :=
  Nonempty (SourceValueToKRegionBridge M K mu)

end ABCBridge.N8.EtaSourceRegionExtraction
