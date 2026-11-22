import tmp.sheaf.n8.closure.EtaSourceActionConcrete
import tmp.sheaf.n8.closure.EtaRssNontrivialActual
import tmp.sheaf.n8.closure.EtaValueGroupLineActual
import Mathlib

/-!
# etaAnab to the actual varying-region Rss

The previous fixed-shell candidate is rejected: a fixed shell/volume carrier is
not the LANA varying-region Rss.  This file uses the actual equal-volume
quotient

  EtaRssNontrivialActual.Rss K mu

of positive finite measurable regions in a nonarchimedean local field.

A candidate map is an actual function

  classOf : Rval -> Rss K mu

with a region family regionOf : Rval -> PositiveFiniteRegion K mu and
classOf a = [regionOf a].  Nonconstancy is a separate actual witness, not a
fixed singleton.

Exact gap: the source action's eval returns a function-valued ThetaPilotPoint
(on ThetaPilotCarrier -> value monoid), not a measurable subset of K.  There is
no production regionOf/classOf from EtaSourceActionConcrete.eval/region to
K-regions.  This file therefore constructs the actual varying carrier and the
conditional map/nonconstancy theorem, and records the missing source region
family as the exact gap; it does not choose an arbitrary region map.
-/

noncomputable section

namespace ABCBridge.N8.EtaAnabToVaryingRss

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.EtaValueGroupLineActual
open LeanFormal.IUT.N8Closure.EtaRssNontrivialActual

universe u1 u2 u3 u

variable {K : Type u} [NormedField K] [MeasurableSpace K] [BorelSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable (mu : Measure K) [Measure.IsAddHaarMeasure mu]

/-- The actual varying-region Rss (equal-volume quotient). -/
abbrev VaryingRss : Type _ := Rss (K := K) mu

/-- The quotient class of an actual positive finite region. -/
noncomputable def regionClass (A : PositiveFiniteRegion K mu) : VaryingRss (K := K) mu :=
  Quotient.mk (SameVolume (K := K) mu) A

/-- The actual varying-region Rss is nontrivial. -/
theorem varyingRss_nontrivial : Nontrivial (VaryingRss (K := K) mu) :=
  etaRss_nontrivial (K := K) (mu := mu)

/-- A candidate etaAnab map to the varying Rss, together with its actual
region family and a nonconstancy witness. -/
structure EtaAnabToVaryingRssCandidate where
  /-- Actual region family on Rval. -/
  regionOf : Rval → PositiveFiniteRegion K mu
  /-- Actual quotient class map. -/
  classOf : Rval → VaryingRss (K := K) mu
  classOf_eq : ∀ a, classOf a = regionClass (K := K) (mu := mu) (regionOf a)
  /-- Actual nonconstancy witness; no fixed singleton. -/
  nonconstant : ∃ a b : Rval, classOf a ≠ classOf b

/-- Conditional actual candidate: a supplied actual region family plus a
nonconstancy witness yields the varying-Rss map. -/
noncomputable def etaAnabToVaryingRssCandidateOf
    (regionOf : Rval → PositiveFiniteRegion K mu)
    (h : ∃ a b : Rval, regionClass (K := K) (mu := mu) (regionOf a) ≠
      regionClass (K := K) (mu := mu) (regionOf b)) :
    EtaAnabToVaryingRssCandidate (K := K) (mu := mu) where
  regionOf := regionOf
  classOf := fun a => regionClass (K := K) (mu := mu) (regionOf a)
  classOf_eq := fun a => rfl
  nonconstant := h

/-- Nonconstancy of any actual varying-Rss candidate. -/
theorem etaAnabToVaryingRssCandidate_nonconstant
    (C : EtaAnabToVaryingRssCandidate (K := K) (mu := mu)) :
    ∃ a b : Rval, C.classOf a ≠ C.classOf b :=
  C.nonconstant

/-- The exact gap: an actual source-compatible region family from
EtaSourceActionConcrete.eval/region to K-regions is absent.  The source eval
lands in the function-valued ThetaPilotPoint carrier, so no region map is
derived here.  This is a recorded interface gap, not an arbitrary map. -/
def EtaAnabVaryingRssSourceRegionGap : Prop :=
  Nonempty (EtaAnabToVaryingRssCandidate (K := K) (mu := mu))

end ABCBridge.N8.EtaAnabToVaryingRss
