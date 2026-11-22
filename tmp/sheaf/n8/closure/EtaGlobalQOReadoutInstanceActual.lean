import tmp.sheaf.n8.closure.EtaQOReadoutRelationClosedActual
import tmp.sheaf.n8.closure.EtaQOClassGlobalActual
import tmp.sheaf.n8.closure.EtaGlobalRegionAtFActual
import tmp.sheaf.n8.closure.EtaPStepNormLink
import Mathlib

/-!
# Global qO readout instance actual

The canonical globalQOReadout and the actual qOClassReadout live on the same
underlying carrier closedBall 0 ||native q||, but the canonical GlobalRssAtF
measure interface is stated on K with its own MeasurableSpace/NormedField
instances, while qOClassReadout uses QCompletion.  The carrier equality and the
measure equality on the qO region are the exact instance/measure gaps.  This
file proves the readout alignment conditionally on those exact equalities; no
arbitrary measure equality is assumed.
-/

noncomputable section

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaGlobalRegionAtFActual
open LeanFormal.IUT.N8Closure.EtaGlobalRssAtF
open LeanFormal.IUT.N8Closure.EtaQOClassGlobalActual
open LeanFormal.IUT.N8Closure.EtaQOReadoutRelationClosedActual
open LeanFormal.IUT.N8Closure.EtaPStepNormLink
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace

namespace LeanFormal.IUT.N8Closure.EtaGlobalQOReadoutInstanceActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable [MeasurableSpace (QCompletion X)] [BorelSpace (QCompletion X)]
variable [ProperSpace (QCompletion X)] [IsUltrametricDist (QCompletion X)]
variable [LocallyCompactSpace (QCompletion X)]

local instance hKmeas : MeasurableSpace (EtaRssAdmissibleCorrection.K X) :=
  nativePMeasurableSpace X

local instance hKborel : BorelSpace (EtaRssAdmissibleCorrection.K X) :=
  nativePBorelSpace X

variable [ProperSpace (EtaRssAdmissibleCorrection.K X)]
  [IsUltrametricDist (EtaRssAdmissibleCorrection.K X)]
variable [Measure.IsOpenPosMeasure (Measure.addHaar : Measure (EtaRssAdmissibleCorrection.K X))]
variable [IsFiniteMeasureOnCompacts (Measure.addHaar : Measure (EtaRssAdmissibleCorrection.K X))]

/-- Exact carrier/instance gap: the canonical globalQOCarrier closed ball and
the actual qORegion are stated with different K/QCompletion instances. -/
def GlobalQOCarrierInstanceGap : Prop :=
  globalQOCarrier X = qORegion X

/-- Exact measure gap on the qO region between the canonical K Haar measure and
the actual normalized Haar μQ. -/
def GlobalQOReadoutMeasureGap
    (μK : Measure (EtaRssAdmissibleCorrection.K X)) [μK.IsAddHaarMeasure]
    (μQ : Measure (QCompletion X)) [μQ.IsAddHaarMeasure] : Prop :=
  μK (globalQOCarrier X) = μQ (qORegion X)

end LeanFormal.IUT.N8Closure.EtaGlobalQOReadoutInstanceActual
