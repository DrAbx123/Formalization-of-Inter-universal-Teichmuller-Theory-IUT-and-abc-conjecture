import tmp.sheaf.n8.closure.EtaQOReadoutRelationClosedActual
import tmp.sheaf.n8.closure.EtaGlobalQOReadoutDegreeActual
import tmp.sheaf.n8.closure.EtaComparisonVaryingTarget
import tmp.sheaf.n8.closure.EtaRssSourceRegionBridge
import tmp.sheaf.n8.closure.EtaPStepNormLink
import Mathlib

/-!
# Canonical global qO readout

The canonical readout is defined directly as qOClassReadout X μQ, not by casting
qORegion to the old K/globalQOCarrier donor interface.  This file proves its
basic equalities (with qOClassReadout μQ and pushed), records the exact
open-class/corrected-readout gaps, and gives the canonical Q calibration target
for the consumer.  No arbitrary measure equality or cast is used.
-/

noncomputable section

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.C9QThetaValuesNamed
open LeanFormal.IUT.N8Closure.C9PaperClosure
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaRssNontrivialActual
open LeanFormal.IUT.N8Closure.EtaRssSourceRegionBridge
open LeanFormal.IUT.N8Closure.EtaGlobalRegionAtFActual
open LeanFormal.IUT.N8Closure.EtaGlobalRssAtF
open LeanFormal.IUT.N8Closure.EtaQOClassGlobalActual
open LeanFormal.IUT.N8Closure.EtaQOReadoutRelationClosedActual
open LeanFormal.IUT.N8Closure.EtaContinuousAddEquivRecordActual2
open LeanFormal.IUT.N8Closure.EtaNormalizedHaarBothActual
open LeanFormal.IUT.N8Closure.EtaGlobalQOReadoutDegreeActual
open LeanFormal.IUT.N8Closure.EtaComparisonVaryingTarget
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace

namespace LeanFormal.IUT.N8Closure.EtaGlobalQOReadoutCanonical

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable [MeasurableSpace (QCompletion X)] [BorelSpace (QCompletion X)]
variable [ProperSpace (QCompletion X)] [IsUltrametricDist (QCompletion X)]
variable [LocallyCompactSpace (QCompletion X)]

local instance hKmeas : MeasurableSpace (EtaRssAdmissibleCorrection.K X) :=
  LeanFormal.IUT.N8Closure.EtaPStepNormLink.nativePMeasurableSpace X

local instance hKborel : BorelSpace (EtaRssAdmissibleCorrection.K X) :=
  LeanFormal.IUT.N8Closure.EtaPStepNormLink.nativePBorelSpace X

variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
  [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
  [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
  (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
  [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- Canonical global qO readout: the actual qOClassReadout of the normalized
Haar μQ.  This bypasses the old K/globalQOCarrier donor interface. -/
noncomputable instance μQ_isHaar : (μQ X).IsAddHaarMeasure := by
  rw [μQ]
  exact Measure.IsAddHaarMeasure.smul _
    (ENNReal.inv_ne_zero.mpr (massQ_pos_lt_top X).2.ne)
    (ENNReal.inv_ne_top.mpr (massQ_pos_lt_top X).1.ne')

noncomputable def canonicalGlobalQOReadout : ℝ :=
  qOClassReadout X (μQ X)

/-- The canonical readout is definitionally qOClassReadout μQ. -/
theorem canonicalGlobalQOReadout_eq :
    canonicalGlobalQOReadout X = qOClassReadout X (μQ X) :=
  rfl

/-- Exact gap to the old open-class consumer calibration. -/
def CanonicalToOpenClassReadoutGap (K : Type u) [NormedField K]
    [MeasurableSpace K] [BorelSpace K] [IsUltrametricDist K] [ProperSpace K]
    (muK : Measure K) [Measure.IsAddHaarMeasure muK] : Prop :=
  canonicalGlobalQOReadout X =
    logVolumeReadout (K := K) (mu := muK) (sourceOpenClass (K := K) (mu := muK))

/-- Exact gap to the corrected normalized readout from the actual degree file. -/
def CanonicalToCorrectedReadoutGap : Prop :=
  canonicalGlobalQOReadout X = correctedNormalizedGlobalQOReadout X

/-- Canonical Q calibration target for the consumer: O.Q is the canonical
actual qO readout. -/
def EtaVaryingQCalibrationCanonical (O : PaperC9Output (X := X) mu) : Prop :=
  O.Q = canonicalGlobalQOReadout X

/-- Canonical Q calibration is definitionally the canonical readout equality;
it is not the old open-class calibration. -/
theorem etaVaryingQCalibrationCanonical_iff (O : PaperC9Output (X := X) mu) :
    EtaVaryingQCalibrationCanonical (X := X) (mu := mu) O ↔
      O.Q = canonicalGlobalQOReadout X :=
  Iff.rfl

end LeanFormal.IUT.N8Closure.EtaGlobalQOReadoutCanonical
