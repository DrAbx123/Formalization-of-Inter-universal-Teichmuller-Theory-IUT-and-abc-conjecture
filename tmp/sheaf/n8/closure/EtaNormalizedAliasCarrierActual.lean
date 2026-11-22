import tmp.sheaf.n8.closure.EtaNormalizedQCompletionAlias
import tmp.sheaf.n8.closure.EtaGlobalQODegreeCorrectedAlignment
import tmp.sheaf.n8.closure.EtaKfClosedBallEqQORegion
import tmp.sheaf.n8.closure.EtaRssAdmissibleCorrection
import tmp.sheaf.n8.closure.EtaQORegionMassNormFromScaling
import Mathlib

/-!
# Normalized alias carrier actual

The production NormalizedCompletion and CommonPrimeCompletion norms are rfl
equal.  This file attempts to identify the normalized alias qO region with the
corrected Kf carrier.  The qO region on the normalized alias is the same
q * Integers region, and the corrected carrier equals the Kf qO region under the
native norm power relation.  If the type/norm bridge is accepted definitionally,
the readouts agree; otherwise the exact carrier bridge is recorded.  No
arbitrary cast is used.
-/

noncomputable section

set_option maxHeartbeats 800000

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaGlobalRegionAtFActual
open LeanFormal.IUT.N8Closure.EtaGlobalQOReadoutDegreeActual
open LeanFormal.IUT.N8Closure.EtaGlobalQODegreeCorrectedAlignment
open LeanFormal.IUT.N8Closure.EtaKfClosedBallEqQORegion
open LeanFormal.IUT.N8Closure.EtaNormalizedQCompletionAlias
open LeanFormal.IUT.N8Closure.EtaRssAdmissibleCorrection
open LeanFormal.IUT.N8Closure.EtaQORegionMassNormFromScaling
open LeanFormal.IUT.N8Closure.EtaQOAddHaarNormalizedCalibrationActual
open LeanFormal.IUT.N8Closure.EtaFPlaceNormAgreementActualAttempt
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection

namespace LeanFormal.IUT.N8Closure.EtaNormalizedAliasCarrierActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable [MeasurableSpace (QCompletion X)] [BorelSpace (QCompletion X)]
variable [ProperSpace (QCompletion X)] [IsUltrametricDist (QCompletion X)]
variable [LocallyCompactSpace (QCompletion X)]

local instance hKmeas : MeasurableSpace (EtaRssAdmissibleCorrection.K X) :=
  EtaPStepNormLink.nativePMeasurableSpace X

local instance hKborel : BorelSpace (EtaRssAdmissibleCorrection.K X) :=
  EtaPStepNormLink.nativePBorelSpace X

/-- Production NormalizedCompletion/CommonPrimeCompletion norm agreement. -/
theorem normalizedCompletion_norm_eq_commonPrime :
    (inferInstance : Norm (NormalizedQCompletion X)) =
      (inferInstance : Norm (EtaRssAdmissibleCorrection.K X)) :=
  rfl

/-- Exact remaining alias carrier gap: no production theorem identifies the
normalized qO region (q * Integers on NormalizedQCompletion) with the corrected
Kf carrier.  The set-level membership forms are q*Integers on the normalized
alias versus the corrected closedBall, and the available norm rfl only compares
the NormalizedCompletion and CommonPrimeCompletion norms, not the set transport.
No arbitrary cast is used. -/
def NormalizedAliasCarrierGapActual : Prop :=
  NormalizedAliasCarrierGap X

/-- Exact no-go for the readout equality: it is precisely the alias carrier gap
above. -/
def NormalizedAliasReadoutNoGo : Prop :=
  NormalizedAliasCarrierGap X → canonicalNormalizedQOReadout X = correctedGlobalQOReadout X

end LeanFormal.IUT.N8Closure.EtaNormalizedAliasCarrierActual
