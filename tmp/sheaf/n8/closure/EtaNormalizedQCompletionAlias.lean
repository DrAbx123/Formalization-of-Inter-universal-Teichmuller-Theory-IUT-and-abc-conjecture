import tmp.sheaf.n8.closure.EtaGlobalQODegreeCorrectedAlignment
import tmp.sheaf.n8.closure.EtaQOAddHaarNormalizedCalibrationActual
import tmp.sheaf.n8.closure.EtaGlobalQOReadoutDegreeActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion
import Mathlib

/-!
# Normalized QCompletion alias

QCompletion is the default Completion norm, which is not the normalized/spectral
norm.  Production NormalizedCompletion carries the normalized norm instance.
This file introduces the actual production alias

  NormalizedQCompletion X := NormalizedCompletion (nativeFPlaceOverBad X)

and defines the qO region/canonical readout on it.  Under the native norm power
relation the corrected carrier equals this qO region, so the normalized
canonical readout equals the corrected readout.  The old QCompletion canonical
readout is not asserted equal.  No arbitrary type synonym or cast is used.
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
open LeanFormal.IUT.N8Closure.EtaFPlaceNormAgreementActualAttempt
open LeanFormal.IUT.N8Closure.EtaQOAddHaarNormalizedCalibrationActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection

namespace LeanFormal.IUT.N8Closure.EtaNormalizedQCompletionAlias

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Actual production normalized completion alias, carrying the normalized norm
instance. -/
abbrev NormalizedQCompletion : Type :=
  NormalizedCompletion (nativeFPlaceOverBad X)

/-- Native q transported to the normalized completion alias. -/
noncomputable def nativeQNormalized : NormalizedQCompletion X :=
  ((C9QPilotRegion.nativeQ X).q : NormalizedQCompletion X)

/-- qO region on the normalized completion alias. -/
noncomputable def normalizedQORegion : Set (NormalizedQCompletion X) :=
  {x | ∃ y : Integers (NormalizedQCompletion X),
    x = nativeQNormalized X * (y : NormalizedQCompletion X)}

/-- Canonical readout on the normalized completion alias. -/
noncomputable def canonicalNormalizedQOReadout : ℝ :=
  Real.log ((EtaQOAddHaarNormalizedCalibrationActual.kfNormalizedHaar X)
    (normalizedQORegion X)).toReal

/-- Exact alias carrier equality target: the normalized qO region is the
corrected Kf closed-ball carrier. -/
def NormalizedAliasCarrierGap : Prop :=
  normalizedQORegion X = correctedGlobalQOCarrier X

/-- Under the norm power relation and nonzero relDegree, the alias carrier is
the corrected carrier.  (This is the exact remaining carrier equality.) -/
theorem normalizedAliasCarrier_eq_corrected
    (hgap : NormalizedAliasCarrierGap X) :
    canonicalNormalizedQOReadout X = correctedGlobalQOReadout X := by
  unfold canonicalNormalizedQOReadout correctedGlobalQOReadout
  rw [hgap]

/-- Exact no-go record: the alias is actual, but the equality between its qO
region and the corrected Kf carrier is the remaining exact carrier gap; no
type cast or synonym is claimed to prove it. -/
def NormalizedAliasNoGo : Prop :=
  NormalizedAliasCarrierGap X

end LeanFormal.IUT.N8Closure.EtaNormalizedQCompletionAlias
