import tmp.sheaf.n8.closure.EtaShellSignedDepthActual
import tmp.sheaf.n8.closure.EtaQActual
import tmp.sheaf.n8.closure.NativeC3
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume

set_option maxHeartbeats 1200000

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaShellQUnitCandidateActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaShellDepthScalingActual
open LeanFormal.IUT.N8Closure.EtaShellSignedDepthActual
open LeanFormal.IUT.N8Closure.EtaAdditiveLogTransportActual
open LeanFormal.IUT.N8Closure.EtaCommonShellActionActual
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open LeanFormal.IUT.N8Closure.EtaQActual
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaVaryingCalibrationQOActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open scoped Padic

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : NormedField (fPlaceShell X).K :=
  NumberFieldFinitePlace.commonPrimeCompletionNormedField
    (place := nativeFPlaceAtPrime X)
local instance : IsUltrametricDist (fPlaceShell X).K :=
  NumberFieldFinitePlace.commonPrimeCompletionUltrametric
    (place := nativeFPlaceAtPrime X)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

abbrev QCompletion (X : N8NativeInput l) : Type :=
  Completion (nativeFPlaceOverBad X)

/-- Native qUnit has norm strictly less than one in the completion. -/
theorem nativeQUnit_thm_norm_lt_one :
    ‖(etaQUnit X : QCompletion X)‖ < 1 := by
  rw [etaQUnit, nativeQUnitActual, Units.val_mk0]
  exact LeanFormal.IUT.ArithmeticQPilotLogVolume.qNorm_lt_one (nativeQActual X)

/-! ## Exact missing carrier map -/

/-- Exact missing carrier map: embed completion units (including the
non-integral native qUnit) into integral shell units.  No such actual map is
provided; the norm mismatch is the obstruction. -/
def EtaQUnitToIntegralShellMap : Prop :=
  ∃ toShell : QCompletion X → (fPlaceShell X).Units,
    ∀ u : QCompletion X,
      ((toShell u).val.val : QCompletion X) = u

def EtaQUnitToIntegralShellMapGap : Prop :=
  ¬ EtaQUnitToIntegralShellMap X

end LeanFormal.IUT.N8Closure.EtaShellQUnitCandidateActual
