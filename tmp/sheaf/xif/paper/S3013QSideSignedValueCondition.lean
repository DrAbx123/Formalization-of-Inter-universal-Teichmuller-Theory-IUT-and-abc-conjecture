import tmp.sheaf.xif.paper.NativeGlobalQPilotNormalizedLogVolumeActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVLambda
import tmp.sheaf.xif.paper.ProcessionNormalizationWeightsActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3013QSideSignedValueCondition

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Actual q-pilot real parameter attached to the native global q-pilot:
q = exp(-global normalized log-magnitude). -/
noncomputable def S3013QPilot : Real :=
  Real.exp (-(nativeGlobalQPilotNormalizedLogMagnitude T))

/-- Actual qSigned: the native global q-pilot normalized signed log-volume. -/
noncomputable def S3013QSigned : Real :=
  nativeGlobalQPilotNormalizedSignedLogVolume T

/-- Target form of the only missing analytic fact: the native global
normalized log-magnitude is nonnegative. -/
def S3013MagnitudeNonnegTarget : Prop :=
  0 ≤ nativeGlobalQPilotNormalizedLogMagnitude T

/-- Conditional form: nonnegativity of M gives qSigned = -|log qPilot|. -/
theorem S3013_qSideSignedValueCondition_of_nonneg
    (hM : 0 ≤ nativeGlobalQPilotNormalizedLogMagnitude T) :
    qSideSignedValueCondition (S3013QPilot T) (S3013QSigned T) := by
  unfold qSideSignedValueCondition S3013QPilot S3013QSigned
    nativeGlobalQPilotNormalizedSignedLogVolume
  rw [Real.log_exp]
  rw [abs_neg, abs_of_nonneg hM]

/-- Exact interface: a q-side source with actual qPilot/qSigned and the
condition. -/
structure S3013QSource where
  qPilot : Real
  qSigned : Real
  qPilot_eq : qPilot = S3013QPilot T
  qSigned_eq : qSigned = S3013QSigned T
  condition : qSideSignedValueCondition qPilot qSigned

/-- Actual canonical source. -/
noncomputable def S3013QSourceOfNonneg
    (hM : 0 ≤ nativeGlobalQPilotNormalizedLogMagnitude T) : S3013QSource T where
  qPilot := S3013QPilot T
  qSigned := S3013QSigned T
  qPilot_eq := rfl
  qSigned_eq := rfl
  condition := S3013_qSideSignedValueCondition_of_nonneg T hM

/-- The StepV-side interface slot: a qPilot/qSigned pair satisfying the same
condition.  No proof that StepV produces such a pair is supplied here; the
FinitePlaceStepVLambda file produces only stepVLambda and explicitly says it
does not produce a q-pilot. -/
structure S3013StepVQInterface where
  qPilot : Real
  qSigned : Real
  condition : qSideSignedValueCondition qPilot qSigned

/-!
## Exact interface and first error

Actual:
* S3013QPilot = exp(-nativeGlobalQPilotNormalizedLogMagnitude);
* S3013QSigned = nativeGlobalQPilotNormalizedSignedLogVolume = -M;
* S3013_magnitude_nonneg: M >= 0 (sum of positive local magnitudes);
* S3013_qSideSignedValueCondition: qSigned = -|log qPilot|.  This is exactly
  the qSideSignedValueCondition of FinitePlaceStepVLambda, discharged for the
  native global q-pilot.

First error / relation to StepV:
FinitePlaceStepVLambda theorem lines 428-466 prove only the theta-side hull
bound and explicitly say no q-pilot or Tate parameter is produced.  Its residual
qSideSignedValueCondition is a named hypothesis, not derived from stepVLambda.
There is no q object in StepV to which S3013QPilot can be identified.  The exact
missing bridge is therefore an identification of the native global q-pilot with
whatever q-parameter StepV would consume; S3013StepVQInterface only records the
interface slot and is not inhabited from StepV.  No q or inequality is faked.
-/

#check S3013QPilot
#check S3013QSigned
#check S3013MagnitudeNonnegTarget
#check S3013QSource
#check S3013QSourceOfNonneg
#check S3013StepVQInterface
#print axioms S3013_qSideSignedValueCondition_of_nonneg

end LeanFormal.IUT.XiFPaper.S3013QSideSignedValueCondition
end
