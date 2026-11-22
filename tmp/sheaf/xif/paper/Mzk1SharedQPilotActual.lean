import tmp.sheaf.xif.paper.Mzk1IVThm110N5Actual
/-! Shared actual native q-pilot source object.

This provides the native q-pilot pair from the actual global data:
`qPilot = exp(-M)`, `qSigned = -M` with `M = nativeGlobalQPilotNormalizedLogMagnitude T`,
and the proved signed condition.  It does **not** identify this pair with the StepV/floor
certificate's engineered qSigned `min(hullLog,-1)`; that bridge is the remaining N5/R1 object. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1SharedQPilotActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S3013QSideSignedValueCondition
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110N5Actual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
/-- Native global q-pilot source paired with the proved signed condition. -/
structure SharedNativeQPilotSource where
  qPilot : Real
  qSigned : Real
  qPilot_eq : qPilot = S3013QPilot T
  qSigned_eq : qSigned = S3013QSigned T
  condition : qSideSignedValueCondition qPilot qSigned
/-- The actual native source object. -/
noncomputable def actualSharedNativeQPilotSource : SharedNativeQPilotSource T where
  qPilot := S3013QPilot T
  qSigned := S3013QSigned T
  qPilot_eq := rfl
  qSigned_eq := rfl
  condition := native_qSideSignedValueCondition_actual T
/-- The actual qPilot has positive exponential form and signed log equals `-M`. -/
theorem actualSharedNativeQPilotSource_qPilot_eq :
    (actualSharedNativeQPilotSource T).qPilot =
      Real.exp (-(nativeGlobalQPilotNormalizedLogMagnitude T)) := rfl
/-- The actual qSigned is the native normalized signed log volume. -/
theorem actualSharedNativeQPilotSource_qSigned_eq :
    (actualSharedNativeQPilotSource T).qSigned =
      nativeGlobalQPilotNormalizedSignedLogVolume T := rfl
/-- Exact remaining bridge, shared N5/R1: identify this native pair with the StepV/floor
certificate qSigned/qPilot and with the C3 q witness. -/
def sharedNativeToStepVAndC3Gap : List String :=
  [ "identify S3013QPilot/S3013QSigned with StepV/floor certificate qPilot/qSigned (floor qSigned = min(hullLog,-1))",
    "identify S3013QPilot with C3 q witness P.line.C3.q.q = qVFamNormalizedGenerator T b",
    "transport Bad place/index/weight match from T to the C3/StepV q object" ]
theorem sharedNativeToStepVAndC3Gap_length : sharedNativeToStepVAndC3Gap.length = 3 := rfl
#check actualSharedNativeQPilotSource
#check actualSharedNativeQPilotSource_qPilot_eq
#check actualSharedNativeQPilotSource_qSigned_eq
end LeanFormal.IUT.XiFPaper.Mzk1SharedQPilotActual
end
