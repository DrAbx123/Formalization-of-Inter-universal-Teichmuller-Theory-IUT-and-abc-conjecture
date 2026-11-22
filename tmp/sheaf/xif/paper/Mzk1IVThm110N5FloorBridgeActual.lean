import tmp.sheaf.xif.paper.Mzk1IVThm110N5Actual
import tmp.sheaf.xif.paper.Mzk1IVThm110HCor312FloorActual
/-! Bridge from the actual floor certificate qSigned to the native q-pilot.

The native N5 condition is already GREEN.  If the floor certificate's qSigned is
identified with the native signed log-volume, the same condition transfers to the
floor certificate.  The remaining object is exactly that equality (plus the C3 q
witness identification with mainline.R1). -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110N5FloorBridgeActual
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
/-- Transfer the native N5 condition to any qSigned equal to the native signed log-volume. -/
theorem qSideSignedValueCondition_of_native_qSigned_eq
    {qSigned : Real} (h : qSigned = S3013QSigned T) :
    qSideSignedValueCondition (S3013QPilot T) qSigned := by
  rw [h]
  exact native_qSideSignedValueCondition_actual T
/-- Exact floor/native q bridge as a structure. -/
structure FloorNativeQBridge where
  floorQSigned : Real
  floorQSigned_eq : floorQSigned = S3013QSigned T
  condition : qSideSignedValueCondition (S3013QPilot T) floorQSigned :=
    qSideSignedValueCondition_of_native_qSigned_eq T floorQSigned_eq
/-- The floor/native q bridge gives the floor N5 condition. -/
theorem floor_qSideSignedValueCondition (B : FloorNativeQBridge T) :
    qSideSignedValueCondition (S3013QPilot T) B.floorQSigned :=
  B.condition
/-- Exact remaining shared source object (N5 + R1). -/
def remainingSharedQObjects : List String :=
  [ "floor certificate qSigned = min(arithmeticTupleCanonicalHullHaarLog places tuple μ,-1) equals S3013QSigned T = -M",
    "S3013QPilot T = C3 q witness P.line.C3.q.q = qVFamNormalizedGenerator T b",
    "Bad place/index/weight match from T to the C3/floor q object",
    "htheta: floor certificate thetaSigned = source thetaLogVolume",
    "hCTheta: CThetaPaper normalization = thetaLogVolume / |log qPilot|" ]
theorem remainingSharedQObjects_length : remainingSharedQObjects.length = 5 := rfl
#check qSideSignedValueCondition_of_native_qSigned_eq
#check floor_qSideSignedValueCondition
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110N5FloorBridgeActual
end
