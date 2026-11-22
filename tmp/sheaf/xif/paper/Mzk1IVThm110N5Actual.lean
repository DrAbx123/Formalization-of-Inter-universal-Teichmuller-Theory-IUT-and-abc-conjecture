import tmp.sheaf.xif.paper.S3013QSideSignedValueCondition
import tmp.sheaf.xif.paper.PaperXiFGlobalDirectActual
/-! N5 magnitude nonnegativity from the actual global q-pilot donor.

The actual donor `nativeGlobalQPilotNormalizedLogMagnitude_nonneg` discharges
`S3013MagnitudeNonnegTarget`, hence the native q-pilot signed condition
`qSigned = -|log q|`.  The remaining N5 step is the identification of this native
q-pilot pair with the StepV certificate's qSigned/qPilot; the floor certificate's
qSigned is the engineered `min(hullLog,-1)`, so it is not definitionally equal to
the native qSigned. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110N5Actual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S3013QSideSignedValueCondition
open LeanFormal.IUT.XiFPaper.PaperXiFGlobalDirectActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
/-- Actual N5 magnitude nonnegativity, discharged by the global q-pilot donor. -/
theorem S3013MagnitudeNonnegTarget_actual : S3013MagnitudeNonnegTarget T :=
  nativeGlobalQPilotNormalizedLogMagnitude_nonneg (T := T)
/-- Native q-pilot signed condition `qSigned = -|log q|`. -/
theorem native_qSideSignedValueCondition_actual :
    qSideSignedValueCondition (S3013QPilot T) (S3013QSigned T) :=
  S3013_qSideSignedValueCondition_of_nonneg T (S3013MagnitudeNonnegTarget_actual T)
/-- Actual native q source. -/
noncomputable def actualS3013QSource : S3013QSource T :=
  S3013QSourceOfNonneg T (S3013MagnitudeNonnegTarget_actual T)
/-- Exact remaining N5 bridge: identify the native q-pilot pair with the qSigned/qPilot
consumed by the StepV/floor certificate. -/
def stepVQIdentificationGap : List String :=
  [ "identify native S3013QSigned with StepV/floor certificate qSigned (engineered min(hullLog,-1))",
    "identify S3013QPilot with the StepV q-parameter",
    "transport qSideSignedValueCondition across this identification" ]
theorem stepVQIdentificationGap_length : stepVQIdentificationGap.length = 3 := rfl
#check S3013MagnitudeNonnegTarget_actual
#check native_qSideSignedValueCondition_actual
#check actualS3013QSource
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110N5Actual
end
