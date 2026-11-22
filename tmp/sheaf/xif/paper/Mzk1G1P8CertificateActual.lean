/- G1/P8 certificate source supply: actual N5 qSideSignedValueCondition and
CThetaPaper source normalization data.  The remaining floor-qSigned bridge /
CTheta upper producer is recorded explicitly. -/
import tmp.sheaf.xif.paper.Mzk1G1P8DisplaySupplyActual
import tmp.sheaf.xif.paper.Mzk1IVThm110N5Actual
import tmp.sheaf.xif.paper.Mzk1IVThm110N5FloorBridgeActual
import tmp.sheaf.xif.paper.Mzk1IVThm110HCor312Actual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1P8CertificateActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S3013QSideSignedValueCondition
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110N5Actual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110N5FloorBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1G1P8DisplaySupplyActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110HCor312Actual
open LeanFormal.IUT.XiFPaper.S2953CThetaFromCertificateActual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Actual N5 q-side signed condition from the actual global q-pilot donor. -/
theorem actual_n5_qSideSignedValueCondition :
    qSideSignedValueCondition (S3013QPilot T) (S3013QSigned T) :=
  native_qSideSignedValueCondition_actual T

/-- Actual CThetaPaper source normalization data: thetaLogVolume is defined as
CThetaPaper times |log qPilot|, so the normalization holds definitionally. -/
structure CThetaSourceNormalization (l : PrimeGeFive)
    (qPilot logQ dmod dFpd fFpd eStar etaPrm : Real) where
  thetaLogVolume : Real
  hCTheta : CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm =
    thetaLogVolume / |Real.log qPilot|

/-- Construct the actual CThetaPaper source normalization from chosen actual
thetaLogVolume data. -/
noncomputable def cThetaSourceNormalizationOfTheta
    (l : PrimeGeFive) (qPilot logQ dmod dFpd fFpd eStar etaPrm : Real)
    (hq : Real.log qPilot ≠ 0) :
    CThetaSourceNormalization l qPilot logQ dmod dFpd fFpd eStar etaPrm where
  thetaLogVolume := CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm * |Real.log qPilot|
  hCTheta := by
    field_simp [abs_ne_zero.mpr hq]

#check actual_n5_qSideSignedValueCondition
#check cThetaSourceNormalizationOfTheta

end LeanFormal.IUT.XiFPaper.Mzk1G1P8CertificateActual
end
