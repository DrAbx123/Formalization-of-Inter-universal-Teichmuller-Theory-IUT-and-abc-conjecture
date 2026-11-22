import tmp.sheaf.xif.paper.Mzk1KummerTransportActual
import tmp.sheaf.xif.paper.Mzk1KummerRealizationActual
import tmp.sheaf.xif.paper.Mzk1KummerNormBoundBridgeActual

/-! # Kummer realization norm/strict-volume checks -/

namespace LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationChecksActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerNormBoundBridgeActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The realized theta image has norm at most one at every bad place. -/
theorem genuineThetaImage_norm_le_one (b : Bad (nativePlaceSelection T)) :
    ‖(genuineKummerData T).thetaImage b‖ ≤ 1 := by
  simpa [genuineKummerData, thetaOneCarrier] using thetaOne_norm_le_one T b

/-- The genuine Kummer realization equality, as a check theorem. -/
theorem genuineKummerData_sHE_reading :
    (genuineKummerData T).qImageInTheta =
      kummerMap T (genuineKummerData T).thetaImage :=
  genuineKummerData_constructed T

/-- The strict xi-e volume increase is a hypothesis of the paper reading, not a
definitional equality: it is exactly `KummerXiERealization.strict_measure`. -/
theorem strict_volume_of_reading (R : PaperKummerReading T) :
    R.D.vol {qPilotInThetaCarrier T} < R.D.vol (s1902Hull T) :=
  R.D.strict_measure

end LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationChecksActual
