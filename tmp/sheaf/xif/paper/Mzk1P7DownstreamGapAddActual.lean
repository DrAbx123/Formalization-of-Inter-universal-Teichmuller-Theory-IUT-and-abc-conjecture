import tmp.sheaf.xif.paper.Node09H1bVolumeInequalityActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P7DownstreamGapAddActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem p7_downstream_gap_add
    (R : LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual.PaperKummerReading T) :
    R.qReading + (R.thetaReading - R.qReading) = R.thetaReading :=
  add_sub_cancel _ _

#print axioms p7_downstream_gap_add
end LeanFormal.IUT.XiFPaper.Mzk1P7DownstreamGapAddActual