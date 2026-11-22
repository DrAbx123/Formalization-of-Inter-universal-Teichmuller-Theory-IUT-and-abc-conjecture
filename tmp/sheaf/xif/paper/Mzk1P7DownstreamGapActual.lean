import tmp.sheaf.xif.paper.Node09H1bVolumeInequalityActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P7DownstreamGapActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- P7 downstream gap consumer: accepted qReading <= thetaReading, in gap form. -/
theorem p7_downstream_gap
    (R : LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual.PaperKummerReading T) :
    0 ≤ R.thetaReading - R.qReading :=
  sub_nonneg.mpr
    (LeanFormal.IUT.XiFPaper.Node09H1bVolumeInequalityActual.h1b_qReading_le_thetaReading T R)

#print axioms p7_downstream_gap
end LeanFormal.IUT.XiFPaper.Mzk1P7DownstreamGapActual