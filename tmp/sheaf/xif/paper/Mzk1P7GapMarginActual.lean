import tmp.sheaf.xif.paper.Node09H1bVolumeInequalityActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P7GapMarginActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Node09H1bVolumeInequalityActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The accepted signed reading gap: `thetaReading - qReading` is nonnegative. -/
theorem p7_gap_nonneg
    (R : LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual.PaperKummerReading T) :
    0 ≤ R.thetaReading - R.qReading :=
  sub_nonneg.mpr (h1b_qReading_le_thetaReading T R)

/-- The accepted signed reading gap is strictly positive (the strict paper inequality). -/
theorem p7_gap_pos
    (R : LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual.PaperKummerReading T) :
    0 < R.thetaReading - R.qReading :=
  sub_pos.mpr (h1b_qReading_lt_thetaReading T R)

/-- Exact gap decomposition: `qReading + (thetaReading - qReading) = thetaReading`. -/
theorem p7_gap_add
    (R : LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual.PaperKummerReading T) :
    R.qReading + (R.thetaReading - R.qReading) = R.thetaReading :=
  add_sub_cancel _ _

#print axioms p7_gap_pos
#print axioms p7_gap_add
end LeanFormal.IUT.XiFPaper.Mzk1P7GapMarginActual