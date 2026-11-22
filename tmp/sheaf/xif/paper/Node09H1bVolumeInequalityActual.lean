/- H1a/H1b volume support: signed tensor volume equality -> <= form,
plus the accepted qReading <= thetaReading inequality (paper signed form).
Fresh alias file for the H1b inequality node; no new hypotheses. -/
import tmp.sheaf.xif.paper.Node09H1aGenericCoordinateActual
import tmp.sheaf.xif.paper.Node09H1aProductFormulaActual
import tmp.sheaf.xif.paper.Node09H1bVolumeActual
import tmp.sheaf.xif.paper.Node09H1bTensorVolumeActual
import tmp.sheaf.xif.paper.Mzk1Cor312AcceptedFinalActual
import tmp.sheaf.xif.paper.Mzk1KummerRealizationActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Node09H1bVolumeInequalityActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
open LeanFormal.IUT.XiFPaper.Node09H1bTensorVolumeActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptedFinalActual

universe u_1 u_2
variable {K : Type*} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type*} [Fintype ι] {V : ι → Type*}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)

/-- The accepted signed paper inequality qReading <= thetaReading. -/
theorem h1b_qReading_le_thetaReading
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] (R : LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual.PaperKummerReading T) :
    R.qReading ≤ R.thetaReading :=
  LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptedFinalActual.accepted_signed_inequality T R

/-- Strict form of the accepted signed inequality. -/
theorem h1b_qReading_lt_thetaReading
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] (R : LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual.PaperKummerReading T) :
    R.qReading < R.thetaReading :=
  LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptedFinalActual.accepted_strict T R

#check h1b_qReading_le_thetaReading
#check h1b_qReading_lt_thetaReading

end LeanFormal.IUT.XiFPaper.Node09H1bVolumeInequalityActual
end
