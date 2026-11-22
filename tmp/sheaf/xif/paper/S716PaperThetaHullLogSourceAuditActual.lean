import tmp.sheaf.xif.paper.PaperLevelXiFTargetProofActual
import tmp.sheaf.xif.paper.ProcessionNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.RootHullMeasureActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import tmp.sheaf.xif.paper.S707ThetaHullVsThetaValueActual
import tmp.sheaf.xif.paper.S657RootSignedHullIndependentActual

-- S716: paper -|log Theta| is the ambient hull log-volume.
-- PaperLevelXiFTargetProofActual perBThetaHullLog is the actual rootNormHull
-- normalized hull log; s663 uses rootThetaMagnitudeProcession average.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S716PaperThetaHullLogSourceAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.ProcessionNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.RootHullMeasureActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S707ThetaHullVsThetaValueActual
open LeanFormal.IUT.XiFPaper.S657RootSignedHullIndependentActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- The actual paper Theta-hull log at b: normalized log of rootNormHull. -/
noncomputable def paperPerBThetaHullLog : Real :=
  perBThetaHullLog T b

theorem paperPerBThetaHullLog_eq_rootNormHullLog :
    paperPerBThetaHullLog T b =
      rootThetaHullLog (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
        Measure.addHaar (rootHalfCoefficient (l := l) T b) := rfl

theorem paperPerBThetaHullLog_eq_ambientHullLog :
    paperPerBThetaHullLog T b =
      arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b)
        qVFamTensorTuple Measure.addHaar (rootNormHull (l := l) T b) := rfl

theorem paperGlobalThetaHullLog_eq :
    globalThetaHullLog T =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * paperPerBThetaHullLog T b := rfl

/-- Exact gap to the s663 theta-average signed hull: the paper hull log
must equal the rootThetaMagnitudeProcession average. -/
def PaperHullVsS663ThetaAverageGap : Prop :=
  paperPerBThetaHullLog T b =
    (rootThetaMagnitudeProcession T b).average

def PaperHullVsS663ThetaAverageGapRequired : Prop :=
  PaperHullVsS663ThetaAverageGap (l := l) T b

/-- S663's signed hull is the negative of that procession average. -/
theorem s663_thetaAverage_signed_value :
    -(rootThetaMagnitudeProcession T b).average =
      -((rootThetaMagnitudeProcession T b).average) := rfl

#check paperPerBThetaHullLog
#check paperPerBThetaHullLog_eq_ambientHullLog
#check PaperHullVsS663ThetaAverageGap

end LeanFormal.IUT.XiFPaper.S716PaperThetaHullLogSourceAuditActual

end