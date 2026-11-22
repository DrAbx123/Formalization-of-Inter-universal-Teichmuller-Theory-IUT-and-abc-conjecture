import tmp.sheaf.xif.paper.PaperLevelXiFTargetProofActual
import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual
import tmp.sheaf.xif.paper.BadPlacePaperRootComparisonActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S641CorrectedPaperThetaComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootComparisonActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Actual global qPilot <= Theta hull comparison from the existing root hull,
with the normalized c_norm qPilot coefficient. -/
theorem s641GlobalQPilot_le_thetaHull :
    globalQPilotLog (l := l) T ≤ globalThetaHullLog (l := l) T :=
  PaperLevelXiFTargetProofActual.globalQPilotLog_le_globalThetaHullLog T

/-- Exact paper root hull formula gap: the paper-coefficient root hull log
equals the paper root formula log. -/
def S641PaperRootHullFormulaGapRequired : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    Nonempty (PaperRootHullFormulaGap T b)

/-- Exact qPilot coefficient correction: the S13 normalized qPilot scalar is
the paper order scalar plus the correction sum. -/
theorem s641QPilotCorrection_decomposition :
    s13QPilotCoefficientSum T =
      paperQPilotCoefficientSum T + qCorrectionSum T :=
  s13QPilotCoefficientSum_eq_paper_add_correction T

end LeanFormal.IUT.XiFPaper.S641CorrectedPaperThetaComparisonActual

end
