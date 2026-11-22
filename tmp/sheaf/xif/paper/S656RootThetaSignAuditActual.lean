import tmp.sheaf.xif.paper.S642PaperRootThetaProcessionActual
import tmp.sheaf.xif.paper.S644PaperRootThetaProcessionActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S656RootThetaSignAuditActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S642PaperRootThetaProcessionActual
open LeanFormal.IUT.XiFPaper.S644PaperRootThetaProcessionActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- S642's "value" is S644's negative signed log, not a positive magnitude. -/
theorem s642_value_eq_s644_signedLog (j : SignedLabel l.value) :
    paperRootThetaValue T b j = paperThetaSignedLogValue T b j := rfl

/-- It is the negative of S644's log magnitude. -/
theorem s642_value_eq_neg_magnitude (j : SignedLabel l.value) :
    paperRootThetaValue T b j = -paperThetaLogMagnitude T b j := rfl

/-- The S644 signed procession uses the same negative values. -/
theorem s644_signed_value_eq_neg_magnitude (j : SignedLabel l.value) :
    (paperThetaSignedProcession T b).value j = -paperThetaLogMagnitude T b j := rfl

/-- The S644 signed average is negative of the log-magnitude average. -/
theorem s644_signed_average_eq_neg_magnitude_average :
    paperThetaSignedAverage T b =
      -((paperThetaSignedProcession T b).average) := rfl

end LeanFormal.IUT.XiFPaper.S656RootThetaSignAuditActual
end
