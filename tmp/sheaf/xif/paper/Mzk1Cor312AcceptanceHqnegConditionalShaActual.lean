import tmp.sheaf.xif.paper.Mzk1Cor312FinalAssemblyActual
import tmp.sheaf.xif.paper.Mzk1KummerTransportActual
import tmp.sheaf.xif.paper.Mzk1KummerRealizationActual
import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual
import tmp.sheaf.xif.paper.Mzk1SignedLogVolumeCor312Actual

/-! # hqneg conditional reduction (log-negative volume -> hqneg) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceHqnegConditionalShaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1SignedLogVolumeCor312Actual
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Negative log-volume of the q-pilot singleton gives the hqneg sign hypothesis. -/
theorem hqneg_of_log_neg (R : PaperKummerReading T)
    (h : Real.log (R.D.vol {qPilotInThetaCarrier T}) < 0) :
    requirementSignedQ (requirementOfReading T R) < 0 := by
  simpa only [requirementSignedQ, signedLogVolume, requirementOfReading] using h

/-- Conditional final Cor 3.12: the only sign input is log-negativity of the
q-pilot volume (no named hqneg needed). -/
theorem cor312_from_log_neg (R : PaperKummerReading T)
    (h : Real.log (R.D.vol {qPilotInThetaCarrier T}) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (cor312Contract_final T R (hqneg_of_log_neg T R h)
        ipl hipl she hshe apt hapt) :=
  cor312Conclusion_final T R (hqneg_of_log_neg T R h) ipl hipl she hshe apt hapt

#print axioms hqneg_of_log_neg
#print axioms cor312_from_log_neg

end LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceHqnegConditionalShaActual
