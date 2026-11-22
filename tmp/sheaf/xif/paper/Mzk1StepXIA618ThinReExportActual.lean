import tmp.sheaf.xif.paper.Mzk1StepXIGateVerificationActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi A618 thin re-export

Thin re-export of the green A618 gate verification. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIA618ThinReExportActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGateVerificationActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIHqnegCoercionActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem stepxi_a618_thin_reexport (R : PaperKummerReading T)
    (h : R.qReading < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (cor312Contract_final T R
        (stepxi_hqneg_of_qReading_neg T R h) ipl hipl she hshe apt hapt) :=
  stepxi_gate_verification T R h ipl hipl she hshe apt hapt

end LeanFormal.IUT.XiFPaper.Mzk1StepXIA618ThinReExportActual

end
