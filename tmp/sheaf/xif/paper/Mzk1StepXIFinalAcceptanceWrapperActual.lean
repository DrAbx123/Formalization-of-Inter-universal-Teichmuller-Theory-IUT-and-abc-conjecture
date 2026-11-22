import tmp.sheaf.xif.paper.Mzk1Cor312AcceptanceFinalActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi final acceptance wrapper

Read-only wrapper over the lattice-owned green `Mzk1Cor312AcceptanceFinalActual`.
It re-exposes the paper/resolved acceptance conclusions under stepxi-owned names. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIFinalAcceptanceWrapperActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceFinalActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem stepxi_final_acceptance_paper (R : PaperKummerReading T)
    (hqneg : requirementSignedQ (requirementOfReading T R) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion (cor312Contract_final T R hqneg ipl hipl she hshe apt hapt) :=
  acceptanceFinal_paper T R hqneg ipl hipl she hshe apt hapt

theorem stepxi_final_acceptance_resolved (D : PositiveQRegionHaarStrict T)
    (hqneg : requirementSignedQ (resolvedRequirement T D) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract (resolvedRequirement T D) hqneg ipl hipl she hshe apt hapt) :=
  acceptanceFinal_resolved T D hqneg ipl hipl she hshe apt hapt

end LeanFormal.IUT.XiFPaper.Mzk1StepXIFinalAcceptanceWrapperActual

end
