import tmp.sheaf.xif.paper.Mzk1StepXIGreenConsumer11Actual
import tmp.sheaf.xif.paper.Mzk1StepXIGreenConsumer12Actual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1StepXIGreenFlagsConsumerActual — StepXI green flags consumer

Reuses the EXIT0 StepXI green consumers: APT-id and link-contract conclusions from
StepXIContractSourceData and an IUTII-to-StepXI link.  No new math; no closure;
gate NOT PASSED; registry 14041; no registry edits. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenFlagsConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumer11Actual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenConsumer12Actual

theorem stepXIGreen_flags
    (S : LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual.StepXIContractSourceData)
    (L : LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkActual.IUTIIToStepXILink) :
    LeanFormal.IUT.Audit.apt.id = "IUT-III.APT" ∧ Cor312Conclusion L.toContract :=
  ⟨stepXIGreenConsumer11_last S L, stepXIGreenConsumer12_second S L⟩

def stepXIGreenFlagsRows : List (String × String × String) :=
  [ ("APT id + link contract", "stepXIGreen_flags", "PROVED (reuse)"),
    ("scope", "source data/link explicit; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem stepXIGreenFlagsRows_length : stepXIGreenFlagsRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGreenFlagsConsumerActual

end
