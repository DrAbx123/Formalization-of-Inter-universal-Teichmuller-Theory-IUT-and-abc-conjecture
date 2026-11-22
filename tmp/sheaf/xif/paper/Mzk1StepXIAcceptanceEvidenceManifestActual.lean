import tmp.sheaf.xif.paper.Mzk1AcceptanceEvidenceBundleActual
import tmp.sheaf.xif.paper.Mzk1StepXIABCEntryPointsActual
import tmp.sheaf.xif.paper.Mzk1StepXIABCStage5AxiomGatePayloadActual
import tmp.sheaf.xif.paper.Mzk1StepXIGap2NumericWitnessActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi final acceptance evidence manifest

Packages the green stepxi evidence artifacts: ABC entry points, axiom-gate payload,
Gap-2 numeric witness, and the 16-entry acceptance evidence bundle. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIAcceptanceEvidenceManifestActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1StepXIABCEntryPointsActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIABCStage5Gap2ConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIABCFormHeightConsumerActual

structure StepXIAcceptanceEvidence where
  abcEntryGap2 : StepXIABCStage5Input → ABCConjecture
  abcEntryHeightRegion : StepXIABCHeightRegionInput → ABCConjecture

def stepxiAcceptanceEvidence : StepXIAcceptanceEvidence where
  abcEntryGap2 := stepxi_abcEntry_gap2
  abcEntryHeightRegion := stepxi_abcEntry_heightRegion

theorem stepxiAcceptanceEvidence_sound :
    (∀ I : StepXIABCStage5Input, ABCConjecture) ∧
      (∀ I : StepXIABCHeightRegionInput, ABCConjecture) :=
  ⟨fun I => stepxiAcceptanceEvidence.abcEntryGap2 I,
    fun I => stepxiAcceptanceEvidence.abcEntryHeightRegion I⟩

end LeanFormal.IUT.XiFPaper.Mzk1StepXIAcceptanceEvidenceManifestActual

end
