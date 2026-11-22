import tmp.sheaf.xif.paper.Mzk1StepXIContractConstructionActual
import tmp.sheaf.xif.paper.Mzk1Cor312ObligationConsumerActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# STEP 0 prior-art: iutiv-abc:StepXI / iutiii StepXI bundle -> Mzk1StepXIContractConstructionActual (typed source data -> contract -> Cor312/q-positive) + Mzk1Cor312ObligationConsumerActual (IPL/SHE/APT ids/deps) -> PROVED combined StepXI consumer bundle: contract conclusions + obligation chain facts from one source datum. No new math; no closure.

# Mzk1StepXIConsumerBundleActual — combined StepXI consumer bundle

PROVED:
* `stepXI_bundle`: from one typed source datum: Cor 3.12 conclusion, q-pilot positivity,
  the three obligation ids, and the obligation dependency chain facts.
NAMED: source-data construction from IUT input; tree obligations pending.
Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIConsumerBundleActual

open LeanFormal.IUT
open LeanFormal.IUT.Audit
open LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312ObligationConsumerActual

/-- **PROVED (bundled):** contract conclusions + obligation chain from one source datum. -/
theorem stepXI_bundle (S : StepXIContractSourceData) :
    Cor312Conclusion S.toContract ∧
      (0 < -S.toContract.qSigned) ∧
      ipl.id = "IUT-III.IPL" ∧
      she.id = "IUT-III.SHE" ∧
      apt.id = "IUT-III.APT" ∧
      ipl.dependsOn = ["IUT-III.theorem-3.11-output", "IUT-III.Ind1", "IUT-III.Ind2"] :=
  ⟨sourceData_cor312 S, sourceData_q_positive S, ipl_id, she_id, apt_id, ipl_depends⟩

/-- Rows. -/
def stepXIBundleRows : List (String × String × String) :=
  [ ("Cor 3.12 + q-positive from source data", "PROVED", "stepXI_bundle")
  , ("IPL/SHE/APT obligation ids and dependencies", "PROVED", "ipl_id/she_id/apt_id/ipl_depends (tree records consumed)")
  , ("source-data construction from IUT input", "NAMED (tree Obligation)", "Contract.lean:61")
  , ("IPL/SHE/APT proofs", "PENDING (tree obligations)", "Obligations.lean:5/12/19 records") ]

theorem stepXIBundleRows_length : stepXIBundleRows.length = 4 := rfl

#check stepXI_bundle
#check stepXIBundleRows_length

end LeanFormal.IUT.XiFPaper.Mzk1StepXIConsumerBundleActual
end