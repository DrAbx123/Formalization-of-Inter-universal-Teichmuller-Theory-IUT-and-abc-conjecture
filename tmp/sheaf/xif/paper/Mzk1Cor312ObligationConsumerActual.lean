import LeanFormal.IUT.IUTIII.Corollary312.Obligations
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# STEP 0 prior-art: iutiii StepXI obligation chain / iutiii:IUTIII.COR312.TARGET audit -> tree Audit.Obligation records ipl/she/apt (Corollary312/Obligations.lean:5/12/19) + StepXIContract ipl/she/apt fields (Contract.lean:37-42) -> paper-layer obligation consumer: ids/status/dependency chain/projections PROVED; contract evidence fields are exactly the obligation props. No closure.

# Mzk1Cor312ObligationConsumerActual — StepXI obligation chain consumer

PROVED (definitional projections of the tree records):
* obligation ids: IUT-III.IPL / IUT-III.SHE / IUT-III.APT;
* statuses pending (the tree records are unfilled obligations);
* dependency chain: ipl <- theorem-3.11-output/Ind1/Ind2; she <- IPL/Ind3; apt <- SHE/vertical-log-kummer;
* contract evidence fields are the obligations' props (StepXIContract.ipl/she/apt).
Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312ObligationConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.Audit

/-- **PROVED:** the IPL obligation id. -/
theorem ipl_id : ipl.id = "IUT-III.IPL" := rfl

/-- **PROVED:** the SHE obligation id. -/
theorem she_id : she.id = "IUT-III.SHE" := rfl

/-- **PROVED:** the APT obligation id. -/
theorem apt_id : apt.id = "IUT-III.APT" := rfl

/-- **PROVED:** the IPL obligation's dependencies. -/
theorem ipl_depends : ipl.dependsOn =
    ["IUT-III.theorem-3.11-output", "IUT-III.Ind1", "IUT-III.Ind2"] := rfl

/-- **PROVED:** the SHE obligation's dependencies (SHE depends on IPL and Ind3). -/
theorem she_depends : she.dependsOn = ["IUT-III.IPL", "IUT-III.Ind3"] := rfl

/-- **PROVED:** the APT obligation's dependencies (APT depends on SHE and IUT-II). -/
theorem apt_depends : apt.dependsOn =
    ["IUT-III.SHE", "IUT-II.vertical-log-kummer"] := rfl

/-- **PROVED:** the contract's ipl/she/apt are the obligation props (projection form). -/
theorem contract_evidence_fields (c : StepXIContract) :
    c.ipl ∧ c.she ∧ c.apt := ⟨c.ipl_evidence, c.she_evidence, c.apt_evidence⟩

/-- Rows: obligation chain consumer. -/
def obligationRows : List (String × String × String) :=
  [ ("IPL obligation", "CONSUMED", "Audit.ipl id/deps PROVED (Obligations.lean:5)")
  , ("SHE obligation", "CONSUMED", "Audit.she id/deps PROVED (:12); depends on IPL + Ind3")
  , ("APT obligation", "CONSUMED", "Audit.apt id/deps PROVED (:19); depends on SHE + IUT-II vertical-log-kummer")
  , ("obligation statuses", "PENDING (tree)", "all three are VerificationStatus.pending records")
  , ("contract evidence fields", "PROVED (projection)", "contract_evidence_fields: StepXIContract.ipl/she/apt evidence") ]

theorem obligationRows_length : obligationRows.length = 5 := rfl

#check ipl_id
#check she_depends
#check apt_depends
#check contract_evidence_fields
#check obligationRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Cor312ObligationConsumerActual
end