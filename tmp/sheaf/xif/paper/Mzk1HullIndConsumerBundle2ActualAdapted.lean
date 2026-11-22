import tmp.sheaf.xif.paper.Mzk1IndeterminacyObligationConsumerActual
import tmp.sheaf.xif.paper.Mzk1TreeIndeterminacyFactsActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Mzk1HullIndConsumerBundle2ActualAdapted — Ind1/2/3 consumer bundle 2

A472/A473: real Lean consumer bundle over the Ind obligation records and tree
facts (green deps). No sorry/axioms; no closure claim. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1HullIndConsumerBundle2ActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Audit
open LeanFormal.IUT.XiFPaper.Mzk1IndeterminacyObligationConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1TreeIndeterminacyFactsActual

theorem indBundle2_ids : ind1.id = "IUT-III.Ind1" ∧ ind2.id = "IUT-III.Ind2" ∧
    ind3.id = "IUT-III.Ind3" := ⟨ind1_id, ind2_id, ind3_id⟩

theorem indBundle2_statuses : ind1.status = VerificationStatus.pending ∧
    ind2.status = VerificationStatus.pending ∧ ind3.status = VerificationStatus.pending :=
  ⟨ind1_status, ind2_status, ind3_status⟩

theorem indBundle2_deps : ind1.dependsOn =
    ["IUT-I-II.prime-strip-core", "IUT-III.generic-quotient-transport",
      "IUT-III.orbit-quotient-transport"] := ind1_depends

def indBundle2Rows : List (String × String × String) :=
  [ ("ids", "PROVED", "indBundle2_ids"),
    ("statuses", "PROVED", "indBundle2_statuses"),
    ("dependencies", "PROVED", "indBundle2_deps") ]

theorem indBundle2Rows_length : indBundle2Rows.length = 3 := rfl

#check indBundle2_ids
#check indBundle2Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1HullIndConsumerBundle2ActualAdapted
end