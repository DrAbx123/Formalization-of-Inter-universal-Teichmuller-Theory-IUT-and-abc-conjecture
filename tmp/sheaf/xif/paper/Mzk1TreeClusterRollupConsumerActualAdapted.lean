import tmp.sheaf.xif.paper.Mzk1TreeStepXIBundleActual
import tmp.sheaf.xif.paper.Mzk1TreeCor312ComparisonActual
import LeanFormal.IUT.IUTIII.Corollary312.Obligations

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree cluster rollup consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeClusterRollupConsumerActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Audit

theorem treeClusterRollupConsumer_bundle (contract : StepXIContract) :
    Cor312Conclusion contract ∧ (0 < -contract.qSigned) ∧
      ipl.id = "IUT-III.IPL" :=
  have h := LeanFormal.IUT.XiFPaper.Mzk1TreeStepXIBundleActual.stepXI_contract_bundle contract Cor312Route.mochizuki3115
  ⟨h.1, LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual.tree_q_positive contract, h.2.2.1⟩

def treeClusterRollupConsumerRows : List (String × String × String) :=
  [ ("contract + q + IPL", "PROVED", "treeClusterRollupConsumer_bundle") ]

theorem treeClusterRollupConsumerRows_length : treeClusterRollupConsumerRows.length = 1 := rfl

#check treeClusterRollupConsumer_bundle
#check treeClusterRollupConsumerRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeClusterRollupConsumerActualAdapted
end