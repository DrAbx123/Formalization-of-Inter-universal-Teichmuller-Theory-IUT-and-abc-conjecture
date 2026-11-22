import tmp.sheaf.xif.paper.Mzk1TreeDetFrozenActual
import tmp.sheaf.xif.paper.Mzk1TreeH5DetTensorBundleActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Mzk1HullDetTensorTreeConsumerActual — tree determinant-tensor consumer

A473: real Lean batch over the green tree frozen det spec files. No
sorry/axioms; no closure claim. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1HullDetTensorTreeConsumerActual

open LeanFormal.IUT

theorem detTensorTree_frozenFromBundle : HullDeterminantLogVolumeFrozenSpec :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeH5DetTensorBundleActual.h5_frozenSpec

theorem detTensorTree_frozenFromSingle : HullDeterminantLogVolumeFrozenSpec :=
  LeanFormal.IUT.XiFPaper.Mzk1TreeDetFrozenActual.tree_detFrozenSpec_holds

def detTensorTreeRows : List (String × String × String) :=
  [ ("frozen spec (bundle)", "PROVED", "detTensorTree_frozenFromBundle"),
    ("frozen spec (single)", "PROVED", "detTensorTree_frozenFromSingle") ]

theorem detTensorTreeRows_length : detTensorTreeRows.length = 2 := rfl

#check detTensorTree_frozenFromBundle
#check detTensorTreeRows_length

end LeanFormal.IUT.XiFPaper.Mzk1HullDetTensorTreeConsumerActual
end