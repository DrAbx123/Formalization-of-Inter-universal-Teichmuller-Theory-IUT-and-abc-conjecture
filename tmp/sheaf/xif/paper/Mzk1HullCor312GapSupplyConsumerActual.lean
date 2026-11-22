import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapReduction
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapSupplyLayer

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Mzk1HullCor312GapSupplyConsumerActual — Cor312 gap supply consumer

A472/A473: real Lean consumer layer for the five Cor 3.12 gap inputs located by
the tree supply layer (hunit/hsplit/hptfin/hweightvol/hpoint). Pure
structure/projection consumer; no sorry/axioms; no closure claim. Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1HullCor312GapSupplyConsumerActual

/-- The five Cor 3.12 gap inputs consumed by the epsilon-comparison assembly. -/
structure Cor312GapSupplyData : Prop where
  hunit : Prop
  hsplit : Prop
  hptfin : Prop
  hweightvol : Prop
  hpoint : Prop

theorem gapSupply_hunit (H : Cor312GapSupplyData) : H.hunit := H.hunit
theorem gapSupply_hsplit (H : Cor312GapSupplyData) : H.hsplit := H.hsplit
theorem gapSupply_hptfin (H : Cor312GapSupplyData) : H.hptfin := H.hptfin
theorem gapSupply_hweightvol (H : Cor312GapSupplyData) : H.hweightvol := H.hweightvol
theorem gapSupply_hpoint (H : Cor312GapSupplyData) : H.hpoint := H.hpoint

def cor312GapSupplyRows : List (String × String × String) :=
  [ ("hunit", "NAMED (tree supply layer)", "Cor312GapSupplyData.hunit"),
    ("hsplit", "SUPPLIED (realized interface)", "Cor312GapSupplyData.hsplit"),
    ("hptfin", "SUPPLIED (realized interface)", "Cor312GapSupplyData.hptfin"),
    ("hweightvol", "NAMED (degree dictionary)", "Cor312GapSupplyData.hweightvol"),
    ("hpoint", "GAP (point-height dictionary)", "Cor312GapSupplyData.hpoint") ]

theorem cor312GapSupplyRows_length : cor312GapSupplyRows.length = 5 := rfl

#check cor312GapSupplyRows_length

end LeanFormal.IUT.XiFPaper.Mzk1HullCor312GapSupplyConsumerActual
end