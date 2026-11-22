import tmp.sheaf.xif.paper.Mzk1DeepStatementLayerV2ActualAdapted

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1Cor312DeepInputsConsumerActualAdapted (adapted copy, A475 reuse) — Cor312 named inputs and gap-supply consumers

Reuses Mzk1DeepStatementLayerV2ActualAdapted (Type-level layer) to assemble the
Cor312 named inputs (hCor312, hSlack, contract) and the five gap-supply data
fields, with projections.  No named paper object is proved; no closure.
Gate NOT PASSED; registry 14041; no registry edits. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312DeepInputsConsumerActualAdapted

open LeanFormal.IUT.XiFPaper.Mzk1DeepStatementLayerV2ActualAdapted

/-- Assemble Cor312NamedInputsBundle from hCor312, hSlack and a contract Prop. -/
def cor312NamedInputs_of (hcor : HCor312Statement) (hslack : HSlackStatement)
    (contract : Prop) : Cor312NamedInputsBundle :=
{ hcor312 := hcor
  hslack := hslack
  contract_statement := contract }

theorem cor312Named_display (hcor : HCor312Statement) (hslack : HSlackStatement)
    (contract : Prop) :
    (cor312NamedInputs_of hcor hslack contract).hcor312.hull_normalizedVolume_display :=
  hCor312_display hcor

theorem cor312Named_finalInequality (hcor : HCor312Statement) (hslack : HSlackStatement)
    (contract : Prop) :
    (cor312NamedInputs_of hcor hslack contract).hslack.final_inequality :=
  hSlack_final hslack

/-- Five-field gap-supply data from explicit Props. -/
def gapSupplyData_of (hunit hsplit hptfin hweightvol hpoint : Prop) :
    Cor312GapSupplyData :=
{ hunit := hunit
  hsplit := hsplit
  hptfin := hptfin
  hweightvol := hweightvol
  hpoint := hpoint }

theorem gapSupply_hunit_of (hunit hsplit hptfin hweightvol hpoint : Prop) :
    (gapSupplyData_of hunit hsplit hptfin hweightvol hpoint).hunit :=
  hunit

theorem gapSupply_hpoint_of (hunit hsplit hptfin hweightvol hpoint : Prop) :
    (gapSupplyData_of hunit hsplit hptfin hweightvol hpoint).hpoint :=
  hpoint

def cor312DeepInputsRows : List (String × String × String) :=
  [ ("named inputs bundle", "cor312NamedInputs_of", "DEF (reuses deep layer)"),
    ("display projection", "cor312Named_display", "PROVED"),
    ("slack projection", "cor312Named_finalInequality", "PROVED"),
    ("gap supply data", "gapSupplyData_of + projections", "DEF/PROVED"),
    ("scope", "named objects only; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem cor312DeepInputsRows_length : cor312DeepInputsRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Cor312DeepInputsConsumerActualAdapted

end
