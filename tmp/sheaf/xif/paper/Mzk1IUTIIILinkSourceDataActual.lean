import tmp.sheaf.xif.paper.Mzk1IUTIIILinkActual
import tmp.sheaf.xif.paper.Mzk1StepXIContractConstructionActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# STEP 0 prior-art: typed link x typed contract construction -> Mzk1IUTIIILinkActual.IUTIIToStepXILink + Mzk1StepXIContractConstructionActual.StepXIContractSourceData -> PROVED conversion: an IUTII link yields StepXI source data, hence a contract and Cor312/q-positive; no new math beyond repackaging the same fields. No closure.

# Mzk1IUTIIILinkSourceDataActual — link => typed contract source data

PROVED:
* `linkSourceData`: the typed link repackaged as StepXI source data;
* `link_sourceData_cor312`: Cor 3.12 conclusion of the resulting contract;
* `link_sourceData_q_positive`: q-pilot positivity.
NAMED: ipl/she/apt statements and the source-data construction from IUT input.
Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkSourceDataActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual

/-- **PROVED:** the typed IUTII link repackaged as StepXI source data. -/
def linkSourceData (L : IUTIIToStepXILink) : StepXIContractSourceData :=
  { qSigned := L.qSigned
    thetaSigned := L.thetaSigned
    targetSigned := L.targetSigned
    q_negative := L.q_negative
    q_le_target := L.q_le_target
    target_le_theta := L.target_le_theta
    iplProp := L.iplProp
    sheProp := L.sheProp
    aptProp := L.aptProp
    ipl_evidence := L.ipl_evidence
    she_evidence := L.she_evidence
    apt_evidence := L.apt_evidence }

/-- **PROVED:** Cor 3.12 from the link's source data. -/
theorem link_sourceData_cor312 (L : IUTIIToStepXILink) :
    Cor312Conclusion linkSourceData L.toContract :=
  sourceData_cor312 linkSourceData L

/-- **PROVED:** q-pilot positivity from the link's source data. -/
theorem link_sourceData_q_positive (L : IUTIIToStepXILink) :
    0 < -linkSourceData L.toContract.qSigned :=
  sourceData_q_positive linkSourceData L

/-- Rows. -/
def linkSourceDataRows : List (String × String × String) :=
  [ ("typed link => contract source data", "PROVED", "linkSourceData")
  , ("link source data => Cor 3.12", "PROVED", "link_sourceData_cor312")
  , ("link source data => q-pilot positivity", "PROVED", "link_sourceData_q_positive")
  , ("ipl/she/apt statements", "NAMED (explicit fields)", "carried with evidence; not derived from IUTII")
  , ("source-data construction from IUT input", "NAMED (tree Obligation)", "Contract.lean:61") ]

theorem linkSourceDataRows_length : linkSourceDataRows.length = 5 := rfl

#check linkSourceData
#check link_sourceData_cor312
#check linkSourceDataRows_length

end LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkSourceDataActual
end