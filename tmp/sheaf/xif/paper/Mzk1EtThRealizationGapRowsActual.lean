import tmp.sheaf.xif.paper.EtTh02DeepInputsActual
import tmp.sheaf.xif.paper.EtTh11ThetaRealizationRowsActual
import tmp.sheaf.xif.paper.Mzk1EtThDeepInputsAnchorsActual
import tmp.sheaf.xif.paper.Mzk1EtThRealizationRowsSummaryActual
import tmp.sheaf.xif.paper.Mzk1EtThClassBGapAnchorsActual

/-!
# Mzk1EtThRealizationGapRowsActual — one gap table for the EtTh realization side

STEP 0 prior-art: EtTh02DeepInputsActual (10 deep inputs), EtTh11ThetaRealizationRowsActual
(7 realization rows), Mzk1EtThDeepInputsAnchorsActual (anchors), 
Mzk1EtThRealizationRowsSummaryActual (row statuses), Mzk1EtThClassBGapAnchorsActual (row 5-7
named-hypothesis bundle) -> REUSE.
This file combines the three EtTh gap layers into one row table with exact counts/linkage;
all class-B/deep inputs remain NAMED.
No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1EtThRealizationGapRowsActual

open LeanFormal.IUT.XiFPaper.EtTh02DeepInputsActual
open LeanFormal.IUT.XiFPaper.EtTh11ThetaRealizationRowsActual
open LeanFormal.IUT.XiFPaper.Mzk1EtThDeepInputsAnchorsActual
open LeanFormal.IUT.XiFPaper.Mzk1EtThRealizationRowsSummaryActual
open LeanFormal.IUT.XiFPaper.Mzk1EtThClassBGapAnchorsActual

/-- The combined EtTh gap rows: (layer, item, status). -/
def etThRealizationGapRows : List (String × String × String) :=
  [ ("deep-inputs", "ten EtTh deep inputs (EtTh02)", "NAMES + ANCHORS (EDA)"),
    ("deep-inputs", "anchor id linkage", "PROVED (EDA)"),
    ("realization-rows", "rows 1-4 A-class", "PROVED/REUSED (EtTh11)"),
    ("realization-rows", "row 5 geometric realization", "NAMED (E4A explicit hypothesis)"),
    ("realization-rows", "row 6 Frobenioid manifestation", "NAMED (E4A explicit hypothesis)"),
    ("realization-rows", "row 7 theta transformation", "NAMED (E4A explicit hypothesis)"),
    ("summary", "row status record (7 rows)", "PROVED (ETR)"),
    ("summary", "A/B class split (4/3)", "PROVED (ETR)") ]

/-- The combined gap table has eight rows. -/
theorem etThRealizationGapRows_length : etThRealizationGapRows.length = 8 := rfl

/-- The deep-input layer has exactly ten entries (id linkage, re-exported). -/
theorem etThRealizationGapRows_deepInputs_count :
    etThDeepInputAnchors.length = 10 :=
  etThDeepInputAnchors_length

/-- The realization rows summary has exactly seven entries (re-exported). -/
theorem etThRealizationGapRows_rows_count :
    etthRealizationRowStatus.length = 7 :=
  etthRealizationRowStatus_length

/-- The class-B row bundle has its five-row status table (re-exported). -/
theorem etThRealizationGapRows_classB_count :
    etThClassBGapRows.length = 5 :=
  etThClassBGapRows_length

#check etThRealizationGapRows
#check etThRealizationGapRows_length
#check etThRealizationGapRows_deepInputs_count
#check etThRealizationGapRows_rows_count
#check etThRealizationGapRows_classB_count

end LeanFormal.IUT.XiFPaper.Mzk1EtThRealizationGapRowsActual
end
