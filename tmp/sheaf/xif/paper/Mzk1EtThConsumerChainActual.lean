import tmp.sheaf.xif.paper.Mzk1EtThRealizationRowsSummaryActual
import tmp.sheaf.xif.paper.Mzk1EtThDeepInputsAnchorsActual
import tmp.sheaf.xif.paper.EtTh11ThetaRealizationRowsActual

/-!
# Mzk1EtThConsumerChainActual — consumer theorems over EtTh row/deep-input assets
(ETR/EDA + EtTh11, all EXIT0). Composed projections only; no axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1EtThConsumerChainActual

open LeanFormal.IUT.XiFPaper.Mzk1EtThRealizationRowsSummaryActual
open LeanFormal.IUT.XiFPaper.Mzk1EtThDeepInputsAnchorsActual
open LeanFormal.IUT.XiFPaper.EtTh11ThetaRealizationRowsActual

/-- Consumer: seven realization rows. -/
theorem consumer_rows_length : etthRealizationRowStatus.length = 7 :=
  etthRealizationRowStatus_length

/-- Consumer: four A-class rows. -/
theorem consumer_A_rows :
    (etthRealizationRowStatus.filter (fun r => r.klass == "A")).length = 4 :=
  etthRealizationRowStatus_A_rows

/-- Consumer: three class-B rows. -/
theorem consumer_B_rows :
    (etthRealizationRowStatus.filter (fun r => r.klass == "B")).length = 3 :=
  etthRealizationRowStatus_B_rows

/-- Consumer: ten deep-input anchors with the EtTh02 id linkage. -/
theorem consumer_deep_ids :
    etThDeepInputAnchors.map (fun a => a.paperId) = etThDeepInputs.map (fun d => d.id) :=
  etThDeepInputAnchors_ids_eq

/-- Consumer: ten deep-input anchors. -/
theorem consumer_deep_length : etThDeepInputAnchors.length = 10 :=
  etThDeepInputAnchors_length

#check consumer_rows_length
#check consumer_A_rows
#check consumer_B_rows
#check consumer_deep_ids
#check consumer_deep_length

end LeanFormal.IUT.XiFPaper.Mzk1EtThConsumerChainActual
end
