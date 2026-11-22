import tmp.sheaf.xif.paper.Mzk1Cor312PaperConsumerActual
import tmp.sheaf.xif.paper.Mzk1Cor312PaperInputsActual
import tmp.sheaf.xif.paper.Mzk1Cor312FinalSelfChecksActual

/-! # Final consumer: paper target and Cor312Conclusion equivalence -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalStatementActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312PaperConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312PaperInputsActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalSelfChecksActual
open LeanFormal.IUT.XiFPaper.Mzk1SignedCor312ContractActual

/-- Both directions: a contract with paper slots satisfies the paper target iff
its `Cor312Conclusion` holds. -/
theorem paperTarget_iff_cor312Conclusion {C : StepXIContract} {qMag thetaMag : Real}
    (hq : C.qSigned = paperSignedQ qMag)
    (ht : C.thetaSigned = paperSignedTheta thetaMag) :
    paperTarget qMag thetaMag ↔ Cor312Conclusion C :=
  (contract_matches_paperTarget hq ht).symm

/-- The paper input table contract has exactly the signed slots `-qMag`/`-thetaMag`. -/
theorem inputsContract_signed_slots (I : Cor312PaperInputs)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    (signedContract_of_inputs I ipl hipl she hshe apt hapt).qSigned = -I.qMag ∧
    (signedContract_of_inputs I ipl hipl she hshe apt hapt).thetaSigned = -I.thetaMag := by
  constructor <;> rfl

end LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalConsumerActual
