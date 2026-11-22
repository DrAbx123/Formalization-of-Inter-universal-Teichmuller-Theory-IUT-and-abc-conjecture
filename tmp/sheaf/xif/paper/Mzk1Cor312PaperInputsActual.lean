import tmp.sheaf.xif.paper.Mzk1Cor312PaperConsumerActual
import tmp.sheaf.xif.paper.Mzk1SignedCor312ContractActual

/-! # Paper input table for Cor 3.12 (consumer/ledger layer) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312PaperInputsActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalStatementActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312PaperConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1SignedCor312ContractActual

/-- The paper input table: magnitudes `|log q|, |log Theta|` with positivity and
the paper inequality `|log Theta| ≤ |log q|`. -/
structure Cor312PaperInputs where
  qMag : Real
  thetaMag : Real
  qMag_pos : 0 < qMag
  theta_le_q : thetaMag ≤ qMag

/-- The paper target holds for the input table. -/
theorem paperTarget_of_inputs (I : Cor312PaperInputs) :
    paperTarget I.qMag I.thetaMag :=
  (paperTarget_iff_magnitudes I.qMag I.thetaMag).2 I.theta_le_q

/-- Signed contract built from the paper input table (qSigned=-|log q|,
thetaSigned=-|log Theta|), with explicit IPL/SHE/APT evidence. -/
noncomputable def signedContract_of_inputs (I : Cor312PaperInputs)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) : StepXIContract :=
  signedCor312Contract (paperSignedQ I.qMag) (paperSignedTheta I.thetaMag)
    (by unfold paperSignedQ; linarith [I.qMag_pos])
    ipl hipl she hshe apt hapt
    (by unfold paperSignedQ paperSignedTheta; linarith [I.theta_le_q])

/-- Consumer theorem: the paper input table yields Cor 3.12 directly. -/
theorem cor312Conclusion_of_inputs (I : Cor312PaperInputs)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion (signedContract_of_inputs I ipl hipl she hshe apt hapt) :=
  cor312Conclusion_of_paperTarget (C := signedContract_of_inputs I ipl hipl she hshe apt hapt)
    rfl rfl I.theta_le_q

end LeanFormal.IUT.XiFPaper.Mzk1Cor312PaperInputsActual
