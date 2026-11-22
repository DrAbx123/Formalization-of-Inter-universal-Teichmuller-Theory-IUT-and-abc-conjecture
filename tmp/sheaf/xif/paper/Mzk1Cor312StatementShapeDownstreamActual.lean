import tmp.sheaf.xif.paper.Mzk1Cor312PaperInputsActual
import tmp.sheaf.xif.paper.Mzk1Cor312SignedProjectionActual

/-! # Statement-shape downstream consumer -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312StatementShapeDownstreamActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1Cor312PaperInputsActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312SignedProjectionActual
open LeanFormal.IUT.XiFPaper.Mzk1SignedCor312ContractActual

/-- The paper statement shape (inputs table) yields `Cor312Conclusion` for the
contract built from that table. -/
theorem statementShape_conclusion (I : Cor312PaperInputs)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion (signedContract_of_inputs I ipl hipl she hshe apt hapt) :=
  cor312Conclusion_of_inputs I ipl hipl she hshe apt hapt

/-- The statement-shape contract has the literal paper signed slots. -/
theorem statementShape_signed_slots (I : Cor312PaperInputs)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    (signedContract_of_inputs I ipl hipl she hshe apt hapt).qSigned = -I.qMag ∧
    (signedContract_of_inputs I ipl hipl she hshe apt hapt).thetaSigned = -I.thetaMag := by
  constructor <;> rfl

end LeanFormal.IUT.XiFPaper.Mzk1Cor312StatementShapeDownstreamActual
