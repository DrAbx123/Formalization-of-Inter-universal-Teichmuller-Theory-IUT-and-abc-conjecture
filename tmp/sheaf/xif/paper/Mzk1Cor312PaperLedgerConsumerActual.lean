import tmp.sheaf.xif.paper.Mzk1Cor312FinalStatementActual
import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual

/-! # Consumer: non-vacuous xi-e requirement -> paper target -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312PaperLedgerConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalStatementActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual

variable {α : Type*} {vol : Set α → Real}

/-- The non-vacuous xi-e requirement gives the paper target at signed magnitudes. -/
theorem requirement_paperTarget (D : XiEContainmentRequirement α vol) :
    paperTarget (-requirementSignedQ D) (-requirementSignedTheta D) := by
  unfold paperTarget paperSignedQ paperSignedTheta
  have h := requirement_signed_inequality D
  linarith

/-- Consumer: the requirement contract yields `Cor312Conclusion`; the paper target
is exactly its signed form. -/
theorem requirement_cor312_consumer (D : XiEContainmentRequirement α vol)
    (hqneg : requirementSignedQ D < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion (requirementContract D hqneg ipl hipl she hshe apt hapt) :=
  requirement_cor312 D hqneg ipl hipl she hshe apt hapt

end LeanFormal.IUT.XiFPaper.Mzk1Cor312PaperLedgerConsumerActual
