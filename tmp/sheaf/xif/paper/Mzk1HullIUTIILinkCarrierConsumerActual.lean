import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier
import tmp.sheaf.xif.paper.Mzk1IUTIIILinkActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Mzk1HullIUTIILinkCarrierConsumerActual — IUTII log-shell carrier link consumer

A472/A473: real Lean consumer relating the IUT II SourceLogShellDatum carrier to
the typed IUTII->IUTIII link of the paper layer. No sorry/axioms; conditional;
no closure claim. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1HullIUTIILinkCarrierConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkActual

/-- Consumer data: a real IUT II log-shell datum plus the typed link. -/
structure IUTIILogShellLinkData where
  datum : SourceLogShellDatum
  link : IUTIIToStepXILink

theorem iutiiLogShellLink_cor312 (D : IUTIILogShellLinkData) :
    Cor312Conclusion D.link.toContract :=
  cor312Conclusion_of_IUTIIToStepXILink D.link

theorem iutiiLogShellLink_qpositive (D : IUTIILogShellLinkData) :
    0 < -D.link.toContract.qSigned :=
  q_positive_of_IUTIIToStepXILink D.link

def iutiiLogShellLinkRows : List (String × String × String) :=
  [ ("datum + link data", "DEFINED", "IUTIILogShellLinkData"),
    ("link -> Cor312", "PROVED", "iutiiLogShellLink_cor312"),
    ("link -> q-positive", "PROVED", "iutiiLogShellLink_qpositive") ]

theorem iutiiLogShellLinkRows_length : iutiiLogShellLinkRows.length = 3 := rfl

#check iutiiLogShellLink_cor312
#check iutiiLogShellLinkRows_length

end LeanFormal.IUT.XiFPaper.Mzk1HullIUTIILinkCarrierConsumerActual
end