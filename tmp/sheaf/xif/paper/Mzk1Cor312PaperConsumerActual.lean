import tmp.sheaf.xif.paper.Mzk1Cor312FinalStatementActual

/-! # Consumer: paper target -> Cor 3.12 conclusion -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312PaperConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalStatementActual

/-- A contract with the paper signed slots implies `Cor312Conclusion` from the
paper magnitude inequality `|log Theta| ≤ |log q|`. -/
theorem cor312Conclusion_of_paperTarget {C : StepXIContract} {qMag thetaMag : Real}
    (hq : C.qSigned = paperSignedQ qMag)
    (ht : C.thetaSigned = paperSignedTheta thetaMag)
    (h : thetaMag ≤ qMag) : Cor312Conclusion C :=
  (contract_matches_paperTarget hq ht).2
    ((paperTarget_iff_magnitudes qMag thetaMag).2 h)

/-- Consumer form: a paper target directly yields the contract conclusion. -/
theorem cor312Conclusion_of_paperTarget_shape {C : StepXIContract} {qMag thetaMag : Real}
    (hq : C.qSigned = paperSignedQ qMag)
    (ht : C.thetaSigned = paperSignedTheta thetaMag)
    (h : paperTarget qMag thetaMag) : Cor312Conclusion C :=
  (contract_matches_paperTarget hq ht).2 h

end LeanFormal.IUT.XiFPaper.Mzk1Cor312PaperConsumerActual
