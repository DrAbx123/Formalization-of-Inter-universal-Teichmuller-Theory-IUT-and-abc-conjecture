import tmp.sheaf.xif.paper.ExpEst00NamingActual

noncomputable section
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.ExpEst01StatementLedgerActual

/-- Statement ledger for [ExpEst]: classification of the paper's explicit-estimate
statements into class A (reusable/proved now) and class B (paper-proved, registered as
paper inputs). -/
def s3135ExpEstStatementLedger : Audit.Obligation :=
  { id := "EXPEST.01.statement-ledger"
    source :=
      "IUT IV section 1 explicit estimates; IUTIV/Estimates/Section1.lean:23-26; " ++
        "Section2.lean:16-19; ElementaryEstimates.lean:76-146"
    status := Audit.VerificationStatus.interface
    note :=
      "CLASS A (proved in tree, re-exported in ExpEst02): e1 arithmeticMean " ++
        "(ElementaryEstimates:76), e2 arithmeticMeanSquares (:88), e3 card GL2 mod " ++
        "prime (:101), e4 card GL2 small primes (:121), e5 adjoin sqrt(-1) finrank " ++
        "<= 2 (:128), e6 logBounds (:146); plus sum_Icc_one_cast (:51) and " ++
        "sum_Icc_one_sq_cast (:63).  CLASS B (paper-proved explicit PNT/Chebyshev " ++
        "forms, registered as paper inputs, NOT proved here): B1 explicit PNT upper " ++
        "form exists n0, forall n >= n0, n <= 4*p_n/(3*log p_n) (Section1.lean:23; " ++
        "paper L913-926 via PNT); B2 sum over primes <= eta bounded by " ++
        "4*eta/(3*log eta) for eta >= eta_prm (Section1.lean:24); B3 Chebyshev " ++
        "theta-function explicit bounds needed by IUT IV section 2 " ++
        "(Section2.lean:16-19).  Mathlib status: PNT asymptotics exist, " ++
        "explicit-constant forms do not; hence class B.  No overclaim; registry " ++
        "frozen 14041."
    dependsOn := [ "EXPEST.00.naming" ]
    sorryItems :=
      [ "B1 explicit PNT upper form",
        "B2 prime reciprocal-sum explicit bound",
        "B3 Chebyshev theta explicit bounds" ] }

#check s3135ExpEstStatementLedger
end LeanFormal.IUT.XiFPaper.ExpEst01StatementLedgerActual
end
