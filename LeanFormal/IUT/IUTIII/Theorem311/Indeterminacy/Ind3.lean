import LeanFormal.IUT.Audit.Status

namespace LeanFormal.IUT.Audit

def ind3 : Obligation :=
  { id := "IUT-III.Ind3"
    source := "IUT III, Theorem 3.11 (Ind3)"
    status := VerificationStatus.pending
    note := "Construct and prove upper-semi compatibility, not just state it. Ind3UpperSemiConstruction.lean (Audit.ind3UpperSemiConstruction, provedKernel) constructs constructedOutputUpperSemi from outputImageFamily (possibleImage indexed by ind3Lift levels) via ofIsUpperSemi, proves the sharp level criterion, strict one-sidedness, and agreement with possibleImageUpperSemi exactly at level zero; the paper log-Kummer analytic carriers remain open."
    dependsOn := ["IUT-II.vertical-log-kummer", "IUT-III.generic-quotient-transport", "IUT-III.Ind3.upper-semi-kernel"] }

end LeanFormal.IUT.Audit
