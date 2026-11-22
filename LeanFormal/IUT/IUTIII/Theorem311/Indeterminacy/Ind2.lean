import LeanFormal.IUT.Audit.Status

namespace LeanFormal.IUT.Audit

def ind2 : Obligation :=
  { id := "IUT-III.Ind2"
    source := "IUT III, Theorem 3.11 (Ind2)"
    status := VerificationStatus.pending
    note := "Prove the second link compatibility without identifying alien copies. Ind2Reduction.lean supplies the generic second-link descent; Ind2AlienCopySeparation.lean (Audit.ind2AlienCopySeparation, provedKernel) proves the Q(i)-at-5 instance: the shifted alien copy gives a second link that is nontrivial for the generator shift, whose descent is bijective, preserves normalizedLogVolume, and equals the diagonal exactly at zero shift; source-level alien-copy carriers remain pending."
    dependsOn := ["IUT-I-II.prime-strip-core", "IUT-III.generic-quotient-transport", "IUT-III.orbit-quotient-transport"] }

end LeanFormal.IUT.Audit
