import tmp.sheaf.n8.closure.PaperP6C6AlignedTarget

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource

namespace LeanFormal.IUT.N8Closure.TargetsC6Aligned

variable {l : PrimeGeFive}

def ChallengeC6Aligned : Prop :=
  ∀ S : SourceInitialThetaData l,
    LeanFormal.IUT.N8Closure.PaperP6C6AlignedTarget.PaperP6C6AlignedTarget S

end LeanFormal.IUT.N8Closure.TargetsC6Aligned
