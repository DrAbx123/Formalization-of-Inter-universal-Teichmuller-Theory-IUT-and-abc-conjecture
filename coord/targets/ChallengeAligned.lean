import tmp.sheaf.n8.closure.PaperP6AlignedTarget

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource

namespace LeanFormal.IUT.N8Closure.TargetsAligned

variable {l : PrimeGeFive}

/-- Frozen aligned target: degree-normalized P6 plus C6 normalizedLogVolume bridge. -/
def ChallengeAligned : Prop :=
  ∀ S : SourceInitialThetaData l,
    LeanFormal.IUT.N8Closure.PaperP6AlignedTarget.PaperP6AlignedTarget S

end LeanFormal.IUT.N8Closure.TargetsAligned
