import tmp.sheaf.n8.closure.PaperP6FullTarget

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource

namespace LeanFormal.IUT.N8Closure.TargetsFull

variable {l : PrimeGeFive}

/-- Frozen combined paper target: P6 Q<=Theta finite plus ValuesBounded on the Theta hull. -/
def ChallengeFull : Prop :=
  ∀ S : SourceInitialThetaData l,
    LeanFormal.IUT.N8Closure.PaperP6FullTarget.PaperP6FullTarget S

end LeanFormal.IUT.N8Closure.TargetsFull
