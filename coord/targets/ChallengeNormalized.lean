import tmp.sheaf.n8.closure.PaperP6NormalizedValuesActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource

namespace LeanFormal.IUT.N8Closure.TargetsNormalized

variable {l : PrimeGeFive}

/-- Frozen normalized target: degree-normalized P6 values fit under normalized Theta. -/
def ChallengeNormalized : Prop :=
  ∀ S : SourceInitialThetaData l,
    LeanFormal.IUT.N8Closure.PaperP6NormalizedValuesActual.PaperP6NormalizedTarget S

end LeanFormal.IUT.N8Closure.TargetsNormalized
