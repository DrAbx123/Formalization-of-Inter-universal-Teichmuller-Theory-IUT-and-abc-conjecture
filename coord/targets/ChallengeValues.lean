import tmp.sheaf.n8.closure.PaperP6ValuesTarget

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource

namespace LeanFormal.IUT.N8Closure.TargetsValues

variable {l : PrimeGeFive}

/-- Frozen values target: P6 Q<=Theta finite plus actual q-pilot values bounded. -/
def ChallengeValues : Prop :=
  ∀ S : SourceInitialThetaData l,
    LeanFormal.IUT.N8Closure.PaperP6ValuesTarget.PaperP6ValuesTarget S

end LeanFormal.IUT.N8Closure.TargetsValues
