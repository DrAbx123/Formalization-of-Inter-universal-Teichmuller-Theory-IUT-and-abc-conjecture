import tmp.sheaf.n8.closure.PaperP6FamilyTarget

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource

namespace LeanFormal.IUT.N8Closure.TargetsFamily

variable {l : PrimeGeFive}

/-- Frozen family target: P6 Q<=Theta finite plus actual q-pilot family bound. -/
def ChallengeFamily : Prop :=
  ∀ S : SourceInitialThetaData l,
    LeanFormal.IUT.N8Closure.PaperP6FamilyTarget.PaperP6FamilyTarget S

end LeanFormal.IUT.N8Closure.TargetsFamily
