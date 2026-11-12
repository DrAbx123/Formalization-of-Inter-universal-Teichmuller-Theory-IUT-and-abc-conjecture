import tmp.sheaf.n8.closure.PaperP6ValuesTarget

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource

namespace LeanFormal.IUT.N8Closure.TargetsCheckValues

variable {l : PrimeGeFive}

def ChallengeValues : Prop :=
  ∀ S : SourceInitialThetaData l,
    LeanFormal.IUT.N8Closure.PaperP6ValuesTarget.PaperP6ValuesTarget S

theorem challengeValues_proved : ChallengeValues (l := l) :=
  fun S => LeanFormal.IUT.N8Closure.PaperP6ValuesTarget.paperP6ValuesTarget_actual S

#print axioms challengeValues_proved

end LeanFormal.IUT.N8Closure.TargetsCheckValues
