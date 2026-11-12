import tmp.sheaf.n8.closure.PaperP6NormalizedValuesActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource

namespace LeanFormal.IUT.N8Closure.TargetsCheckNormalized

variable {l : PrimeGeFive}

def ChallengeNormalized : Prop :=
  ∀ S : SourceInitialThetaData l,
    LeanFormal.IUT.N8Closure.PaperP6NormalizedValuesActual.PaperP6NormalizedTarget S

theorem challengeNormalized_proved : ChallengeNormalized (l := l) :=
  fun S => LeanFormal.IUT.N8Closure.PaperP6NormalizedValuesActual.paperP6NormalizedTarget_actual S

#print axioms challengeNormalized_proved

end LeanFormal.IUT.N8Closure.TargetsCheckNormalized
