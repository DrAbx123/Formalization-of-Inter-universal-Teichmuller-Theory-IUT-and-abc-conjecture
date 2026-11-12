import tmp.sheaf.n8.closure.PaperP6FamilyTarget

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource

namespace LeanFormal.IUT.N8Closure.TargetsCheckFamily

variable {l : PrimeGeFive}

def ChallengeFamily : Prop :=
  ∀ S : SourceInitialThetaData l,
    LeanFormal.IUT.N8Closure.PaperP6FamilyTarget.PaperP6FamilyTarget S

theorem challengeFamily_proved : ChallengeFamily (l := l) :=
  fun S => LeanFormal.IUT.N8Closure.PaperP6FamilyTarget.paperP6FamilyTarget_actual S

#print axioms challengeFamily_proved

end LeanFormal.IUT.N8Closure.TargetsCheckFamily
