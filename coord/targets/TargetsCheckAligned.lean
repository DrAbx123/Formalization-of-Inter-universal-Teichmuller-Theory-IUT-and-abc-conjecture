import tmp.sheaf.n8.closure.PaperP6AlignedTarget

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource

namespace LeanFormal.IUT.N8Closure.TargetsCheckAligned

variable {l : PrimeGeFive}

def ChallengeAligned : Prop :=
  ∀ S : SourceInitialThetaData l,
    LeanFormal.IUT.N8Closure.PaperP6AlignedTarget.PaperP6AlignedTarget S

theorem challengeAligned_proved : ChallengeAligned (l := l) :=
  fun S => LeanFormal.IUT.N8Closure.PaperP6AlignedTarget.paperP6AlignedTarget_actual S

#print axioms challengeAligned_proved

end LeanFormal.IUT.N8Closure.TargetsCheckAligned
