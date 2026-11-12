import tmp.sheaf.n8.closure.PaperP6C6AlignedTarget

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource

namespace LeanFormal.IUT.N8Closure.TargetsCheckC6Aligned

variable {l : PrimeGeFive}

def ChallengeC6Aligned : Prop :=
  ∀ S : SourceInitialThetaData l,
    LeanFormal.IUT.N8Closure.PaperP6C6AlignedTarget.PaperP6C6AlignedTarget S

theorem challengeC6Aligned_proved : ChallengeC6Aligned (l := l) :=
  fun S => LeanFormal.IUT.N8Closure.PaperP6C6AlignedTarget.paperP6C6AlignedTarget_actual S

#print axioms challengeC6Aligned_proved

end LeanFormal.IUT.N8Closure.TargetsCheckC6Aligned
