import tmp.sheaf.n8.closure.PaperP6FullTarget

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource

namespace LeanFormal.IUT.N8Closure.TargetsCheckFull

variable {l : PrimeGeFive}

def ChallengeFull : Prop :=
  ∀ S : SourceInitialThetaData l,
    LeanFormal.IUT.N8Closure.PaperP6FullTarget.PaperP6FullTarget S

theorem challengeFull_proved : ChallengeFull (l := l) :=
  fun S => LeanFormal.IUT.N8Closure.PaperP6FullTarget.paperP6FullTarget_actual S

#print axioms challengeFull_proved

end LeanFormal.IUT.N8Closure.TargetsCheckFull
