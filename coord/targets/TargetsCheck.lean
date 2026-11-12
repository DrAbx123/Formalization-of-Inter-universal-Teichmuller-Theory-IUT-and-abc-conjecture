import tmp.sheaf.n8.closure.PaperP6Target

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource

namespace LeanFormal.IUT.N8Closure.TargetsCheck

variable {l : PrimeGeFive}

/-- The checked target statement. -/
def Challenge : Prop :=
  ∀ S : SourceInitialThetaData l,
    LeanFormal.IUT.N8Closure.PaperP6Target2.PaperP6Target S

/-- Target is inhabited by the actual paper P6 proof. -/
theorem challenge_proved : Challenge (l := l) :=
  fun S => LeanFormal.IUT.N8Closure.PaperP6Target2.paperP6Target_actual S

#print axioms challenge_proved

end LeanFormal.IUT.N8Closure.TargetsCheck
