import tmp.sheaf.n8.closure.PaperP6Target

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource

namespace LeanFormal.IUT.N8Closure.Targets

variable {l : PrimeGeFive}

/-- Frozen candidate target: paper-level P6 for qualified initial Theta-data. -/
def Challenge : Prop :=
  ∀ S : SourceInitialThetaData l,
    LeanFormal.IUT.N8Closure.PaperP6Target2.PaperP6Target S

end LeanFormal.IUT.N8Closure.Targets
