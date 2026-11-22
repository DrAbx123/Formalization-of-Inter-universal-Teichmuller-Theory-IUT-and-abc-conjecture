import tmp.sheaf.xif.paper.S2508UniversalCoverActual
import tmp.sheaf.xif.paper.S2505RhoVActual

/-! # S2509: actual generator rho on the S2508 universal cover

Combines the actual `S2508UniversalCover : S2500UniversalCoverRequired p` with
the actual `S2505GeneratorRho` to obtain concrete realified values on the
base-p pro-generators at every finite Galois level. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2500CategoricalOtriangleActual
open LeanFormal.IUT.XiFPaper.S2501UniversalCoverSystemActual
open LeanFormal.IUT.XiFPaper.S2505RhoVActual
open LeanFormal.IUT.XiFPaper.S2508UniversalCoverActual

namespace LeanFormal.IUT.XiFPaper.S2509C9GeneratorActual

variable (p : Nat) [Fact (Nat.Prime p)]

noncomputable def S2509Cover : S2500UniversalCoverRequired p :=
  S2508UniversalCover p

/-- The actual realified value of the base-p generator at each finite level. -/
noncomputable def S2509GeneratorRho (L : (S2509Cover p).proSystem.Index) : Real :=
  S2505GeneratorRho p (S2509Cover p) L

#check S2509Cover
#check S2509GeneratorRho

end LeanFormal.IUT.XiFPaper.S2509C9GeneratorActual
end
