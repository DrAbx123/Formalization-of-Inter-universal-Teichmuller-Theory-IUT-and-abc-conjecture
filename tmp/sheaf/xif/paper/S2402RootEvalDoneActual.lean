import tmp.sheaf.xif.paper.S2389RootEvalActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2402RootEvalDoneActual

open WeierstrassCurve
open LeanFormal.IUT.XiFPaper.S2389RootEvalActual
universe u
variable {R : Type u} [Field R] [Nontrivial R]
variable (W : WeierstrassCurve R) [W.IsElliptic]

#check S2389TwoTorsionPolynomial_map



end LeanFormal.IUT.XiFPaper.S2402RootEvalDoneActual
end