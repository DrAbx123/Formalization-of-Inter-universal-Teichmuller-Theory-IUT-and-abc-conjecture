import tmp.sheaf.xif.paper.S2405RootEvalCorrectActual
import tmp.sheaf.xif.paper.S2376ThreeRootsActual
import tmp.sheaf.xif.paper.S2358TwoTorsionOrderActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2406TwoTorsionPointsTransportActual

open WeierstrassCurve
open WeierstrassCurve.Affine.Point
open LeanFormal.IUT.XiFPaper.S2353TwoTorsionEquationActual
open LeanFormal.IUT.XiFPaper.S2354TwoTorsionPointsActual
open LeanFormal.IUT.XiFPaper.S2358TwoTorsionOrderActual
open LeanFormal.IUT.XiFPaper.S2376ThreeRootsActual
open LeanFormal.IUT.XiFPaper.S2405RootEvalCorrectActual

universe u
variable {R : Type u} [Field R] [Nontrivial R]
variable (W : WeierstrassCurve R) [W.IsElliptic]

#check S2405_eval_zero_of_mem
#check S2358_two_nsmul

