import tmp.sheaf.xif.paper.S2344TwoTorsionEquationActual
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

/-! # S2349: explicit calc proof of the corrected 2-torsion Equation -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2349TwoTorsionEqProofActual

open WeierstrassCurve
open LeanFormal.IUT.XiFPaper.S2335TwoTorsionRootActual
open LeanFormal.IUT.XiFPaper.S2337TwoTorsionCorrectActual
open LeanFormal.IUT.XiFPaper.S2344TwoTorsionEquationActual

universe u

variable {R : Type u} [Field R] (W : WeierstrassCurve R)

#check S2337Y



end LeanFormal.IUT.XiFPaper.S2349TwoTorsionEqProofActual

end
