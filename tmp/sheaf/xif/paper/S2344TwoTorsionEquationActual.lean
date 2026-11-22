import tmp.sheaf.xif.paper.S2337TwoTorsionCorrectActual
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

/-! # S2344: Equation for the corrected 2-torsion point -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2344TwoTorsionEquationActual

open WeierstrassCurve
open LeanFormal.IUT.XiFPaper.S2335TwoTorsionRootActual
open LeanFormal.IUT.XiFPaper.S2337TwoTorsionCorrectActual

universe u

variable {R : Type u} [Field R] (W : WeierstrassCurve R)

#check S2337Y

