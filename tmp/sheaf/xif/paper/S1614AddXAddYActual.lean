import tmp.sheaf.xif.paper.S1613C_Psi3Actual
import tmp.sheaf.xif.paper.S1612ZSMulPointFinalActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
namespace LeanFormal.IUT.XiFPaper.S1614AddXAddYActual
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
open WeierstrassCurve.Universal
open LeanFormal.IUT.XiFPaper.S1593ZSMulFieldActual
open LeanFormal.IUT.XiFPaper.S1603AffineGroupLawActual
open LeanFormal.IUT.XiFPaper.S1611PolynomialXRearrangeActual
open LeanFormal.IUT.XiFPaper.S1612ZSMulPointFinalActual
open LeanFormal.IUT.XiFPaper.S1613C_Psi3Actual

#check s1613_C_Ψ₃
#check s1613_polyToField_Ψ₂Sq
#check s1611_slopeOne_eq
#check S1612AddXSmulOne
#check S1612AddYSmulOne
#check S1612SmulXAdd
#check S1612SmulYAddSubNegY

/-- Exact addX target, unchanged. -/
def S1614AddX : Prop := S1612AddXSmulOne

/-- Exact addY target, unchanged. -/
def S1614AddY : Prop := S1612AddYSmulOne

end LeanFormal.IUT.XiFPaper.S1614AddXAddYActual
end